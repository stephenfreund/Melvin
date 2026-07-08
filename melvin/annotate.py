"""Per-statement mover annotations (the margin letters of the paper's figures).

`Lowerer._stmt_static` already classifies every statement, but it joins ALL of
a variable's mover clauses, so a mutex whose write clauses are
`right-mover if \\old(m)==0 && m==tid` and `left-mover if \\old(m)==tid && m==0`
would display N for both `acquire` and `release`.  For the three actions whose
transition is statically known we do better: evaluate each clause condition
under a tiny three-valued abstract interpreter with the transition bound

    acquire(m):        \\old(m) = 0,        m = tid
    release(m):        \\old(m) = tid,      m = 0
    cas(x, e, n) hit:   \\old(x) = e,        x = n     (when e, n are static)

and join only the clauses that are not definitely ruled out — giving the exact
R on acquire and L on release.  This is DISPLAY ONLY: verification always uses
the state-sensitive mover (`Lowerer._mover_expr`) inside Boogie.
"""

from __future__ import annotations

from typing import Dict, List, Optional

from . import ast_nodes as A
from .effects import Effect, join, join_all, seq, star
from .types import TypeInfo
from .vcgen import Lowerer, _Ctx

# Abstract values: Python ints, booleans, the positive symbol TID, or UNKNOWN.
TID = object()
UNKNOWN = object()


def _cmp_eq(a, b):
    """Three-valued equality over abstract values."""
    if a is UNKNOWN or b is UNKNOWN:
        return UNKNOWN
    if a is TID and b is TID:
        return True
    if a is TID or b is TID:
        other = b if a is TID else a
        if isinstance(other, int):
            # tid is positive but otherwise unconstrained
            return False if other <= 0 else UNKNOWN
        return UNKNOWN
    return a == b


def _not(v):
    return UNKNOWN if v is UNKNOWN else (not v)


def _eval(e: A.Expr, cur: Dict[str, object], old: Dict[str, object]):
    """Evaluate `e` to an abstract value (int/bool/TID) or UNKNOWN.

    `cur` and `old` map variable names to abstract values; unmapped variables
    are UNKNOWN.  Only the operators that appear in realistic mover-clause
    guards are interpreted; everything else is UNKNOWN.
    """
    if isinstance(e, A.Num):
        return e.value
    if isinstance(e, A.BoolLit):
        return e.value
    if isinstance(e, A.Tid):
        return TID
    if isinstance(e, A.Var):
        return cur.get(e.name, UNKNOWN)
    if isinstance(e, A.Old):
        return _eval(e.inner, old, old)
    if isinstance(e, A.Unary):
        v = _eval(e.operand, cur, old)
        if e.op == "!":
            return _not(v) if isinstance(v, bool) or v is UNKNOWN else UNKNOWN
        if e.op == "-" and isinstance(v, int):
            return -v
        return UNKNOWN
    if isinstance(e, A.Binary):
        l = _eval(e.left, cur, old)
        r = _eval(e.right, cur, old)
        op = e.op
        if op == "==":
            return _cmp_eq(l, r)
        if op == "!=":
            return _not(_cmp_eq(l, r))
        if op == "&&":
            if l is False or r is False:
                return False
            if l is True and r is True:
                return True
            return UNKNOWN
        if op == "||":
            if l is True or r is True:
                return True
            if l is False and r is False:
                return False
            return UNKNOWN
        if op == "==>":
            if l is False or r is True:
                return True
            if l is True and r is False:
                return False
            return UNKNOWN
        if op in ("+", "-", "*") and isinstance(l, int) and isinstance(r, int):
            return {"+": l + r, "-": l - r, "*": l * r}[op]
        if op in ("<", "<=", ">", ">="):
            # tid > 0 is the only symbolic fact we track
            if l is TID and r == 0:
                return {"<": False, "<=": False, ">": True, ">=": True}[op]
            if r is TID and l == 0:
                return {"<": True, "<=": True, ">": False, ">=": False}[op]
            if isinstance(l, int) and isinstance(r, int):
                return {"<": l < r, "<=": l <= r, ">": l > r, ">=": l >= r}[op]
            return UNKNOWN
        return UNKNOWN
    return UNKNOWN


def _abstract(e: A.Expr):
    """Abstract value of a cas argument: literal, tid, or UNKNOWN."""
    if isinstance(e, A.Num):
        return e.value
    if isinstance(e, A.Tid):
        return TID
    if isinstance(e, A.BoolLit):
        return e.value
    return UNKNOWN


def _transition_mover(low: Lowerer, gname: str, old_val, new_val) -> Effect:
    """Join of the write clauses not definitely ruled out by the transition
    old_val -> new_val.  E if every clause is ruled out (never permitted)."""
    clauses = low._clauses_for(gname, "write")
    cur = {gname: new_val}
    old = {gname: old_val}
    keep = [cl for cl in clauses if _eval(cl.cond, cur, old) is not False]
    if not keep:
        return Effect.E
    return join_all(cl.mover for cl in keep)


class _Annotator:
    """Mirrors Lowerer._stmt_static, refining acquire/release/cas letters."""

    def __init__(self, prog: A.Program, ti: TypeInfo):
        self.prog = prog
        self.ti = ti
        self.low = Lowerer(prog, ti)
        self.ann: Dict[int, Effect] = {}

    # -- refined static effects -------------------------------------------

    def stmt_eff(self, s: A.Stmt, ctx: _Ctx) -> Effect:
        if isinstance(s, A.Acquire):
            return _transition_mover(self.low, s.lock, 0, TID)
        if isinstance(s, A.Release):
            return _transition_mover(self.low, s.lock, TID, 0)
        if isinstance(s, A.Assign):
            kind, _ = self.ti.assign_kind[id(s)]
            if kind == "write":
                # the written value may rule out clauses (e.g. `l = 0` cannot
                # be the acquire transition `l == tid`)
                return _transition_mover(self.low, s.lhs, UNKNOWN, _abstract(s.rhs))
            return self.low._stmt_static(s, ctx)
        if isinstance(s, A.If):
            t = self.cond_eff(s.cond, success=True)
            for st in s.then_body:
                t = seq(t, self.stmt_eff(st, ctx))
            e = self.cond_eff(s.cond, success=False)
            for st in s.else_body:
                e = seq(e, self.stmt_eff(st, ctx))
            return join(t, e)
        if isinstance(s, A.While):
            it = self.cond_eff(s.cond, success=True)
            for st in s.body:
                it = seq(it, self.stmt_eff(st, ctx))
            return seq(star(it), self.cond_eff(s.cond, success=False))
        return self.low._stmt_static(s, ctx)

    def cond_eff(self, c: A.Cond, success: bool) -> Effect:
        if isinstance(c, A.NotCond):
            return self.cond_eff(c.inner, not success)
        if isinstance(c, A.CasCond):
            if success:
                return _transition_mover(
                    self.low, c.target, _abstract(c.expected), _abstract(c.new))
            return Effect.B          # failing cas is a store identity
        return Effect.B

    # -- source walk --------------------------------------------------------

    def put(self, line: int, eff: Effect) -> None:
        if line > 0 and line not in self.ann:
            self.ann[line] = eff

    def walk(self, stmts: List[A.Stmt], ctx: _Ctx) -> None:
        for s in stmts:
            if isinstance(s, A.Call_) and not self._atomic_callee(s):
                continue        # non-atomic calls have no single mover letter
            self.put(s.span.start.line, self.stmt_eff(s, ctx))
            if isinstance(s, A.If):
                self.walk(s.then_body, ctx)
                self.walk(s.else_body, ctx)
            elif isinstance(s, A.While):
                self.walk(s.body, ctx)

    def _atomic_callee(self, s: A.Call_) -> bool:
        callee = self.prog.find_func(s.name)
        return callee is not None and callee.is_atomic

    def run(self) -> Dict[int, Effect]:
        for f in self.prog.funcs:
            ctx = _Ctx(f"fn:{f.name}", f, atomic=f.is_atomic)
            self.walk(f.body, ctx)
        for th in self.prog.threads:
            self.walk(th.body, _Ctx("thread", None, atomic=False))
        return self.ann


def mover_annotations(prog: A.Program, ti: TypeInfo) -> Dict[int, str]:
    """Map 1-based source line -> mover letter (Y/B/R/L/N/E) for every
    statement.  A line holding a compound statement shows the whole
    construct's effect; statements inside multi-line bodies get their own."""
    return {line: eff.value for line, eff in _Annotator(prog, ti).run().items()}


# ===========================================================================
# Per-line explanations and schematic stores (UI hover support)
# ===========================================================================

def _fmt_abs(v) -> str:
    if v is TID:
        return "tid"
    if v is UNKNOWN:
        return "?"
    if isinstance(v, bool):
        return "true" if v else "false"
    return str(v)


def _clause_text(cl: A.MoverClause, source_lines: List[str]) -> str:
    """The clause as written in the source (via its span)."""
    sp = cl.span
    try:
        if sp.start.line == sp.end.line:
            return source_lines[sp.start.line - 1][sp.start.col - 1:sp.end.col - 1].strip()
        parts = [source_lines[sp.start.line - 1][sp.start.col - 1:]]
        parts += source_lines[sp.start.line:sp.end.line - 1]
        parts.append(source_lines[sp.end.line - 1][:sp.end.col - 1])
        return " ".join(p.strip() for p in parts)
    except IndexError:
        return f"{cl.mover.pretty}"


def _clause_rows(clauses, cur, old, source_lines) -> List[Dict]:
    """Each candidate clause with its three-valued status under the
    transition bound in cur/old."""
    rows = []
    for cl in clauses:
        st = _eval(cl.cond, cur, old)
        status = "matches" if st is True else \
                 ("ruled out" if st is False else "possible")
        rows.append({"text": _clause_text(cl, source_lines),
                     "mover": cl.mover.value, "status": status})
    return rows


class _Explainer(_Annotator):
    """Adds, per annotated line, a record of WHY the letter was chosen."""

    def __init__(self, prog: A.Program, ti: TypeInfo, source: str,
                 flow: Optional[Dict[int, Dict]] = None):
        super().__init__(prog, ti)
        self.source_lines = source.splitlines()
        self.expl: Dict[int, Dict] = {}
        self.flow = flow or {}      # line -> abstract store before the line

    def _env(self, s: A.Stmt) -> Dict:
        return dict(self.flow.get(s.span.start.line, {}))

    def put(self, line: int, eff: Effect) -> None:
        if line > 0 and line not in self.ann:
            self.ann[line] = eff
            self.expl[line] = self._pending if self._pending is not None else {}

    def walk(self, stmts: List[A.Stmt], ctx: _Ctx) -> None:
        for s in stmts:
            if isinstance(s, A.Call_) and not self._atomic_callee(s):
                continue
            self._pending = self.explain_stmt(s, ctx)
            self.put(s.span.start.line, self.stmt_eff(s, ctx))
            if isinstance(s, A.If):
                self.walk(s.then_body, ctx)
                self.walk(s.else_body, ctx)
            elif isinstance(s, A.While):
                self.walk(s.body, ctx)

    def explain_stmt(self, s: A.Stmt, ctx: _Ctx) -> Dict:
        src = self.source_lines
        if isinstance(s, A.Yield):
            return {"action": "yield",
                    "note": "ends the current reducible sequence (effect Y)"}
        if isinstance(s, A.Acquire):
            cls = self.low._clauses_for(s.lock, "write")
            env = self._env(s)
            return {"action": f"acquire({s.lock})",
                    "transition": f"{s.lock}: 0 → tid",
                    "clauses": _clause_rows(cls, {**env, s.lock: TID},
                                            {**env, s.lock: 0}, src),
                    "note": "join of the clauses not ruled out by the transition"}
        if isinstance(s, A.Release):
            cls = self.low._clauses_for(s.lock, "write")
            env = self._env(s)
            return {"action": f"release({s.lock})",
                    "transition": f"{s.lock}: tid → 0",
                    "clauses": _clause_rows(cls, {**env, s.lock: 0},
                                            {**env, s.lock: TID}, src),
                    "note": "join of the clauses not ruled out by the transition"}
        if isinstance(s, A.UnstableRead):
            return {"action": f"unstable read of {s.source}",
                    "note": "an unstable read is a right-mover by definition"}
        if isinstance(s, A.Assign):
            kind, gvar = self.ti.assign_kind[id(s)]
            if kind == "write":
                v = _abstract(s.rhs)
                cls = self.low._clauses_for(s.lhs, "write")
                env = self._env(s)
                return {"action": f"write to {s.lhs}",
                        "transition": f"{s.lhs}: ? → {_fmt_abs(v)}",
                        "clauses": _clause_rows(cls, {**env, s.lhs: v}, env, src),
                        "note": "join of the clauses not ruled out by the "
                                "written value"}
            if kind == "read":
                cls = self.low._clauses_for(gvar, "read")
                env = self._env(s)
                return {"action": f"read of {gvar}",
                        "clauses": _clause_rows(cls, env, env, src),
                        "note": "join of the read clauses that may apply"}
            return {"action": "thread-local computation",
                    "note": "touches no shared state: always a both-mover"}
        if isinstance(s, (A.If, A.While)):
            what = "if" if isinstance(s, A.If) else "while loop"
            out = {"action": what,
                   "note": f"combined effect of the {what}'s condition and body"}
            c = s.cond
            while isinstance(c, A.NotCond):
                c = c.inner
            if isinstance(c, A.CasCond):
                cls = self.low._clauses_for(c.target, "write")
                out["transition"] = (f"cas: {c.target} "
                                     f"{_fmt_abs(_abstract(c.expected))} → "
                                     f"{_fmt_abs(_abstract(c.new))} on success")
                out["clauses"] = _clause_rows(
                    cls, {c.target: _abstract(c.new)},
                    {c.target: _abstract(c.expected)}, src)
            return out
        if isinstance(s, A.Call_):
            callee = self.prog.find_func(s.name)
            if callee is not None and callee.is_atomic:
                return {"action": f"call {s.name}()",
                        "note": f"atomic function: its declared mover is "
                                f"'{callee.spec.mover.pretty}'"}
            return {"action": f"call {s.name}()"}
        if isinstance(s, A.Assert):
            return {"action": "assert",
                    "note": "a specification check: no shared access, both-mover"}
        return {"action": type(s).__name__.lower(),
                "note": "no shared access: both-mover"}

    def run(self):
        self._pending = None
        super().run()
        return self.ann, self.expl


class _StoreFlow:
    """A small forward 3-valued abstract interpretation, DISPLAY ONLY: per
    line, what is definitely known about the globals just before that line
    (lock values, literal writes).  Approximate by construction: a `yield`
    keeps locks held by this thread (only the holder may release under the
    lock discipline) and drops everything else to `?`."""

    def __init__(self, prog: A.Program, ti: TypeInfo):
        self.prog = prog
        self.ti = ti
        self.low = Lowerer(prog, ti)
        self.per_line: Dict[int, Dict[str, str]] = {}
        self.raw: Dict[int, Dict] = {}

    def run(self) -> Dict[int, Dict[str, str]]:
        for f in self.prog.funcs:
            ctx = _Ctx(f"fn:{f.name}", f, atomic=f.is_atomic)
            self.walk(f.body, {}, ctx)
        for th in self.prog.threads:
            self.walk(th.body, {}, _Ctx("thread", None, atomic=False))
        return self.per_line

    # state: dict global -> abstract value (missing = UNKNOWN)
    def record(self, s: A.Stmt, state: Dict) -> None:
        line = s.span.start.line
        if line > 0 and line not in self.per_line:
            self.per_line[line] = {
                g: _fmt_abs(state.get(g, UNKNOWN))
                for g in sorted(self.ti.globals)}
            self.raw[line] = dict(state)

    @staticmethod
    def _join(a: Dict, b: Dict) -> Dict:
        return {g: v for g, v in a.items() if b.get(g, UNKNOWN) == v}

    def _cond_state(self, c: A.Cond, state: Dict, success: bool) -> Dict:
        while isinstance(c, A.NotCond):
            c = c.inner
            success = not success
        if isinstance(c, A.CasCond) and success:
            out = dict(state)
            out[c.target] = _abstract(c.new)
            return out
        return dict(state)

    def walk(self, stmts: List[A.Stmt], state: Dict, ctx: _Ctx) -> Dict:
        for s in stmts:
            self.record(s, state)
            if isinstance(s, A.Acquire):
                state = {**state, s.lock: TID}
            elif isinstance(s, A.Release):
                state = {**state, s.lock: 0}
            elif isinstance(s, A.Assign):
                kind, _ = self.ti.assign_kind[id(s)]
                if kind == "write":
                    state = {**state, s.lhs: _abstract(s.rhs)}
            elif isinstance(s, A.Yield):
                state = {g: v for g, v in state.items()
                         if v is TID and g in self.ti.lock_names}
            elif isinstance(s, A.Call_):
                callee = self.prog.find_func(s.name)
                if callee is not None:
                    state = dict(state)
                    for g in self.low._callee_global_writes(callee):
                        state.pop(g, None)
                    if not callee.is_atomic:
                        # a non-atomic callee yields internally
                        state = {g: v for g, v in state.items()
                                 if v is TID and g in self.ti.lock_names}
            elif isinstance(s, A.If):
                s1 = self.walk(s.then_body,
                               self._cond_state(s.cond, state, True), ctx)
                s2 = self.walk(s.else_body,
                               self._cond_state(s.cond, state, False), ctx)
                state = self._join(s1, s2)
            elif isinstance(s, A.While):
                # facts about loop-modified globals are dropped at the head;
                # what remains is invariant, so it also holds on exit
                entry = dict(state)
                for g in self.low._loop_modified(s, ctx):
                    entry.pop(g, None)
                self.walk(s.body, self._cond_state(s.cond, entry, True), ctx)
                state = entry
        return state


def line_details(prog: A.Program, ti: TypeInfo, source: str) -> List[Dict]:
    """Per-line records for the UI: the mover letter, an explanation of why,
    and the schematic abstract store just before the line."""
    flow = _StoreFlow(prog, ti)
    stores = flow.run()
    effs, expl = _Explainer(prog, ti, source, flow=flow.raw).run()
    return [{"line": line, "effect": eff.value,
             "explain": expl.get(line) or None,
             "store": stores.get(line)}
            for line, eff in sorted(effs.items())]


def render_listing(source: str, ann: Dict[int, str]) -> str:
    """The CLI listing: each source line prefixed with a mover-letter margin."""
    out = []
    for i, line in enumerate(source.splitlines(), start=1):
        letter = ann.get(i, " ")
        out.append(f" {letter} | {line}")
    return "\n".join(out)
