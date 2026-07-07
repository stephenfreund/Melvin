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


def render_listing(source: str, ann: Dict[int, str]) -> str:
    """The CLI listing: each source line prefixed with a mover-letter margin."""
    out = []
    for i, line in enumerate(source.splitlines(), start=1):
        letter = ann.get(i, " ")
        out.append(f" {letter} | {line}")
    return "\n".join(out)
