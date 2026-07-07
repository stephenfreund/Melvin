"""Verification-condition generation: lowering Mover Logic to Boogie.

Each function definition, each mover-spec validity condition, and the run-time
state rule become a separate Boogie procedure.  A procedure passes verification
in Boogie iff the corresponding Mover Logic obligation holds.

Store model (inside one procedure, verifying one arbitrary thread `tid`):
  * `v_<g>`   -- current value of store item <g> (global or thread-local)
  * `o_<g>`   -- snapshot at the start of the current reducible sequence
                 (this is what `\\old` denotes in P, Q, and the guarantee G)
  * `pre_<g>` -- snapshot just before an action (what `\\old` denotes in a
                 mover-spec clause)
  * `py_<g>`  -- snapshot just before a yield (what `\\old` denotes in R)
  * `ce_<g>`  -- snapshot at a call site (what `\\old` denotes in a callee's Q)
  * `eff`     -- ghost int tracking the running effect (see prelude codes)

The running effect `eff` is composed with the *exact*, state-sensitive mover of
each action (an `if/else` over the spec clauses), and `assert eff != E` after
every action enforces reducibility (R*[N]L* separated by yields).
"""

from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple

from . import ast_nodes as A
from .boogie_backend import Emitter
from .diagnostics import Span, TypeError_
from .effects import Effect, join_all, seq, star, leq
from .prelude import prelude, EFF_CODE, E_CODE, R_CODE, L_CODE, Y_CODE, B_CODE, N_CODE
from .types import TypeInfo

BUILTIN_FUNCS = {"head", "tail", "Some", "even", "isNone", "theVal"}


class Translator:
    """Translate Mover Logic expressions to Boogie expressions."""

    def __init__(self, ti: TypeInfo):
        self.ti = ti
        self.unknown_funcs: Dict[str, int] = {}   # name -> arity, for uninterpreted decls

    def tr(self, e: A.Expr, cur: Dict[str, str], old: Dict[str, str]) -> str:
        t = type(e)
        if t is A.Num:
            return str(e.value)
        if t is A.BoolLit:
            return "true" if e.value else "false"
        if t is A.NilLit:
            return "Nil"
        if t is A.NoneLit:
            return "None"
        if t is A.Tid:
            return cur.get("tid", "tid")
        if t is A.Result:
            return cur["result"]
        if t is A.Old:
            # \old(e): resolve bare names against the `old` snapshot map.
            return self.tr(e.inner, old, old)
        if t is A.Var:
            name = e.name
            if name in cur:
                return cur[name]
            raise TypeError_(f"unbound variable {name!r} in specification", e.span)
        if t is A.Unary:
            inner = self.tr(e.operand, cur, old)
            op = "!" if e.op == "!" else "-"
            return f"({op}{inner})"
        if t is A.Binary:
            return self._binary(e, cur, old)
        if t is A.Index:
            return f"{self.tr(e.base, cur, old)}[{self.tr(e.index, cur, old)}]"
        if t is A.Call:
            return self._call(e, cur, old)
        if t is A.Quant:
            v = e.var
            cur2 = dict(cur); cur2[v] = v
            old2 = dict(old); old2[v] = v
            lo = self.tr(e.lo, cur, old)
            hi = self.tr(e.hi, cur, old)
            body = self.tr(e.body, cur2, old2)
            if e.kind == "forall":
                return f"(forall {v}: int :: ({lo} <= {v} && {v} < {hi}) ==> ({body}))"
            return f"(exists {v}: int :: ({lo} <= {v} && {v} < {hi}) && ({body}))"
        raise TypeError_(f"cannot translate expression {t.__name__}", getattr(e, "span", None))

    _OPS = {
        "&&": "&&", "||": "||", "==>": "==>", "<==>": "<==>",
        "==": "==", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
        "+": "+", "-": "-", "*": "*", "/": "div", "%": "mod",
    }

    def _binary(self, e: A.Binary, cur, old) -> str:
        l = self.tr(e.left, cur, old)
        r = self.tr(e.right, cur, old)
        if e.op == "::":
            return f"cons({l}, {r})"
        return f"({l} {self._OPS[e.op]} {r})"

    def _call(self, e: A.Call, cur, old) -> str:
        args = ", ".join(self.tr(a, cur, old) for a in e.args)
        if e.name in BUILTIN_FUNCS:
            return f"{e.name}({args})"
        self.unknown_funcs[e.name] = len(e.args)
        return f"{e.name}({args})"


class Lowerer:
    def __init__(self, prog: A.Program, ti: TypeInfo):
        self.prog = prog
        self.ti = ti
        self.tr = Translator(ti)
        self.em = Emitter()

    # ------------------------------------------------------------------ util
    def store_items(self, scope: str) -> List[str]:
        """All store variables visible in a scope: globals + that scope's locals + result."""
        items = list(self.ti.globals.keys())
        locs = self.ti.scope_locals(scope)
        for l in locs:
            items.append(l)
        if "result" not in items and "result" not in locs:
            items.append("result")
        return items

    def btype(self, name: str, scope: str) -> str:
        if name in self.ti.globals:
            return self.ti.globals[name]
        locs = self.ti.scope_locals(scope)
        if name in locs:
            return locs[name]
        if name == "result":
            return "int"
        return "int"

    def cur_map(self, scope: str) -> Dict[str, str]:
        m = {n: f"v_{n}" for n in self.store_items(scope)}
        m["result"] = "v_result"
        m["tid"] = "tid"
        return m

    def snap_map(self, scope: str, snap: str) -> Dict[str, str]:
        m = {n: f"{snap}_{n}" for n in self.store_items(scope)}
        m["result"] = f"{snap}_result"
        m["tid"] = "tid"
        return m

    def declare_vars(self, scope: str) -> None:
        items = self.store_items(scope)
        for n in items:
            bt = self.btype(n, scope)
            for snap in ("v", "o", "pre", "py", "ce"):
                self.em.line(f"var {snap}_{n}: {bt};")
        self.em.line("var tid: int;")
        self.em.line("var eff: int;")
        self.em.line("var mv: int;")
        self.em.line("var le_save: int;")

    def globals_list(self) -> List[str]:
        return list(self.ti.globals.keys())

    def snapshot(self, snap: str, scope: str, only_globals: bool = False) -> None:
        items = self.globals_list() if only_globals else self.store_items(scope)
        for n in items:
            self.em.line(f"{snap}_{n} := v_{n};")

    def restore_seq_start(self, scope: str) -> None:
        for n in self.store_items(scope):
            self.em.line(f"o_{n} := v_{n};")

    # ---------------------------------------------------------------- movers
    def _clauses_for(self, gname: str, access: str) -> List[A.MoverClause]:
        vd = self.prog.find_var(gname)
        if vd is None:
            return []
        out = []
        for cl in vd.clauses:
            if cl.index is not None:
                continue  # element-access clauses handled separately
            if cl.access is None or cl.access == access:
                out.append(cl)
        return out

    def _mover_static(self, gname: str, access: str) -> Effect:
        clauses = self._clauses_for(gname, access)
        return join_all(cl.mover for cl in clauses)

    def _mover_expr(self, gname: str, access: str, scope: str) -> str:
        """Boogie `if/else` selecting the exact state-sensitive mover code.

        `\\old` in a clause refers to the pre-action snapshot `pre_`, bare names
        to the post-action store `v_`.
        """
        clauses = self._clauses_for(gname, access)
        cur = self.cur_map(scope)
        old = self.snap_map(scope, "pre")
        return self._mover_ite(clauses, cur, old)

    def _mover_ite(self, clauses, cur: Dict[str, str], old: Dict[str, str]) -> str:
        """Generic mover selection `if c1 then e1 else ... else E` over `clauses`,
        with `\\old` bound to `old` (the access pre-store) and bare names to `cur`
        (the access post-store)."""
        expr = str(E_CODE)
        for cl in reversed(clauses):
            cond = self.tr.tr(cl.cond, cur, old)
            expr = f"(if {cond} then {EFF_CODE[cl.mover.name]} else {expr})"
        return expr

    def _emit_mover(self, gname: str, access: str, scope: str, span: Span, what: str) -> None:
        """Emit the access-legality assert and compose the running effect."""
        self.em.line(f"mv := {self._mover_expr(gname, access, scope)};")
        self.em.assert_(
            f"mv != {E_CODE}", span,
            f"{what} of {gname!r} is not permitted here by its mover specification "
            f"(possible data race)",
        )
        self.em.line("eff := seqEff(eff, mv);")
        self.em.assert_(
            f"eff != {E_CODE}", span,
            f"{what} of {gname!r} breaks reducibility here: this reducible sequence "
            f"is not of the form R*[N]L* (insert a yield to split it)",
        )

    # -------------------------------------------------------------- programs
    def lower(self) -> Emitter:
        for f in self.prog.funcs:
            if f.is_atomic:
                self.gen_atomic_fn(f)
            else:
                self.gen_nonatomic_fn(f)
        self.gen_validity()
        self.gen_state_checks()
        self.gen_rely_checks()

        # Prepend the prelude plus any uninterpreted-function declarations.
        header = [prelude()]
        for name, arity in sorted(self.tr.unknown_funcs.items()):
            sig = ", ".join(["int"] * arity)
            header.append(f"function {name}({sig}) returns (bool);")
        head = Emitter()
        for line in ("\n".join(header)).splitlines():
            head.raw(line)
        head.blank()
        offset = len(head.lines)
        final = Emitter()
        final.lines = head.lines + self.em.lines
        final.obligations = {ln + offset: ob for ln, ob in self.em.obligations.items()}
        return final

    # ----------------------------------------------------------- atomic defs
    def gen_atomic_fn(self, f: A.FnDecl) -> None:
        scope = f"fn:{f.name}"
        spec: A.AtomicSpec = f.spec
        self.em.blank()
        self.em.line(f"// atomic function {f.name}()  (M-def-atomic)")
        self.em.line(f"procedure {{:entrypoint}} Def_{f.name}()")
        self.em.line("{")
        self.em.indent()
        self.declare_vars(scope)
        self.em.line("assume tid > 0;")
        self.snapshot("o", scope)          # \old == entry store
        cur = self.cur_map(scope)
        self.em.line(f"assume {self.tr.tr(spec.requires, cur, self.snap_map(scope, 'o'))};")
        self.em.line(f"eff := {B_CODE};")  # skip identity
        ctx = _Ctx(scope, f, atomic=True)
        self.emit_block(f.body, ctx)
        # postcondition Q (\old == entry == o_)
        self.em.assert_(
            self.tr.tr(spec.ensures, cur, self.snap_map(scope, "o")),
            f.span, f"postcondition of atomic {f.name}() may not hold",
        )
        # effect must be at most the declared atomic mover  (M-conseq)
        self.em.assert_(
            f"leqEff(eff, {EFF_CODE[spec.mover.name]})", f.span,
            f"body of {f.name}() has a larger effect than its declared "
            f"'atomic {spec.mover.pretty}'",
        )
        self.em.dedent()
        self.em.line("}")

    def gen_nonatomic_fn(self, f: A.FnDecl) -> None:
        scope = f"fn:{f.name}"
        spec: A.NonAtomicSpec = f.spec
        self.em.blank()
        self.em.line(f"// non-atomic function {f.name}()  (M-def-non-atomic)")
        self.em.line(f"procedure {{:entrypoint}} Def_{f.name}()")
        self.em.line("{")
        self.em.indent()
        self.declare_vars(scope)
        self.em.line("assume tid > 0;")
        self.snapshot("o", scope)
        cur = self.cur_map(scope)
        self.em.line(f"assume {self.tr.tr(spec.requires, cur, self.snap_map(scope, 'o'))};")
        self.em.line(f"eff := {B_CODE};")
        ctx = _Ctx(scope, f, atomic=False, relies=spec.relies, guarantees=spec.guarantees)
        self.emit_block(f.body, ctx)
        # postcondition two(T): T over the current store
        self.em.assert_(
            self.tr.tr(spec.ensures, cur, cur),
            f.span, f"postcondition of {f.name}() may not hold",
        )
        # body must consist of reducible sequences and end in a yield: effect <= R
        self.em.assert_(
            f"leqEff(eff, {R_CODE})", f.span,
            f"body of non-atomic {f.name}() must consist of reducible sequences "
            f"separated by yields and end in a yield (effect must be <= right-mover)",
        )
        self.em.dedent()
        self.em.line("}")

    # ------------------------------------------------------------ statements
    def emit_block(self, body: List[A.Stmt], ctx: "_Ctx") -> None:
        for s in body:
            self.emit_stmt(s, ctx)

    def emit_stmt(self, s: A.Stmt, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        if isinstance(s, A.Skip):
            return
        if isinstance(s, A.Wrong):
            self.em.assert_("false", s.span, "this program point (wrong) is reachable")
            return
        if isinstance(s, A.Assert):
            # An assertion is a two-store predicate: `\old` binds to the start of
            # the current reducible sequence (the `o_` snapshot), like P and Q.
            self.em.assert_(self.tr.tr(s.expr, cur, self.snap_map(scope, "o")),
                            s.span, "assertion may not hold")
            return
        if isinstance(s, A.Yield):
            self.emit_yield(s, ctx)
            return
        if isinstance(s, A.Acquire):
            self.emit_acquire(s, ctx)
            return
        if isinstance(s, A.Release):
            self.emit_release(s, ctx)
            return
        if isinstance(s, A.Assign):
            self.emit_assign(s, ctx)
            return
        if isinstance(s, A.UnstableRead):
            self.snapshot("pre", scope, only_globals=True)
            self.em.line(f"havoc v_{s.lhs};")
            self.em.line(f"eff := seqEff(eff, {R_CODE});")  # unstable read is a right-mover
            self.em.assert_(f"eff != {E_CODE}", s.span,
                            "unstable read breaks reducibility here")
            return
        if isinstance(s, A.If):
            self.emit_if(s, ctx)
            return
        if isinstance(s, A.While):
            self.emit_while(s, ctx)
            return
        if isinstance(s, A.Call_):
            self.emit_call(s, ctx)
            return
        raise TypeError_(f"cannot lower statement {type(s).__name__}", s.span)

    def emit_assign(self, s: A.Assign, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        kind, gvar = self.ti.assign_kind[id(s)]
        if kind == "write":
            self.snapshot("pre", scope, only_globals=True)
            self.em.line(f"v_{s.lhs} := {self.tr.tr(s.rhs, cur, cur)};")
            self._emit_mover(s.lhs, "write", scope, s.span, "write")
        elif kind == "read":
            self.snapshot("pre", scope, only_globals=True)
            self._emit_mover(gvar, "read", scope, s.span, "read")
            self.em.line(f"v_{s.lhs} := v_{gvar};")
        else:  # local computation: both-mover, no effect change
            self.em.line(f"v_{s.lhs} := {self.tr.tr(s.rhs, cur, cur)};")

    def emit_acquire(self, s: A.Acquire, ctx: "_Ctx") -> None:
        scope = ctx.scope
        self.snapshot("pre", scope, only_globals=True)
        # acquire blocks unless the lock is free (guard: \old(m) == 0)
        self.em.line(f"assume pre_{s.lock} == 0;")
        self.em.line(f"v_{s.lock} := tid;")
        self._emit_mover(s.lock, "write", scope, s.span, "acquire")

    def emit_release(self, s: A.Release, ctx: "_Ctx") -> None:
        scope = ctx.scope
        self.snapshot("pre", scope, only_globals=True)
        self.em.line(f"v_{s.lock} := 0;")
        self._emit_mover(s.lock, "write", scope, s.span, "release")

    def emit_yield(self, s: A.Yield, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        if ctx.atomic:
            # atomic functions use G = false, so any reachable yield fails.
            self.em.assert_("false", s.span,
                            "atomic functions may not contain a yield")
            return
        # P => G  (G over \old = reducible-sequence start = o_)
        self.em.assert_(
            self.tr.tr(ctx.guarantees, cur, self.snap_map(scope, "o")),
            s.span, "the guarantee G may be violated by the reducible sequence "
                    "before this yield",
        )
        # interference: havoc globals and assume the rely once; this models R*
        # because gen_rely_checks proves R reflexive and transitive
        self.snapshot("py", scope, only_globals=True)
        for g in self.globals_list():
            self.em.line(f"havoc v_{g};")
        self.em.line(
            f"assume {self.tr.tr(ctx.relies, cur, self.snap_map(scope, 'py'))};"
        )
        # start a new reducible sequence
        self.restore_seq_start(scope)
        self.em.line(f"eff := seqEff(eff, {Y_CODE});")

    def emit_if(self, s: A.If, ctx: "_Ctx") -> None:
        scope = ctx.scope
        self.em.line("if (*) {")
        self.em.indent()
        self.emit_action_success(s.cond, ctx)
        self.emit_block(s.then_body, ctx)
        self.em.dedent()
        self.em.line("} else {")
        self.em.indent()
        self.emit_action_fail(s.cond, ctx)
        self.emit_block(s.else_body, ctx)
        self.em.dedent()
        self.em.line("}")

    def emit_while(self, s: A.While, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        inv = self.tr.tr(s.invariant, cur, self.snap_map(scope, "o")) if s.invariant else "true"
        # Static (state-insensitive) effect of one iteration, used only for the
        # termination side-condition and downstream effect (over-approximation).
        iter_static = self._loop_iter_static(s, ctx)
        a2_static = self._cond_fail_static(s.cond)
        loop_static = seq(star(iter_static), a2_static)
        if leq(loop_static, Effect.L):
            raise TypeError_(
                "loop may fail to terminate after committing: its effect is "
                f"'{loop_static.pretty}' (<= left-mover); a reducible loop must "
                "not lie entirely in the post-commit (left-mover) region",
                s.span,
            )
        modified = self._loop_modified(s, ctx)
        self.em.line("// while loop (M-while); each iteration must be a right-mover-or-less")
        self.em.line("le_save := eff;")            # effect before the loop
        self.em.assert_(inv, s.span, "loop invariant may not hold on entry")
        for g in modified:
            self.em.line(f"havoc v_{g};")
        self.em.line(f"assume {inv};")
        self.em.line("if (*) {")
        self.em.indent()
        self.em.line(f"eff := {B_CODE};")          # one arbitrary iteration, fresh
        self.emit_action_success(s.cond, ctx)      # exact successful test A1
        self.emit_block(s.body, ctx)
        self.em.assert_(inv, s.span, "loop body may not preserve the loop invariant")
        self.em.assert_(f"leqEff(eff, {R_CODE})", s.span,
                        "loop body is not reducible (its effect exceeds a right-mover; "
                        "a reducible loop may not commit inside the loop)")
        self.em.line("assume false;")              # cut this iteration
        self.em.dedent()
        self.em.line("}")
        # Exit path: compose the (static) iteration closure, then the *exact*
        # loop-exit action A2, so the loop's overall effect is precise on exit.
        self.em.line(f"eff := seqEff(le_save, {EFF_CODE[star(iter_static).name]});")
        self.emit_action_fail(s.cond, ctx)         # exact failing test A2 (composes into eff)
        self.em.assert_(f"eff != {E_CODE}", s.span,
                        "loop breaks reducibility in its surrounding sequence")

    # ------------------------------------------------- conditional actions
    def emit_action_success(self, c: A.Cond, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        if isinstance(c, A.NotCond):
            self.emit_action_fail(c.inner, ctx)
            return
        if isinstance(c, A.BoolCond):
            self.em.line(f"assume {self.tr.tr(c.expr, cur, cur)};")
            return
        if isinstance(c, A.CasCond):
            self.snapshot("pre", scope, only_globals=True)
            self.em.line(f"assume pre_{c.target} == {self.tr.tr(c.expected, cur, cur)};")
            self.em.line(f"v_{c.target} := {self.tr.tr(c.new, cur, cur)};")
            self._emit_mover(c.target, "write", scope, c.span, "successful cas")
            return
        raise TypeError_("unknown conditional action", c.span)

    def emit_action_fail(self, c: A.Cond, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        if isinstance(c, A.NotCond):
            self.emit_action_success(c.inner, ctx)
            return
        if isinstance(c, A.BoolCond):
            self.em.line(f"assume !({self.tr.tr(c.expr, cur, cur)});")
            return
        if isinstance(c, A.CasCond):
            # failing cas is the identity action and a both-mover; no effect change.
            self.em.line("assume true;")
            return
        raise TypeError_("unknown conditional action", c.span)

    def _cond_fail_static(self, c: A.Cond) -> Effect:
        if isinstance(c, A.NotCond):
            return self._cond_success_static(c.inner)
        if isinstance(c, A.BoolCond):
            return Effect.B
        if isinstance(c, A.CasCond):
            return Effect.B
        return Effect.B

    def _cond_success_static(self, c: A.Cond) -> Effect:
        if isinstance(c, A.NotCond):
            return self._cond_fail_static(c.inner)
        if isinstance(c, A.BoolCond):
            return Effect.B
        if isinstance(c, A.CasCond):
            return self._mover_static(c.target, "write")
        return Effect.B

    def _loop_iter_static(self, s: A.While, ctx: "_Ctx") -> Effect:
        eff = self._cond_success_static(s.cond)
        for st in s.body:
            eff = seq(eff, self._stmt_static(st, ctx))
        return eff

    def _stmt_static(self, s: A.Stmt, ctx: "_Ctx") -> Effect:
        if isinstance(s, (A.Skip, A.Assert)):
            return Effect.B
        if isinstance(s, A.Yield):
            return Effect.Y
        if isinstance(s, A.Wrong):
            return Effect.B
        if isinstance(s, A.UnstableRead):
            return Effect.R
        if isinstance(s, A.Acquire) or isinstance(s, A.Release):
            return self._mover_static(s.lock, "write")
        if isinstance(s, A.Assign):
            kind, gvar = self.ti.assign_kind[id(s)]
            if kind == "write":
                return self._mover_static(s.lhs, "write")
            if kind == "read":
                return self._mover_static(gvar, "read")
            return Effect.B
        if isinstance(s, A.If):
            a1 = self._cond_success_static(s.cond)
            a2 = self._cond_fail_static(s.cond)
            t = a1
            for st in s.then_body:
                t = seq(t, self._stmt_static(st, ctx))
            e = a2
            for st in s.else_body:
                e = seq(e, self._stmt_static(st, ctx))
            from .effects import join
            return join(t, e)
        if isinstance(s, A.While):
            it = self._loop_iter_static(s, ctx)
            return seq(star(it), self._cond_fail_static(s.cond))
        if isinstance(s, A.Call_):
            callee = self.prog.find_func(s.name)
            if callee is not None and callee.is_atomic:
                return callee.spec.mover
            return Effect.R
        return Effect.B

    def _loop_modified(self, s: A.While, ctx: "_Ctx") -> List[str]:
        mods: Set[str] = set()

        def scan(stmts: List[A.Stmt]):
            for st in stmts:
                if isinstance(st, A.Assign) and st.lhs in self.ti.globals:
                    mods.add(st.lhs)
                if isinstance(st, (A.Acquire, A.Release)):
                    mods.add(st.lock)
                if isinstance(st, A.If):
                    if isinstance(st.cond, A.CasCond):
                        mods.add(st.cond.target)
                    scan(st.then_body); scan(st.else_body)
                if isinstance(st, A.While):
                    if isinstance(st.cond, A.CasCond):
                        mods.add(st.cond.target)
                    scan(st.body)
                if isinstance(st, A.Call_):
                    mods.update(self.ti.globals.keys())
        if isinstance(s.cond, A.CasCond):
            mods.add(s.cond.target)
        if isinstance(s.cond, A.NotCond) and isinstance(s.cond.inner, A.CasCond):
            mods.add(s.cond.inner.target)
        scan(s.body)
        return [g for g in self.globals_list() if g in mods]

    # -------------------------------------------------------- function calls
    def emit_call(self, s: A.Call_, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        callee = self.prog.find_func(s.name)
        # snapshot call entry for the callee's \old
        self.snapshot("ce", scope)
        if callee.is_atomic:
            spec: A.AtomicSpec = callee.spec
            self.em.assert_(
                self.tr.tr(spec.requires, cur, cur), s.span,
                f"precondition of atomic {s.name}() may not hold at this call",
            )
            self._havoc_callee_effects(callee, scope)
            self.em.line(f"assume {self.tr.tr(spec.ensures, cur, self.snap_map(scope, 'ce'))};")
            self.em.line(f"eff := seqEff(eff, {EFF_CODE[spec.mover.name]});")
            self.em.assert_(f"eff != {E_CODE}", s.span,
                            f"call to {s.name}() breaks reducibility here")
        else:
            spec: A.NonAtomicSpec = callee.spec
            # M-call-non-atomic: current reducible sequence must be trivial (S holds)
            self.em.assert_(
                self.tr.tr(spec.requires, cur, cur), s.span,
                f"precondition of {s.name}() may not hold at this call",
            )
            self._havoc_callee_effects(callee, scope)
            self.em.line(f"assume {self.tr.tr(spec.ensures, cur, cur)};")
            self.restore_seq_start(scope)
            self.em.line(f"eff := seqEff(eff, {R_CODE});")
            self.em.assert_(f"eff != {E_CODE}", s.span,
                            f"call to {s.name}() breaks reducibility here")

    def _havoc_callee_effects(self, callee: A.FnDecl, caller_scope: str) -> None:
        # Havoc exactly the globals the callee writes and the locals it assigns.
        # (Mover Logic omits frame conditions, so callee ensures must pin what
        #  matters; we havoc writes and let the ensures constrain them.)
        gwrites = self._callee_global_writes(callee)
        for g in gwrites:
            self.em.line(f"havoc v_{g};")
        caller_items = set(self.store_items(caller_scope))
        for l in self._callee_local_writes(callee):
            # Only locals visible in the caller need havocking; the callee's
            # private working locals do not affect the caller's state.
            if l in caller_items:
                self.em.line(f"havoc v_{l};")

    def _callee_global_writes(self, callee: A.FnDecl) -> List[str]:
        out: Set[str] = set()

        def scan(stmts):
            for st in stmts:
                if isinstance(st, A.Assign) and st.lhs in self.ti.globals:
                    out.add(st.lhs)
                if isinstance(st, (A.Acquire, A.Release)):
                    out.add(st.lock)
                if isinstance(st, A.If):
                    if isinstance(st.cond, A.CasCond):
                        out.add(st.cond.target)
                    if isinstance(st.cond, A.NotCond) and isinstance(st.cond.inner, A.CasCond):
                        out.add(st.cond.inner.target)
                    scan(st.then_body); scan(st.else_body)
                if isinstance(st, A.While):
                    if isinstance(st.cond, A.CasCond):
                        out.add(st.cond.target)
                    if isinstance(st.cond, A.NotCond) and isinstance(st.cond.inner, A.CasCond):
                        out.add(st.cond.inner.target)
                    scan(st.body)
        scan(callee.body)
        return [g for g in self.globals_list() if g in out]

    def _callee_local_writes(self, callee: A.FnDecl) -> List[str]:
        scope = f"fn:{callee.name}"
        locs = self.ti.scope_locals(scope)
        out: Set[str] = set()

        def scan(stmts):
            for st in stmts:
                if isinstance(st, A.Assign) and st.lhs not in self.ti.globals:
                    out.add(st.lhs)
                if isinstance(st, A.UnstableRead):
                    out.add(st.lhs)
                if isinstance(st, A.If):
                    scan(st.then_body); scan(st.else_body)
                if isinstance(st, A.While):
                    scan(st.body)
        scan(callee.body)
        # only locals that are shared thread-local names (present in caller too);
        # havoc them all conservatively -- they are the callee's working locals.
        return sorted(out)

    # -------------------------------------------------- mover-spec validity
    def gen_validity(self) -> None:
        """Check mover-specification validity (paper's Validity definition).

        All four conditions are checked, for every ordered pair of variables
        X (accessed by thread t) and Y (accessed by thread u), with t != u:

          (1) a right-mover of t commutes to the right of a following non-mover
              of u;
          (2) a left-mover of u commutes to the left of a preceding non-mover
              of t;
          (3) an action of t does not change the mover u computes;
          (4) a non-mover of t cannot cause a left-mover of u to block.

        Actions are modelled exactly as in the paper: a write to a variable X is
        <X = v> for an arbitrary local-determined value v (total), and a read is
        the identity on the shared store.  Because writes are deterministic and
        their post-values do not depend on the shared store, the existential
        witness store required by conditions (1), (2), (4) is *constructed*
        explicitly (apply the two actions in the opposite order), so each
        condition becomes an ordinary Boogie assertion rather than a quantifier
        alternation.  Reads and other store-identity actions (failing cas,
        unstable reads) commute trivially and are omitted from (1),(2),(4).
        """
        self.em.blank()
        self.em.line("// ==== Mover specification validity (Definition: Validity) ====")
        for xw in self.prog.vars:
            for yv in self.prog.vars:
                self._validity3(xw, yv)
        writable = [vd for vd in self.prog.vars if self._clauses_for(vd.name, "write")]
        for xw in writable:
            for yw in writable:
                self._validity_commute(1, xw, yw)
                self._validity_commute(2, xw, yw)
                self._validity_commute(4, xw, yw)

    def _validity_commute(self, num: int, xw: A.VarDecl, yw: A.VarDecl) -> None:
        """Emit conditions (1), (2), or (4) for the write-pair (X by t, Y by u).

        Let sigma be the pre-store, sigma' = sigma[X := v1], and consider the two
        write actions A1 = <X := v1> (thread t) and A2 = <Y := v2> (thread u).
        We assume the condition's mover hypotheses and assert that the two
        actions produce the same final store in either order (the commuting
        witness).  For X != Y this holds structurally; for X == Y it forces the
        two writes to agree, so a spec that lets two threads make conflicting
        non-both-mover writes to the same location is rejected.
        """
        gl = list(self.ti.globals.keys())
        X, Y = xw.name, yw.name
        xty, yty = self.ti.globals[X], self.ti.globals[Y]
        xwrite = self._clauses_for(X, "write")
        ywrite = self._clauses_for(Y, "write")

        sigma = {**{g: f"s_{g}" for g in gl}}
        sigmaX = {**sigma, X: "v1"}                       # sigma' = sigma[X:=v1]
        sigmaXY = {**sigmaX, Y: "v2"}                     # sigma'' = sigma'[Y:=v2]
        sigmaY = {**sigma, Y: "v2"}                       # sigma[Y:=v2] (for cond 4)

        def m(clauses, tv, cur, old):
            c = {**cur, "tid": tv}
            o = {**old, "tid": tv}
            return self._mover_ite(clauses, c, o)

        moverX_t = m(xwrite, "t", sigmaX, sigma)          # M(A1, t, sigma)
        if num == 1:
            h1 = f"leqEff({moverX_t}, {R_CODE})"
            h2 = f"leqEff({m(ywrite, 'u', sigmaXY, sigmaX)}, {N_CODE})"  # M(A2,u,sigma')<=N
        elif num == 2:
            h1 = f"leqEff({moverX_t}, {N_CODE})"
            h2 = f"leqEff({m(ywrite, 'u', sigmaXY, sigmaX)}, {L_CODE})"  # M(A2,u,sigma')<=L
        else:  # num == 4
            h1 = f"leqEff({moverX_t}, {N_CODE})"
            h2 = f"leqEff({m(ywrite, 'u', sigmaY, sigma)}, {L_CODE})"    # M(A2,u,sigma)<=L

        # Commuting witness: sigma[X:=v1][Y:=v2] equals sigma[Y:=v2][X:=v1].
        post_XY = {**{g: sigma[g] for g in gl}, X: "v1"}
        post_XY[Y] = "v2"
        post_YX = {**{g: sigma[g] for g in gl}, Y: "v2"}
        post_YX[X] = "v1"
        eqs = " && ".join(f"({post_XY[g]} == {post_YX[g]})" for g in gl)

        self.em.blank()
        self.em.line(f"// validity({num}): writes to {X!r} (t) and {Y!r} (u) commute")
        self.em.line(f"procedure {{:entrypoint}} Valid{num}_{X}_{Y}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var s_{g}: {self.ti.globals[g]};")
        self.em.line(f"var v1: {xty}; var v2: {yty};")
        self.em.line("var t: int; var u: int;")
        self.em.line("assume t > 0 && u > 0 && t != u;")
        self.em.line(f"assume {h1};")
        self.em.line(f"assume {h2};")
        self.em.assert_(
            eqs, xw.span,
            f"invalid mover specification: a {self._cond_name(num)} to {X!r} by one "
            f"thread and a write to {Y!r} by another do not commute "
            f"(validity condition {num} fails)",
        )
        self.em.dedent()
        self.em.line("}")

    @staticmethod
    def _cond_name(num: int) -> str:
        return {1: "right-mover write", 2: "non-mover write",
                4: "non-mover write"}[num]

    def _validity3(self, xw: A.VarDecl, yv: A.VarDecl) -> None:
        gl = list(self.ti.globals.keys())
        xw_write = [cl for cl in xw.clauses if cl.index is None
                    and cl.access in (None, "write")]
        if not xw_write:
            return
        # Build the mover-selection expression for an access to Y by thread u.
        def mover_of_y(access: str, store_cur, store_old) -> str:
            expr = str(E_CODE)
            clauses = [cl for cl in yv.clauses if cl.index is None
                       and cl.access in (None, access)]
            for cl in reversed(clauses):
                cond = self.tr.tr(cl.cond, store_cur, store_old)
                expr = f"(if {cond} then {EFF_CODE[cl.mover.name]} else {expr})"
            return expr

        # Store `sig` (pre) and `sig2` (post, X changed) share all vars but X.
        pre = {**{g: f"s_{g}" for g in gl}, "tid": "u"}
        post = {**{g: (f"s2_{xw.name}" if g == xw.name else f"s_{g}") for g in gl},
                "tid": "u"}
        # Writer's own mover (thread t) must be well-defined (!= E) for this step.
        wexpr = str(E_CODE)
        writer_cur = {**{g: (f"s2_{xw.name}" if g == xw.name else f"s_{g}") for g in gl},
                      "tid": "t"}
        writer_old = {**{g: f"s_{g}" for g in gl}, "tid": "t"}
        for cl in reversed(xw_write):
            cond = self.tr.tr(cl.cond, writer_cur, writer_old)
            wexpr = f"(if {cond} then {EFF_CODE[cl.mover.name]} else {wexpr})"

        self.em.blank()
        self.em.line(f"// validity(3): a write to {xw.name!r} by t keeps {yv.name!r}'s mover for u")
        self.em.line(f"procedure {{:entrypoint}} Valid3_{xw.name}_{yv.name}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var s_{g}: {self.ti.globals[g]};")
        self.em.line(f"var s2_{xw.name}: {self.ti.globals[xw.name]};")
        self.em.line("var t: int; var u: int;")
        self.em.line("assume t > 0 && u > 0 && t != u;")
        self.em.line(f"assume {wexpr} != {E_CODE};")   # t's write is well-defined
        for access in ("read", "write"):
            y_before = mover_of_y(access, pre, pre)
            y_after = mover_of_y(access, post, post)
            self.em.assert_(
                f"({y_before}) == ({y_after})", yv.span,
                f"invalid mover specification: a write to {xw.name!r} by one thread "
                f"can change the {access} mover of {yv.name!r} for another thread "
                f"(validity condition 3 fails)",
            )
        self.em.dedent()
        self.em.line("}")

    # ------------------------------------------------------- state checks
    def gen_state_checks(self) -> None:
        """M-state obligations that are independent of a single thread body:
        the guarantee is reflexive (I => G) and each thread's guarantee is
        contained in every other thread's rely (G_t => R_u)."""
        thread_fns = self._thread_functions()
        if not thread_fns:
            return
        self.em.blank()
        self.em.line("// ==== run-time state rule (M-state) ====")
        # Deduplicate by function name; count how many threads run each role so
        # we know whether a role can interfere with *another copy of itself*.
        by_name: Dict[str, A.FnDecl] = {}
        counts: Dict[str, int] = {}
        for f in thread_fns:
            by_name[f.name] = f
            counts[f.name] = counts.get(f.name, 0) + 1
        unique = [f for f in by_name.values() if isinstance(f.spec, A.NonAtomicSpec)]
        for f in unique:
            self._reflexive_guarantee(f)
        # G_t => R_u for each ordered pair of distinct thread roles, plus a role
        # against itself when at least two threads run it.
        for ft in unique:
            for fu in unique:
                if ft.name == fu.name and counts[ft.name] < 2:
                    continue
                self._guarantee_implies_rely(ft, fu)
        if self.prog.init is not None:
            self._init_establishes(unique)

    def _thread_functions(self) -> List[A.FnDecl]:
        out = []
        for th in self.prog.threads:
            fn = self._single_call_target(th.body)
            if fn is not None:
                out.append(fn)
        return out

    def _single_call_target(self, body: List[A.Stmt]) -> Optional[A.FnDecl]:
        calls = [s for s in body if isinstance(s, A.Call_)]
        non_yield = [s for s in body if not isinstance(s, (A.Yield, A.Skip))]
        if len(calls) == 1 and len(non_yield) == 1:
            return self.prog.find_func(calls[0].name)
        return None

    def _reflexive_guarantee(self, f: A.FnDecl) -> None:
        spec: A.NonAtomicSpec = f.spec
        gl = list(self.ti.globals.keys())
        self.em.blank()
        self.em.line(f"// I => G for {f.name}()  (guarantee is reflexive)")
        self.em.line(f"procedure {{:entrypoint}} Reflexive_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var v_{g}: {self.ti.globals[g]};")
        self.em.line("var tid: int; assume tid > 0;")
        cur = {**{g: f"v_{g}" for g in gl}, "tid": "tid"}
        self.em.assert_(self.tr.tr(spec.guarantees, cur, cur), f.span,
                        f"guarantee of {f.name}() is not reflexive (I => G fails)")
        self.em.dedent()
        self.em.line("}")

    def _guarantee_implies_rely(self, ft: A.FnDecl, fu: A.FnDecl) -> None:
        gspec: A.NonAtomicSpec = ft.spec
        rspec: A.NonAtomicSpec = fu.spec
        gl = list(self.ti.globals.keys())
        self.em.blank()
        self.em.line(f"// G[{ft.name}] => R[{fu.name}] for distinct threads")
        self.em.line(f"procedure {{:entrypoint}} GR_{ft.name}_{fu.name}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var v_{g}: {self.ti.globals[g]}; var o_{g}: {self.ti.globals[g]};")
        self.em.line("var t: int; var u: int; assume t > 0 && u > 0 && t != u;")
        cur_t = {**{g: f"v_{g}" for g in gl}, "tid": "t"}
        old_t = {**{g: f"o_{g}" for g in gl}, "tid": "t"}
        cur_u = {**{g: f"v_{g}" for g in gl}, "tid": "u"}
        old_u = {**{g: f"o_{g}" for g in gl}, "tid": "u"}
        g_expr = self.tr.tr(gspec.guarantees, cur_t, old_t)
        r_expr = self.tr.tr(rspec.relies, cur_u, old_u)
        self.em.line(f"assume {g_expr};")
        self.em.assert_(r_expr, fu.span,
                        f"guarantee of {ft.name}() is not contained in the rely of "
                        f"{fu.name}() (G_t => R_u fails)")
        self.em.dedent()
        self.em.line("}")

    def _init_establishes(self, thread_fns: List[A.FnDecl]) -> None:
        gl = list(self.ti.globals.keys())
        self.em.blank()
        self.em.line("// initial store establishes each thread precondition (M-state)")
        self.em.line("procedure {:entrypoint} Init_establishes()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var v_{g}: {self.ti.globals[g]};")
        self.em.line("var tid: int; assume tid > 0;")
        cur = {**{g: f"v_{g}" for g in gl}, "tid": "tid"}
        self.em.line(f"assume {self.tr.tr(self.prog.init.pred, cur, cur)};")
        for f in thread_fns:
            spec = f.spec
            req = spec.requires if hasattr(spec, "requires") else None
            if req is not None:
                self.em.assert_(self.tr.tr(req, cur, cur), self.prog.init.span,
                                f"initial store may not satisfy the precondition of "
                                f"{f.name}()")
        self.em.dedent()
        self.em.line("}")

    # ------------------------------------- rely well-formedness (R must be R*)
    def gen_rely_checks(self) -> None:
        """`emit_yield` assumes the rely ONCE to summarise any finite number of
        interference steps (the paper quantifies over R*).  A single assumed
        step soundly models R* only if R is its own reflexive-transitive
        closure, so both properties are discharged for every non-atomic
        function.  (Guarantees need no closure check: they are asserted one
        reducible sequence at a time, and multi-step composition is absorbed
        entirely on the rely side.)"""
        nonatomic = [f for f in self.prog.funcs if not f.is_atomic]
        if not nonatomic:
            return
        self.em.blank()
        self.em.line("// ==== rely well-formedness: R must equal R* ====")
        for f in nonatomic:
            self._rely_reflexive(f)
            self._rely_transitive(f)

    def _rely_reflexive(self, f: A.FnDecl) -> None:
        spec: A.NonAtomicSpec = f.spec
        gl = list(self.ti.globals.keys())
        self.em.blank()
        self.em.line(f"// R(s, s) for {f.name}()  (rely is reflexive)")
        self.em.line(f"procedure {{:entrypoint}} RelyRefl_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            self.em.line(f"var a_{g}: {self.ti.globals[g]};")
        self.em.line("var tid: int; assume tid > 0;")
        s = {**{g: f"a_{g}" for g in gl}, "tid": "tid"}
        self.em.assert_(
            self.tr.tr(spec.relies, s, s), spec.relies.span,
            f"rely of {f.name}() is not reflexive: the environment may take no "
            f"steps at a yield, so R must admit an unchanged store",
        )
        self.em.dedent()
        self.em.line("}")

    def _rely_transitive(self, f: A.FnDecl) -> None:
        spec: A.NonAtomicSpec = f.spec
        gl = list(self.ti.globals.keys())
        self.em.blank()
        self.em.line(f"// R;R => R for {f.name}()  (rely is transitive)")
        self.em.line(f"procedure {{:entrypoint}} RelyTrans_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g in gl:
            t = self.ti.globals[g]
            self.em.line(f"var a_{g}: {t}; var b_{g}: {t}; var c_{g}: {t};")
        self.em.line("var tid: int; assume tid > 0;")
        sa = {**{g: f"a_{g}" for g in gl}, "tid": "tid"}
        sb = {**{g: f"b_{g}" for g in gl}, "tid": "tid"}
        sc = {**{g: f"c_{g}" for g in gl}, "tid": "tid"}
        self.em.line(f"assume {self.tr.tr(spec.relies, sb, sa)};")
        self.em.line(f"assume {self.tr.tr(spec.relies, sc, sb)};")
        self.em.assert_(
            self.tr.tr(spec.relies, sc, sa), spec.relies.span,
            f"rely of {f.name}() is not transitive: two successive interference "
            f"steps do not compose into one rely step, so the single rely "
            f"assumed at a yield cannot model R*",
        )
        self.em.dedent()
        self.em.line("}")


class _Ctx:
    def __init__(self, scope: str, fn: Optional[A.FnDecl], atomic: bool,
                 relies: Optional[A.Expr] = None, guarantees: Optional[A.Expr] = None):
        self.scope = scope
        self.fn = fn
        self.atomic = atomic
        self.relies = relies
        self.guarantees = guarantees


def lower_program(prog: A.Program, ti: TypeInfo) -> Emitter:
    return Lowerer(prog, ti).lower()
