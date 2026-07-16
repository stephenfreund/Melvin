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

The heap: each class C contributes shared store items alongside the scalar
globals -- one Boogie map per field (`f_<C>_<fld>: [C]T`) and an allocation
set (`alloc_<C>: [C]bool`).  Because a whole map is just another store item
(Boogie permits map-typed variables and whole-map assignment), all snapshot
machinery above applies unchanged; a field access `e.f` translates to
`f_<C>_<fld>[e]` against the appropriate snapshot.  Field mover clauses are
evaluated with `this` bound to the receiver of the access.

The running effect `eff` is composed with the *exact*, state-sensitive mover of
each action (an `if/else` over the spec clauses), and `assert eff != E` after
every action enforces reducibility (R*[N]L* separated by yields).  The proof
rules state their effect antecedents as upper bounds (`M(A,P) <= e`, etc.), so
the exact minimal effect is always a valid -- and optimal -- ascription; the
two places a *larger* effect must be ascribed are loops (M-while's ascribed
effect may not be `<= L`) and blocking acquires (M-action's totality side
condition), both handled by `effects.bump_not_left` / the prelude's `bumpEff`.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple

from . import ast_nodes as A
from .boogie_backend import Emitter
from .diagnostics import Span, TypeError_
from .effects import Effect, bump_not_left, join_all, seq, star, leq
from .prelude import prelude, EFF_CODE, E_CODE, R_CODE, L_CODE, Y_CODE, B_CODE, N_CODE
from .types import TypeInfo, type_to_boogie


def _unwrap_not(c: A.Cond) -> A.Cond:
    while isinstance(c, A.NotCond):
        c = c.inner
    return c

BUILTIN_FUNCS = {"head", "tail", "Some", "even", "isNone", "theVal"}


def fmap_name(cls: str, fld: str) -> str:
    """Boogie name of the per-field heap map of class `cls`."""
    return f"f_{cls}_{fld}"


def alloc_name(cls: str) -> str:
    """Boogie name of the allocation set of class (or array type) `cls`."""
    return f"alloc_{cls}"


def null_name(cls: str) -> str:
    return f"null_{cls}"


def arr_elems_name(at: str) -> str:
    """Boogie name of the elements map of array type `at` (= Arr_C_f)."""
    return f"elems_{at[4:]}"


def arr_len_name(at: str) -> str:
    return f"len_{at[4:]}"


def default_value(boogie_type: str) -> Optional[str]:
    """Default a freshly allocated field of this type starts with (None if the
    type has no canonical default; the field then starts unconstrained)."""
    if boogie_type == "int":
        return "0"
    if boogie_type == "bool":
        return "false"
    if boogie_type == "List":
        return "Nil"
    if boogie_type == "Optional":
        return "None"
    if boogie_type.startswith("["):      # array-typed fields: no default
        return None
    if boogie_type in ("Value",):
        return None
    return null_name(boogie_type)        # a class reference


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
        if t is A.NullLit:
            return null_name(self.ti.expr_class[id(e)])
        if t is A.FieldAccess:
            cls = self.ti.expr_class[id(e)]
            m = fmap_name(cls, e.field)
            if m not in cur:
                raise TypeError_(f"field {e.field!r} is not accessible here", e.span)
            return f"{cur[m]}[{self.tr(e.base, cur, old)}]"
        if t is A.Index and id(e) in self.ti.expr_class:
            at = self.ti.expr_class[id(e)]
            m = arr_elems_name(at)
            return (f"{cur[m]}[{self.tr(e.base, cur, old)}]"
                    f"[{self.tr(e.index, cur, old)}]")
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
            body = self.tr(e.body, cur2, old2)
            if e.cls is not None:
                bt = e.cls
                if "." in bt:
                    cname, fname = bt.split(".", 1)
                    bt = self.ti.array_fields[(cname, fname)]
                if e.kind == "forall":
                    return f"(forall {v}: {bt} :: ({body}))"
                return f"(exists {v}: {bt} :: ({body}))"
            lo = self.tr(e.lo, cur, old)
            hi = self.tr(e.hi, cur, old)
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
        if e.name == "length" and id(e) in self.ti.expr_class:
            at = self.ti.expr_class[id(e)]
            return f"{cur[arr_len_name(at)]}[{self.tr(e.args[0], cur, old)}]"
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
        # Heap store items: one map per field plus an allocation set per class.
        self.heap_types: Dict[str, str] = {}   # item name -> boogie type
        for cname, fields in ti.classes.items():
            self.heap_types[alloc_name(cname)] = f"[{cname}]bool"
            for fld, ft in fields.items():
                self.heap_types[fmap_name(cname, fld)] = f"[{cname}]{ft}"
        for at, elemty in ti.arrays.items():
            self.heap_types[alloc_name(at)] = f"[{at}]bool"
            self.heap_types[arr_elems_name(at)] = f"[{at}][int]{elemty}"
            self.heap_types[arr_len_name(at)] = f"[{at}]int"
        # reverse lookup: array type -> its declaring (class, field)
        self.arr_field: Dict[str, Tuple[str, str]] = {
            at: cf for cf, at in ti.array_fields.items()}
        # Per-call-site spec-substitution temps, filled by _scan_temps.
        self.call_binds: Dict[int, Dict[str, Tuple[str, str]]] = {}
        # Per-call-site point-havoc frame: [(value temp, field map)] when the
        # callee only writes the heap through `this` (see _writes_only_this).
        self.call_frame: Dict[int, List[Tuple[str, str]]] = {}

    # ------------------------------------------------------------------ util
    def shared_list(self) -> List[str]:
        """All shared store items: scalar globals plus heap maps/alloc sets."""
        return list(self.ti.globals.keys()) + sorted(self.heap_types.keys())

    def store_items(self, scope: str) -> List[str]:
        """All store variables visible in a scope: shared items + that scope's
        locals + result."""
        items = self.shared_list()
        locs = self.ti.scope_locals(scope)
        for l in locs:
            items.append(l)
        if "result" not in items and "result" not in locs:
            items.append("result")
        return items

    def _display_names(self, f: A.FnDecl) -> frozenset:
        """Source-level names shown in a counterexample for function `f`: the
        globals plus `f`'s own locals (which include its parameters and `this`).
        `result` is the callee return channel and is present in the encoding of
        any function that calls another, but is only meaningful -- and only
        shown -- where `f` itself uses it (assigns it or names it in a spec)."""
        names = set(self.ti.globals.keys())
        names.update(self.ti.scope_locals(f"fn:{f.name}").keys())
        if self._uses_result(f):
            names.add("result")
        return frozenset(names)

    @staticmethod
    def _uses_result(f: A.FnDecl) -> bool:
        def in_expr(e) -> bool:
            if e is None:
                return False
            if isinstance(e, A.Result):
                return True
            for c in vars(e).values():
                if isinstance(c, A.Expr) and in_expr(c):
                    return True
                if isinstance(c, list) and any(
                        isinstance(x, A.Expr) and in_expr(x) for x in c):
                    return True
            return False

        for attr in ("requires", "ensures", "relies", "guarantees"):
            if in_expr(getattr(f.spec, attr, None)):
                return True

        def in_stmts(stmts) -> bool:
            for s in stmts:
                if isinstance(s, A.Assign) and s.lhs == "result":
                    return True
                if isinstance(s, A.Call_) and getattr(s, "assign_to", None) == "result":
                    return True
                if isinstance(s, A.If) and (in_stmts(s.then_body) or in_stmts(s.else_body)):
                    return True
                if isinstance(s, A.While) and in_stmts(s.body):
                    return True
            return False

        return in_stmts(f.body)

    def btype(self, name: str, scope: str) -> str:
        if name in self.ti.globals:
            return self.ti.globals[name]
        if name in self.heap_types:
            return self.heap_types[name]
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

    def declare_vars(self, scope: str, temps: Optional[List[Tuple[str, str]]] = None) -> None:
        items = self.store_items(scope)
        for n in items:
            bt = self.btype(n, scope)
            for snap in ("v", "o", "pre", "py", "ce"):
                self.em.line(f"var {snap}_{n}: {bt};")
        self.em.line("var tid: int;")
        self.em.line("var eff: int;")
        self.em.line("var mv: int;")
        self.em.line("var le_save: int;")
        for name, bt in (temps or []):
            self.em.line(f"var {name}: {bt};")

    def globals_list(self) -> List[str]:
        return self.shared_list()

    def snapshot(self, snap: str, scope: str, only_globals: bool = False) -> None:
        items = self.shared_list() if only_globals else self.store_items(scope)
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

    def _emit_mover(self, gname: str, access: str, scope: str, span: Span,
                    what: str, partial: bool = False) -> None:
        """Emit the access-legality assert and compose the running effect.

        `partial` marks a blocking action (acquire): M-action's totality side
        condition (e <= L implies A total) forbids ascribing it an effect in
        the left-mover region, so its exact mover is bumped to the least
        effect not <= L before composing (a blocking action placed after the
        commit point could block forever)."""
        self.em.line(f"mv := {self._mover_expr(gname, access, scope)};")
        self.em.assert_(
            f"mv != {E_CODE}", span,
            f"{what} of {gname!r} is not permitted here by its mover specification "
            f"(possible data race)",
        )
        if partial:
            self.em.line("mv := bumpEff(mv);  // blocking action: ascribed effect not <= L")
        self.em.line("eff := seqEff(eff, mv);")
        self.em.assert_(
            f"eff != {E_CODE}", span,
            f"{what} of {gname!r} breaks reducibility here: this reducible sequence "
            f"is not of the form R*[N]L* (insert a yield to split it)"
            + ("; a blocking action may not follow the commit point"
               if partial else ""),
        )

    # ---------------------------------------------------------- field movers
    def _field_clauses(self, cls: str, fld: str, access: str) -> List[A.MoverClause]:
        vd = self.prog.find_field(cls, fld)
        if vd is None:
            return []
        out = []
        for cl in vd.clauses:
            if cl.index is not None:
                continue
            if cl.access is None or cl.access == access:
                out.append(cl)
        return out

    def _field_mover_static(self, cls: str, fld: str, access: str) -> Effect:
        return join_all(cl.mover for cl in self._field_clauses(cls, fld, access))

    def _field_mover_expr(self, cls: str, fld: str, access: str, scope: str,
                          recv: str) -> str:
        """Mover selection for an access to `recv`.`fld`: the clause guards are
        evaluated with `this` bound to the (pre-captured) receiver, bare field
        names against the post-action heap, and `\\old` against the pre-action
        `pre_` snapshot."""
        clauses = self._field_clauses(cls, fld, access)
        cur = self.cur_map(scope); cur["this"] = recv
        old = self.snap_map(scope, "pre"); old["this"] = recv
        return self._mover_ite(clauses, cur, old)

    def _emit_field_mover(self, cls: str, fld: str, access: str, scope: str,
                          recv: str, span: Span, what: str,
                          partial: bool = False) -> None:
        self.em.line(f"mv := {self._field_mover_expr(cls, fld, access, scope, recv)};")
        self.em.assert_(
            f"mv != {E_CODE}", span,
            f"{what} of field {fld!r} is not permitted here by its mover "
            f"specification (possible data race)",
        )
        if partial:
            self.em.line("mv := bumpEff(mv);  // blocking action: ascribed effect not <= L")
        self.em.line("eff := seqEff(eff, mv);")
        self.em.assert_(
            f"eff != {E_CODE}", span,
            f"{what} of field {fld!r} breaks reducibility here: this reducible "
            f"sequence is not of the form R*[N]L* (insert a yield to split it)"
            + ("; a blocking action may not follow the commit point"
               if partial else ""),
        )

    def _capture_recv(self, base: A.Expr, cls: str, scope: str, span: Span,
                      what: str) -> str:
        """Copy the receiver into its per-class temp and check it non-null."""
        cur = self.cur_map(scope)
        recv = f"recv_{cls}"
        self.em.line(f"{recv} := {self.tr.tr(base, cur, cur)};")
        self.em.assert_(f"{recv} != {null_name(cls)}", span,
                        f"the receiver of this {what} may be null")
        return recv

    # ---------------------------------------------------------- array movers
    def _elem_clauses(self, at: str, access: str) -> List[A.MoverClause]:
        cls, fld = self.arr_field[at]
        vd = self.prog.find_field(cls, fld)
        if vd is None:
            return []
        return [cl for cl in vd.clauses if cl.index is not None
                and (cl.access is None or cl.access == access)]

    def _elem_mover_static(self, at: str, access: str) -> Effect:
        return join_all(cl.mover for cl in self._elem_clauses(at, access))

    def _elem_mover_ite(self, clauses: List[A.MoverClause], idx: str,
                        tid: str = "tid") -> str:
        """Element clause guards are state-independent (tid + index only), so
        they translate against a minimal environment with each clause's index
        variable bound to `idx`."""
        expr = str(E_CODE)
        for cl in reversed(clauses):
            env = {cl.index: idx, "tid": tid}
            cond = self.tr.tr(cl.cond, env, env)
            expr = f"(if {cond} then {EFF_CODE[cl.mover.name]} else {expr})"
        return expr

    def _emit_elem_access(self, at: str, access: str, base: A.Expr,
                          index: A.Expr, scope: str, span: Span,
                          what: str) -> Tuple[str, str]:
        """Common prologue of an element access: capture the array reference
        and index, check null and bounds, snapshot, and check the element
        mover.  Returns (array temp, index temp)."""
        cur = self.cur_map(scope)
        aref = f"recv_{at}"
        self.em.line(f"{aref} := {self.tr.tr(base, cur, cur)};")
        self.em.assert_(f"{aref} != {null_name(at)}", span,
                        f"the array of this {what} may be null")
        self.em.line(f"aidx := {self.tr.tr(index, cur, cur)};")
        self.em.assert_(
            f"0 <= aidx && aidx < v_{arr_len_name(at)}[{aref}]", span,
            f"the index of this {what} may be out of bounds")
        self.snapshot("pre", scope, only_globals=True)
        clauses = self._elem_clauses(at, access)
        self.em.line(f"mv := {self._elem_mover_ite(clauses, 'aidx')};")
        self.em.assert_(
            f"mv != {E_CODE}", span,
            f"{what} is not permitted here by the element mover specification "
            f"(possible data race)")
        self.em.line("eff := seqEff(eff, mv);")
        self.em.assert_(
            f"eff != {E_CODE}", span,
            f"{what} breaks reducibility here: this reducible sequence is not "
            f"of the form R*[N]L* (insert a yield to split it)")
        return aref, "aidx"

    # ------------------------------------------------------------ temp scan
    def _scan_temps(self, body: List[A.Stmt], scope: str) -> List[Tuple[str, str]]:
        """Collect the auxiliary locals a procedure body needs: per-class
        receiver and allocation temps, and per-call-site spec-substitution
        temps for method receivers and arguments."""
        decls: Dict[str, str] = {}
        counter = [0]

        def field_kind_cls(kind_val: str) -> str:
            return kind_val.split(".", 1)[0]

        def scan_cond(c: A.Cond) -> None:
            c = _unwrap_not(c)
            if isinstance(c, A.CasCond) and c.target_expr is not None:
                cls = self.ti.expr_class[id(c.target_expr)]
                decls[f"recv_{cls}"] = cls

        def scan(stmts: List[A.Stmt]) -> None:
            for st in stmts:
                if isinstance(st, A.Assign):
                    kind, gv = self.ti.assign_kind[id(st)]
                    if kind == "fieldread":
                        cls = field_kind_cls(gv)
                        decls[f"recv_{cls}"] = cls
                    elif kind == "new":
                        decls[f"newref_{gv}"] = gv
                    elif kind == "elemread":
                        decls[f"recv_{gv}"] = gv
                        decls["aidx"] = "int"
                    elif kind == "newarray":
                        at = self.ti.expr_class[id(st.rhs)]
                        decls[f"newref_{at}"] = at
                elif isinstance(st, A.ArrayWrite):
                    kind, at = self.ti.assign_kind[id(st)]
                    decls[f"recv_{at}"] = at
                    decls["aidx"] = "int"
                elif isinstance(st, A.FieldWrite):
                    kind, gv = self.ti.assign_kind[id(st)]
                    cls = field_kind_cls(gv)
                    decls[f"recv_{cls}"] = cls
                elif isinstance(st, A.UnstableRead) and st.source_expr is not None:
                    cls = self.ti.expr_class[id(st.source_expr)]
                    decls[f"recv_{cls}"] = cls
                elif isinstance(st, (A.Acquire, A.Release)) and st.lock_expr is not None:
                    cls = self.ti.expr_class[id(st.lock_expr)]
                    decls[f"recv_{cls}"] = cls
                elif isinstance(st, A.Call_):
                    target = self.ti.call_target.get(id(st), st.name)
                    callee = self.prog.find_func(target)
                    if callee is None:
                        continue
                    k = counter[0]; counter[0] += 1
                    binds: Dict[str, Tuple[str, str]] = {}
                    if st.receiver is not None:
                        binds["this"] = (f"cs{k}_this", callee.cls)
                    for i, p in enumerate(callee.params):
                        binds[p.name] = (f"cs{k}_a{i}", type_to_boogie(p.type))
                    for name, bt in binds.values():
                        decls[name] = bt
                    self.call_binds[id(st)] = binds
                    if callee.cls is not None and self._writes_only_this(callee):
                        frame = []
                        written = set(self._callee_shared_writes(callee))
                        for j, fld in enumerate(sorted(self.ti.classes[callee.cls])):
                            fm = fmap_name(callee.cls, fld)
                            if fm in written:
                                tmp = f"cs{k}_hv{j}"
                                decls[tmp] = self.ti.classes[callee.cls][fld]
                                frame.append((tmp, fm))
                        self.call_frame[id(st)] = frame
                elif isinstance(st, A.If):
                    scan_cond(st.cond)
                    scan(st.then_body); scan(st.else_body)
                elif isinstance(st, A.While):
                    scan_cond(st.cond)
                    scan(st.body)

        scan(body)
        return sorted(decls.items())

    # -------------------------------------------------------------- programs
    def lower(self) -> Emitter:
        for f in self.prog.funcs:
            self.em.scope_names = self._display_names(f)
            if f.is_atomic:
                self.gen_atomic_fn(f)
            else:
                self.gen_nonatomic_fn(f)
        # the validity/state/rely procedures are not tied to a user function
        # body, so leave their obligations unrestricted.
        self.em.scope_names = None
        self.gen_validity()
        self.gen_state_checks()
        self.gen_rely_checks()

        # Prepend the prelude, per-class type declarations, and any
        # uninterpreted-function declarations.
        header = [prelude()]
        for c in self.prog.classes:
            header.append(f"// class {c.name}")
            header.append(f"type {c.name};")
            header.append(f"const unique {null_name(c.name)}: {c.name};")
        for at in self.ti.arrays:
            header.append(f"// array type {at}")
            header.append(f"type {at};")
            header.append(f"const unique {null_name(at)}: {at};")
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
        self.declare_vars(scope, self._scan_temps(f.body, scope))
        self.em.line("assume tid > 0;")
        self._assume_receiver(f, scope)
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
        self.declare_vars(scope, self._scan_temps(f.body, scope))
        self.em.line("assume tid > 0;")
        self._assume_receiver(f, scope)
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

    def _assume_receiver(self, f: A.FnDecl, scope: str) -> None:
        """A method runs on an allocated, non-null receiver; ref-typed
        parameters are null or allocated."""
        if f.cls is not None:
            self.em.line(f"assume v_this != {null_name(f.cls)} && "
                         f"v_{alloc_name(f.cls)}[v_this];")
        for p in f.params:
            pt = type_to_boogie(p.type)
            if pt in self.ti.classes:
                self.em.line(f"assume v_{p.name} == {null_name(pt)} || "
                             f"v_{alloc_name(pt)}[v_{p.name}];")

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
        if isinstance(s, A.FieldWrite):
            self.emit_field_write(s, ctx)
            return
        if isinstance(s, A.ArrayWrite):
            self.emit_array_write(s, ctx)
            return
        if isinstance(s, A.UnstableRead):
            if s.source_expr is not None:
                cls = self.ti.expr_class[id(s.source_expr)]
                self._capture_recv(s.source_expr.base, cls, scope, s.span,
                                   "unstable read")
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
            self._assign_local(s.lhs, f"v_{gvar}")
        elif kind == "fieldread":
            cls, fld = gvar.split(".", 1)
            recv = self._capture_recv(s.rhs.base, cls, scope, s.span, "field read")
            self.snapshot("pre", scope, only_globals=True)
            self._emit_field_mover(cls, fld, "read", scope, recv, s.span, "read")
            self._assign_local(s.lhs, f"v_{fmap_name(cls, fld)}[{recv}]")
        elif kind == "new":
            self.emit_new(s, gvar, ctx)
        elif kind == "elemread":
            at = gvar
            aref, aidx = self._emit_elem_access(
                at, "read", s.rhs.base, s.rhs.index, scope, s.span, "element read")
            self._assign_local(s.lhs, f"v_{arr_elems_name(at)}[{aref}][{aidx}]")
        elif kind == "newarray":
            self.emit_new_array(s, ctx)
        else:  # local computation: both-mover, no effect change
            self._assign_local(s.lhs, rhs_ast=s.rhs, cur=cur)

    def _assign_local(self, lhs: str, rhs_boogie: Optional[str] = None,
                      rhs_ast: "A.Expr" = None,
                      cur: Optional[Dict[str, str]] = None) -> None:
        """Assign to a thread-local via `havoc; assume` rather than a direct
        `:=`.  This is logically identical to the assignment (havoc then pin to
        the exact value), but makes the local a named model constant so it shows
        up in a counterexample store -- Boogie prunes locals defined by a plain
        deterministic `:=` from its models.

        For an AST right-hand side we first snapshot the pre-value into `pre_lhs`
        and translate against it, so a self-referential RHS (`t = t + n`) reads
        the old value rather than the just-havocked one.  (Doing this
        unconditionally keeps the assignment sound regardless of the RHS shape.)
        """
        if rhs_ast is not None:
            self.em.line(f"pre_{lhs} := v_{lhs};")
            cur2 = dict(cur); cur2[lhs] = f"pre_{lhs}"
            rhs_boogie = self.tr.tr(rhs_ast, cur2, cur2)
        self.em.line(f"havoc v_{lhs};")
        self.em.line(f"assume v_{lhs} == {rhs_boogie};")

    def emit_new(self, s: A.Assign, cls: str, ctx: "_Ctx") -> None:
        """`x = new C`: pick an unallocated non-null reference, mark it
        allocated, and reset its fields to their type defaults.  Allocation is
        invisible to other threads (the fresh reference is unreachable), so it
        is a both-mover with no spec check."""
        ref = f"newref_{cls}"
        am = alloc_name(cls)
        self.em.line(f"havoc {ref};")
        self.em.line(f"assume {ref} != {null_name(cls)} && !v_{am}[{ref}];")
        self.em.line(f"v_{am} := v_{am}[{ref} := true];")
        for fld, ft in self.ti.classes[cls].items():
            d = default_value(ft)
            if d is not None:
                fm = fmap_name(cls, fld)
                self.em.line(f"v_{fm} := v_{fm}[{ref} := {d}];")
            # types without a canonical default start unconstrained: the map
            # value at a never-allocated index was never pinned by anyone
        self._assign_local(s.lhs, ref)

    def emit_new_array(self, s: A.Assign, ctx: "_Ctx") -> None:
        """`x = new T[n]`: pick a fresh unallocated array reference and fix its
        length; the elements start unconstrained.  Like object allocation this
        is invisible to other threads (a both-mover with no spec check)."""
        scope = ctx.scope
        cur = self.cur_map(scope)
        at = self.ti.expr_class[id(s.rhs)]
        ref = f"newref_{at}"
        am = alloc_name(at)
        size = self.tr.tr(s.rhs.size, cur, cur)
        self.em.assert_(f"({size}) >= 0", s.span,
                        "the size of this array allocation may be negative")
        self.em.line(f"havoc {ref};")
        self.em.line(f"assume {ref} != {null_name(at)} && !v_{am}[{ref}];")
        self.em.line(f"v_{am} := v_{am}[{ref} := true];")
        lm = arr_len_name(at)
        self.em.line(f"v_{lm} := v_{lm}[{ref} := {size}];")
        self._assign_local(s.lhs, ref)

    def emit_array_write(self, s: A.ArrayWrite, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        kind, at = self.ti.assign_kind[id(s)]
        aref, aidx = self._emit_elem_access(
            at, "write", s.base, s.index, scope, s.span, "element write")
        em = arr_elems_name(at)
        val = self.tr.tr(s.rhs, cur, cur)
        self.em.line(f"v_{em} := v_{em}[{aref} := v_{em}[{aref}][{aidx} := {val}]];")

    def emit_acquire(self, s: A.Acquire, ctx: "_Ctx") -> None:
        scope = ctx.scope
        if s.lock_expr is not None:
            cls = self.ti.expr_class[id(s.lock_expr)]
            recv = self._capture_recv(s.lock_expr.base, cls, scope, s.span, "acquire")
            fm = fmap_name(cls, s.lock)
            self.snapshot("pre", scope, only_globals=True)
            self.em.line(f"assume pre_{fm}[{recv}] == 0;")
            self.em.line(f"v_{fm} := v_{fm}[{recv} := tid];")
            self._emit_field_mover(cls, s.lock, "write", scope, recv, s.span,
                                   "acquire", partial=True)
            return
        self.snapshot("pre", scope, only_globals=True)
        # acquire blocks unless the lock is free (guard: \old(m) == 0)
        self.em.line(f"assume pre_{s.lock} == 0;")
        self.em.line(f"v_{s.lock} := tid;")
        self._emit_mover(s.lock, "write", scope, s.span, "acquire", partial=True)

    def emit_release(self, s: A.Release, ctx: "_Ctx") -> None:
        scope = ctx.scope
        if s.lock_expr is not None:
            cls = self.ti.expr_class[id(s.lock_expr)]
            recv = self._capture_recv(s.lock_expr.base, cls, scope, s.span, "release")
            fm = fmap_name(cls, s.lock)
            self.snapshot("pre", scope, only_globals=True)
            self.em.line(f"v_{fm} := v_{fm}[{recv} := 0];")
            self._emit_field_mover(cls, s.lock, "write", scope, recv, s.span, "release")
            return
        self.snapshot("pre", scope, only_globals=True)
        self.em.line(f"v_{s.lock} := 0;")
        self._emit_mover(s.lock, "write", scope, s.span, "release")

    def emit_field_write(self, s: A.FieldWrite, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        kind, gvar = self.ti.assign_kind[id(s)]
        cls, fld = gvar.split(".", 1)
        recv = self._capture_recv(s.base, cls, scope, s.span, "field write")
        fm = fmap_name(cls, fld)
        self.snapshot("pre", scope, only_globals=True)
        self.em.line(f"v_{fm} := v_{fm}[{recv} := {self.tr.tr(s.rhs, cur, cur)}];")
        self._emit_field_mover(cls, fld, "write", scope, recv, s.span, "write")

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
        # interference: havoc shared state and assume the rely once; this
        # models R* because gen_rely_checks proves R reflexive and transitive
        self.snapshot("py", scope, only_globals=True)
        for g in self.shared_list():
            self.em.line(f"havoc v_{g};")
        for conj in self._builtin_rely("v", "py"):
            self.em.line(f"assume {conj};")
        self.em.line(
            f"assume {self.tr.tr(ctx.relies, cur, self.snap_map(scope, 'py'))};"
        )
        # start a new reducible sequence
        self.restore_seq_start(scope)
        self.em.line(f"eff := seqEff(eff, {Y_CODE});")

    def _builtin_rely(self, cur_snap: str, old_snap: str) -> List[str]:
        """Interference facts guaranteed by the semantics itself (not by user
        relies): other threads only ever allocate, so allocation sets grow,
        and array lengths are fixed at allocation."""
        out = []
        for cname in self.ti.classes:
            am = alloc_name(cname)
            out.append(f"(forall _o: {cname} :: {old_snap}_{am}[_o] ==> "
                       f"{cur_snap}_{am}[_o])")
        for at in self.ti.arrays:
            am = alloc_name(at)
            lm = arr_len_name(at)
            out.append(f"(forall _a: {at} :: {old_snap}_{am}[_a] ==> "
                       f"({cur_snap}_{am}[_a] && "
                       f"{cur_snap}_{lm}[_a] == {old_snap}_{lm}[_a]))")
        return out

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
        # downstream effect (over-approximation).
        iter_static = self._loop_iter_static(s, ctx)
        a2_static = self._cond_fail_static(s.cond)
        loop_static = seq(star(iter_static), a2_static)
        modified = self._loop_modified(s, ctx)
        self.em.line("// while loop (M-while); each iteration must be a right-mover-or-less")
        self.em.line("le_save := eff;")            # effect before the loop
        self.em.assert_(inv, s.span, "loop invariant may not hold on entry")
        for g in modified:
            self.em.line(f"havoc v_{g};")
        for l in self._loop_modified_locals(s, ctx):
            self.em.line(f"havoc v_{l};")
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
        if leq(loop_static, Effect.L):
            # M-while requires the ascribed loop effect e to satisfy
            # (M(A1,P);e1)*;M(A2,P) <= e and not (e <= L).  When the loop's
            # static effect lies in the left-mover region, ascribe the least
            # effect above it instead (Y,B -> R; L -> N) and compose *that*
            # downstream.  This is sound because the rule's effect antecedent
            # is an upper bound; the not-<=-L guard is needed because zero
            # iterations perform no action (a yield-only closure Y must not
            # reset the surrounding phase), and it is what keeps a loop out
            # of the post-commit region, where termination would be required.
            e_loop = bump_not_left(loop_static)
            self.em.line(f"eff := seqEff(le_save, {EFF_CODE[e_loop.name]});"
                         f"  // ascribed loop effect {e_loop.name} (M-while: e not <= L)")
        self.em.assert_(f"eff != {E_CODE}", s.span,
                        "loop breaks reducibility in its surrounding sequence "
                        "(a loop's effect may not be below a left-mover, so it "
                        "cannot be placed after the commit point)")

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
            if c.target_expr is not None:
                cls = self.ti.expr_class[id(c.target_expr)]
                recv = self._capture_recv(c.target_expr.base, cls, scope, c.span, "cas")
                fm = fmap_name(cls, c.target)
                self.snapshot("pre", scope, only_globals=True)
                self.em.line(f"assume pre_{fm}[{recv}] == {self.tr.tr(c.expected, cur, cur)};")
                self.em.line(f"v_{fm} := v_{fm}[{recv} := {self.tr.tr(c.new, cur, cur)}];")
                self._emit_field_mover(cls, c.target, "write", scope, recv, c.span,
                                       "successful cas")
                return
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
            if c.target_expr is not None:
                cls = self.ti.expr_class[id(c.target_expr)]
                return self._field_mover_static(cls, c.target, "write")
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
            if s.lock_expr is not None:
                cls = self.ti.expr_class[id(s.lock_expr)]
                mv = self._field_mover_static(cls, s.lock, "write")
            else:
                mv = self._mover_static(s.lock, "write")
            if isinstance(s, A.Acquire):
                # acquire may block: its ascribed effect must not be <= L
                # (M-action's totality side condition).
                mv = bump_not_left(mv)
            return mv
        if isinstance(s, A.FieldWrite):
            kind, gvar = self.ti.assign_kind[id(s)]
            cls, fld = gvar.split(".", 1)
            return self._field_mover_static(cls, fld, "write")
        if isinstance(s, A.ArrayWrite):
            kind, at = self.ti.assign_kind[id(s)]
            return self._elem_mover_static(at, "write")
        if isinstance(s, A.Assign):
            kind, gvar = self.ti.assign_kind[id(s)]
            if kind == "write":
                return self._mover_static(s.lhs, "write")
            if kind == "read":
                return self._mover_static(gvar, "read")
            if kind == "fieldread":
                cls, fld = gvar.split(".", 1)
                return self._field_mover_static(cls, fld, "read")
            if kind == "elemread":
                return self._elem_mover_static(gvar, "read")
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
            # the ascribed loop effect is never <= L (M-while side condition)
            return bump_not_left(seq(star(it), self._cond_fail_static(s.cond)))
        if isinstance(s, A.Call_):
            callee = self.prog.find_func(self.ti.call_target.get(id(s), s.name))
            if callee is not None and callee.is_atomic:
                return callee.spec.mover
            return Effect.R
        return Effect.B

    def _shared_writes(self, stmts: List[A.Stmt], mods: Set[str],
                       seen_fns: Set[str]) -> None:
        """Collect the shared store items (globals, field maps, alloc sets)
        that `stmts` may write, following calls transitively."""

        def cas_target(c: A.Cond) -> None:
            c = _unwrap_not(c)
            if isinstance(c, A.CasCond):
                if c.target_expr is not None:
                    cls = self.ti.expr_class[id(c.target_expr)]
                    mods.add(fmap_name(cls, c.target))
                else:
                    mods.add(c.target)

        for st in stmts:
            if isinstance(st, A.Assign):
                kind, gvar = self.ti.assign_kind[id(st)]
                if kind == "write":
                    mods.add(st.lhs)
                elif kind == "new":
                    mods.add(alloc_name(gvar))
                    for fld in self.ti.classes[gvar]:
                        mods.add(fmap_name(gvar, fld))
                elif kind == "newarray":
                    at = self.ti.expr_class[id(st.rhs)]
                    mods.add(alloc_name(at))
                    mods.add(arr_len_name(at))
            elif isinstance(st, A.FieldWrite):
                kind, gvar = self.ti.assign_kind[id(st)]
                cls, fld = gvar.split(".", 1)
                mods.add(fmap_name(cls, fld))
            elif isinstance(st, A.ArrayWrite):
                kind, at = self.ti.assign_kind[id(st)]
                mods.add(arr_elems_name(at))
            elif isinstance(st, (A.Acquire, A.Release)):
                if st.lock_expr is not None:
                    cls = self.ti.expr_class[id(st.lock_expr)]
                    mods.add(fmap_name(cls, st.lock))
                else:
                    mods.add(st.lock)
            elif isinstance(st, A.If):
                cas_target(st.cond)
                self._shared_writes(st.then_body, mods, seen_fns)
                self._shared_writes(st.else_body, mods, seen_fns)
            elif isinstance(st, A.While):
                cas_target(st.cond)
                self._shared_writes(st.body, mods, seen_fns)
            elif isinstance(st, A.Call_):
                target = self.ti.call_target.get(id(st), st.name)
                if target not in seen_fns:
                    seen_fns.add(target)
                    callee = self.prog.find_func(target)
                    if callee is not None:
                        self._shared_writes(callee.body, mods, seen_fns)

    def _loop_modified(self, s: A.While, ctx: "_Ctx") -> List[str]:
        mods: Set[str] = set()
        c = _unwrap_not(s.cond)
        if isinstance(c, A.CasCond):
            if c.target_expr is not None:
                mods.add(fmap_name(self.ti.expr_class[id(c.target_expr)], c.target))
            else:
                mods.add(c.target)
        self._shared_writes(s.body, mods, set())
        return [g for g in self.shared_list() if g in mods]

    def _loop_modified_locals(self, s: A.While, ctx: "_Ctx") -> List[str]:
        """Thread-locals the loop body may write.  These must be havocked on
        the loop's exit path too: otherwise the exit test A2 is evaluated over
        the locals' PRE-loop values, which can make the whole continuation
        vacuously unreachable (e.g. `i = 0; while (i < 3) {... i = i + 1;}`
        would `assume !(0 < 3)`, verifying anything that follows)."""
        out: Set[str] = set()

        def scan(stmts: List[A.Stmt]) -> None:
            for st in stmts:
                if isinstance(st, A.Assign) and st.lhs not in self.ti.globals:
                    out.add(st.lhs)
                elif isinstance(st, A.UnstableRead):
                    out.add(st.lhs)
                elif isinstance(st, A.Call_):
                    target = self.ti.call_target.get(id(st), st.name)
                    callee = self.prog.find_func(target)
                    if callee is not None:
                        out.update(self._callee_local_writes(callee))
                    if st.assign_to is not None:
                        out.add(st.assign_to)
                elif isinstance(st, A.If):
                    scan(st.then_body); scan(st.else_body)
                elif isinstance(st, A.While):
                    scan(st.body)

        scan(s.body)
        visible = set(self.store_items(ctx.scope))
        return sorted(n for n in out
                      if n in visible and n not in self.ti.globals
                      and n not in self.heap_types)

    # -------------------------------------------------------- function calls
    def emit_call(self, s: A.Call_, ctx: "_Ctx") -> None:
        scope = ctx.scope
        cur = self.cur_map(scope)
        target = self.ti.call_target.get(id(s), s.name)
        callee = self.prog.find_func(target)
        # Capture the receiver and argument values in temps: in the callee's
        # spec, `this` and parameter names denote these call-entry values
        # (parameters are immutable), so requires/ensures are translated with
        # them substituted in.
        binds = self.call_binds.get(id(s), {})
        for name, (tmp, _bt) in binds.items():
            if name == "this":
                self.em.line(f"{tmp} := {self.tr.tr(s.receiver, cur, cur)};")
                self.em.assert_(f"{tmp} != {null_name(callee.cls)}", s.span,
                                "the receiver of this method call may be null")
            else:
                idx = [p.name for p in callee.params].index(name)
                self.em.line(f"{tmp} := {self.tr.tr(s.args[idx], cur, cur)};")
        sub = {name: tmp for name, (tmp, _bt) in binds.items()}
        cur_b = {**cur, **sub}
        frame = self.call_frame.get(id(s))
        recv_tmp = sub.get("this")
        # snapshot call entry for the callee's \old
        self.snapshot("ce", scope)
        if callee.is_atomic:
            spec: A.AtomicSpec = callee.spec
            self.em.assert_(
                self.tr.tr(spec.requires, cur_b, cur_b), s.span,
                f"precondition of atomic {target}() may not hold at this call",
            )
            self._havoc_callee_effects(callee, scope, frame, recv_tmp)
            old_b = {**self.snap_map(scope, "ce"), **sub}
            self.em.line(f"assume {self.tr.tr(spec.ensures, cur_b, old_b)};")
            self.em.line(f"eff := seqEff(eff, {EFF_CODE[spec.mover.name]});")
            self.em.assert_(f"eff != {E_CODE}", s.span,
                            f"call to {target}() breaks reducibility here")
        else:
            spec: A.NonAtomicSpec = callee.spec
            # M-call-non-atomic: current reducible sequence must be trivial (S holds)
            self.em.assert_(
                self.tr.tr(spec.requires, cur_b, cur_b), s.span,
                f"precondition of {target}() may not hold at this call",
            )
            self._havoc_callee_effects(callee, scope, frame, recv_tmp)
            self.em.line(f"assume {self.tr.tr(spec.ensures, cur_b, cur_b)};")
            self.restore_seq_start(scope)
            self.em.line(f"eff := seqEff(eff, {R_CODE});")
            self.em.assert_(f"eff != {E_CODE}", s.span,
                            f"call to {target}() breaks reducibility here")
        if s.assign_to is not None and s.assign_to != "result":
            self._assign_local(s.assign_to, "v_result")

    def _writes_only_this(self, callee: A.FnDecl, seen: Optional[Set[str]] = None) -> bool:
        """True iff every heap write the callee performs (transitively) goes
        through the receiver `this` of its own class, and it allocates nothing.
        Such a callee can be framed precisely at a call site: only the
        receiver's entries in its class's field maps need havocking."""
        if seen is None:
            seen = {callee.name}

        def is_this(e: A.Expr) -> bool:
            return isinstance(e, A.Var) and e.name == "this"

        def ok(stmts: List[A.Stmt]) -> bool:
            for st in stmts:
                if isinstance(st, A.Assign):
                    kind, _ = self.ti.assign_kind[id(st)]
                    if kind in ("new", "newarray"):
                        return False
                elif isinstance(st, A.ArrayWrite):
                    return False
                elif isinstance(st, A.FieldWrite):
                    if not is_this(st.base):
                        return False
                elif isinstance(st, (A.Acquire, A.Release)):
                    if st.lock_expr is not None and not is_this(st.lock_expr.base):
                        return False
                elif isinstance(st, (A.If, A.While)):
                    c = _unwrap_not(st.cond)
                    if isinstance(c, A.CasCond) and c.target_expr is not None \
                            and not is_this(c.target_expr.base):
                        return False
                    bodies = ([st.then_body, st.else_body]
                              if isinstance(st, A.If) else [st.body])
                    if not all(ok(b) for b in bodies):
                        return False
                elif isinstance(st, A.Call_):
                    target = self.ti.call_target.get(id(st), st.name)
                    inner = self.prog.find_func(target)
                    if inner is None:
                        continue
                    if st.receiver is None:
                        # a plain function is fine only if it touches no heap
                        if any(g in self.heap_types
                               for g in self._callee_shared_writes(inner)):
                            return False
                    elif not is_this(st.receiver):
                        return False
                    elif target not in seen:
                        seen.add(target)
                        if not self._writes_only_this(inner, seen):
                            return False
            return True

        return ok(callee.body)

    def _havoc_callee_effects(self, callee: A.FnDecl, caller_scope: str,
                              frame: Optional[List[Tuple[str, str]]] = None,
                              recv_tmp: Optional[str] = None) -> None:
        # Havoc exactly the shared items the callee writes (transitively,
        # through nested calls) and the locals it assigns.  (Mover Logic omits
        # frame conditions, so callee ensures must pin what matters; we havoc
        # writes and let the ensures constrain them.)
        framed = {fm for _tmp, fm in (frame or [])}
        for g in self._callee_shared_writes(callee):
            if g in framed:
                continue
            self.em.line(f"havoc v_{g};")
        # a callee that writes the heap only through `this` disturbs exactly
        # the receiver's entries: havoc those points, not the whole maps
        for tmp, fm in (frame or []):
            self.em.line(f"havoc {tmp};")
            self.em.line(f"v_{fm} := v_{fm}[{recv_tmp} := {tmp}];")
        caller_items = set(self.store_items(caller_scope))
        param_names = {p.name for p in callee.params} | {"this"}
        for l in self._callee_local_writes(callee):
            # Only locals visible in the caller need havocking; the callee's
            # private working locals do not affect the caller's state.
            # Parameters are immutable, so they are never written.
            if l in caller_items and l not in param_names:
                self.em.line(f"havoc v_{l};")

    def _callee_shared_writes(self, callee: A.FnDecl) -> List[str]:
        out: Set[str] = set()
        self._shared_writes(callee.body, out, {callee.name})
        return [g for g in self.shared_list() if g in out]

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
        # Field specs.  Guards may only dereference `this` and may not mention
        # scalar globals, so cross-class and field/global pairs commute
        # structurally; the interesting cases are within one class -- two
        # accesses through possibly-aliasing receivers.
        for c in self.prog.classes:
            for xw in c.fields:
                for yv in c.fields:
                    self._field_validity3(c, xw, yv)
            fwritable = [fd for fd in c.fields
                         if self._field_clauses(c.name, fd.name, "write")]
            for xw in fwritable:
                self._field_validity_commute(1, c, xw)
                self._field_validity_commute(2, c, xw)
                self._field_validity_commute(4, c, xw)
        # Array element specs.  Element guards are state-independent (tid and
        # index only), so condition (3) holds trivially -- no write can change
        # the mover another thread computes.  Only the commute conditions on
        # two element writes (possibly to the same array and index) remain.
        for at in sorted(self.ti.arrays):
            if self._elem_clauses(at, "write"):
                self._elem_validity_commute(1, at)
                self._elem_validity_commute(2, at)
                self._elem_validity_commute(4, at)

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

    # ---- field-spec validity: two accesses through possibly-aliased receivers
    def _field_store_dicts(self) -> Dict[str, str]:
        return {g: f"s_{g}" for g in self.shared_list()}

    def _emit_field_validity_header(self, name: str, cls: str, vtypes: List[str]) -> None:
        self.em.line(f"procedure {{:entrypoint}} {name}()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var s_{g}: {bt};")
        self.em.line(f"var o1: {cls}; var o2: {cls};")
        for i, vt in enumerate(vtypes, 1):
            self.em.line(f"var v{i}: {vt};")
        self.em.line("var t: int; var u: int;")
        self.em.line("assume t > 0 && u > 0 && t != u;")
        self.em.line(f"assume o1 != {null_name(cls)} && o2 != {null_name(cls)};")

    def _field_validity_commute(self, num: int, c: A.ClassDecl, xw: A.VarDecl) -> None:
        """Conditions (1), (2), (4) for two writes to the same field X of class
        C through receivers o1 (thread t) and o2 (thread u), which may alias.
        For o1 != o2 the map updates commute structurally; for o1 == o2 the
        assertion forces the two writes to agree, exactly as in the scalar
        case."""
        cls = c.name
        X = xw.name
        fmX = fmap_name(cls, X)
        xty = self.ti.classes[cls][X]
        xwrite = self._field_clauses(cls, X, "write")
        sigma = self._field_store_dicts()

        upd1 = f"s_{fmX}[o1 := v1]"                 # sigma'  = sigma[o1.X := v1]
        upd12 = f"{upd1}[o2 := v2]"                 # sigma'' = sigma'[o2.X := v2]
        upd2 = f"s_{fmX}[o2 := v2]"
        upd21 = f"{upd2}[o1 := v1]"

        def m(tv: str, this: str, cur_map: str, old_map: str) -> str:
            cur = {**sigma, fmX: cur_map, "tid": tv, "this": this}
            old = {**sigma, fmX: old_map, "tid": tv, "this": this}
            return self._mover_ite(xwrite, cur, old)

        moverX_t = m("t", "o1", upd1, f"s_{fmX}")   # M(A1, t, sigma)
        if num == 1:
            h1 = f"leqEff({moverX_t}, {R_CODE})"
            h2 = f"leqEff({m('u', 'o2', upd12, upd1)}, {N_CODE})"   # M(A2,u,sigma')<=N
        elif num == 2:
            h1 = f"leqEff({moverX_t}, {N_CODE})"
            h2 = f"leqEff({m('u', 'o2', upd12, upd1)}, {L_CODE})"   # M(A2,u,sigma')<=L
        else:  # num == 4
            h1 = f"leqEff({moverX_t}, {N_CODE})"
            h2 = f"leqEff({m('u', 'o2', upd2, f's_{fmX}')}, {L_CODE})"  # M(A2,u,sigma)<=L

        self.em.blank()
        self.em.line(f"// validity({num}): writes to field {cls}.{X} by t (o1) "
                     f"and u (o2) commute")
        self._emit_field_validity_header(f"FValid{num}_{cls}_{X}", cls, [xty, xty])
        self.em.line(f"assume {h1};")
        self.em.line(f"assume {h2};")
        self.em.assert_(
            f"({upd12}[o1] == {upd21}[o1]) && ({upd12}[o2] == {upd21}[o2])",
            xw.span,
            f"invalid mover specification: a {self._cond_name(num)} to field "
            f"{X!r} by one thread and a write by another (possibly through an "
            f"aliased receiver) do not commute (validity condition {num} fails)",
        )
        self.em.dedent()
        self.em.line("}")

    def _elem_validity_commute(self, num: int, at: str) -> None:
        """Conditions (1), (2), (4) for two element writes to arrays of type
        `at`: A1 = <o1[i1] := v1> by t and A2 = <o2[i2] := v2> by u.  The
        writes commute structurally unless both the arrays and the indices
        alias, in which case the assertion forces the values to agree."""
        cls, fld = self.arr_field[at]
        ety = self.ti.arrays[at]
        em = arr_elems_name(at)
        wcl = self._elem_clauses(at, "write")

        def upd(m: str, o: str, i: str, v: str) -> str:
            return f"{m}[{o} := {m}[{o}][{i} := {v}]]"

        base = f"s_{em}"
        m1 = upd(base, "o1", "i1", "v1")           # after A1
        m12 = upd(m1, "o2", "i2", "v2")            # A1 then A2
        m2 = upd(base, "o2", "i2", "v2")           # after A2
        m21 = upd(m2, "o1", "i1", "v1")            # A2 then A1

        mover1 = self._elem_mover_ite(wcl, "i1", "t")
        mover2 = self._elem_mover_ite(wcl, "i2", "u")
        if num == 1:
            h1 = f"leqEff({mover1}, {R_CODE})"
            h2 = f"leqEff({mover2}, {N_CODE})"
        else:  # 2 and 4 coincide for state-independent element movers
            h1 = f"leqEff({mover1}, {N_CODE})"
            h2 = f"leqEff({mover2}, {L_CODE})"

        self.em.blank()
        self.em.line(f"// validity({num}): element writes to {cls}.{fld} arrays commute")
        self.em.line(f"procedure {{:entrypoint}} AValid{num}_{at}()")
        self.em.line("{")
        self.em.indent()
        self.em.line(f"var s_{em}: {self.heap_types[em]};")
        self.em.line(f"var o1: {at}; var o2: {at};")
        self.em.line("var i1: int; var i2: int;")
        self.em.line(f"var v1: {ety}; var v2: {ety};")
        self.em.line("var t: int; var u: int;")
        self.em.line("assume t > 0 && u > 0 && t != u;")
        self.em.line(f"assume {h1};")
        self.em.line(f"assume {h2};")
        vd = self.prog.find_field(cls, fld)
        self.em.assert_(
            f"({m12}[o1][i1] == {m21}[o1][i1]) && ({m12}[o2][i2] == {m21}[o2][i2])",
            vd.span if vd else None,
            f"invalid mover specification: two element writes to {fld!r} arrays "
            f"by different threads (possibly aliasing array and index) do not "
            f"commute (validity condition {num} fails)",
        )
        self.em.dedent()
        self.em.line("}")

    def _field_validity3(self, c: A.ClassDecl, xw: A.VarDecl, yv: A.VarDecl) -> None:
        """Condition (3) for fields: a write to o1.X by thread t must not
        change the mover thread u computes for an access to o2.Y (o1 and o2
        may alias)."""
        cls = c.name
        xw_write = [cl for cl in xw.clauses if cl.index is None
                    and cl.access in (None, "write")]
        if not xw_write:
            return
        fmX = fmap_name(cls, xw.name)
        xty = self.ti.classes[cls][xw.name]
        sigma = self._field_store_dicts()
        upd1 = f"s_{fmX}[o1 := v1]"

        def mover_of_y(access: str, fmX_val: str) -> str:
            clauses = [cl for cl in yv.clauses if cl.index is None
                       and cl.access in (None, access)]
            cur = {**sigma, fmX: fmX_val, "tid": "u", "this": "o2"}
            return self._mover_ite(clauses, cur, cur)

        # t's own write must be well-defined (!= E) for this step
        wcur = {**sigma, fmX: upd1, "tid": "t", "this": "o1"}
        wold = {**sigma, "tid": "t", "this": "o1"}
        wexpr = self._mover_ite(xw_write, wcur, wold)

        self.em.blank()
        self.em.line(f"// validity(3): a write to {cls}.{xw.name} by t keeps "
                     f"{cls}.{yv.name}'s mover for u")
        self._emit_field_validity_header(f"FValid3_{cls}_{xw.name}_{yv.name}", cls, [xty])
        self.em.line(f"assume {wexpr} != {E_CODE};")
        for access in ("read", "write"):
            y_before = mover_of_y(access, f"s_{fmX}")
            y_after = mover_of_y(access, upd1)
            self.em.assert_(
                f"({y_before}) == ({y_after})", yv.span,
                f"invalid mover specification: a write to field {xw.name!r} by "
                f"one thread can change the {access} mover of field {yv.name!r} "
                f"for another thread (validity condition 3 fails)",
            )
        self.em.dedent()
        self.em.line("}")

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

    def shared_types(self) -> List[Tuple[str, str]]:
        out = [(g, self.ti.globals[g]) for g in self.ti.globals]
        out.extend(sorted(self.heap_types.items()))
        return out

    def _reflexive_guarantee(self, f: A.FnDecl) -> None:
        spec: A.NonAtomicSpec = f.spec
        gl = self.shared_list()
        self.em.blank()
        self.em.line(f"// I => G for {f.name}()  (guarantee is reflexive)")
        self.em.line(f"procedure {{:entrypoint}} Reflexive_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var v_{g}: {bt};")
        self.em.line("var tid: int; assume tid > 0;")
        cur = {**{g: f"v_{g}" for g in gl}, "tid": "tid"}
        self.em.assert_(self.tr.tr(spec.guarantees, cur, cur), f.span,
                        f"guarantee of {f.name}() is not reflexive (I => G fails)")
        self.em.dedent()
        self.em.line("}")

    def _guarantee_implies_rely(self, ft: A.FnDecl, fu: A.FnDecl) -> None:
        gspec: A.NonAtomicSpec = ft.spec
        rspec: A.NonAtomicSpec = fu.spec
        gl = self.shared_list()
        self.em.blank()
        self.em.line(f"// G[{ft.name}] => R[{fu.name}] for distinct threads")
        self.em.line(f"procedure {{:entrypoint}} GR_{ft.name}_{fu.name}()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var v_{g}: {bt}; var o_{g}: {bt};")
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
        gl = self.shared_list()
        self.em.blank()
        self.em.line("// initial store establishes each thread precondition (M-state)")
        self.em.line("procedure {:entrypoint} Init_establishes()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var v_{g}: {bt};")
        self.em.line("var tid: int; assume tid > 0;")
        # the initial heap is empty: nothing is allocated yet
        for cname in self.ti.classes:
            self.em.line(f"assume (forall _o: {cname} :: !v_{alloc_name(cname)}[_o]);")
        for at in self.ti.arrays:
            self.em.line(f"assume (forall _a: {at} :: !v_{alloc_name(at)}[_a]);")
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
        gl = self.shared_list()
        self.em.blank()
        self.em.line(f"// R(s, s) for {f.name}()  (rely is reflexive)")
        self.em.line(f"procedure {{:entrypoint}} RelyRefl_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var a_{g}: {bt};")
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
        gl = self.shared_list()
        self.em.blank()
        self.em.line(f"// R;R => R for {f.name}()  (rely is transitive)")
        self.em.line(f"procedure {{:entrypoint}} RelyTrans_{f.name}()")
        self.em.line("{")
        self.em.indent()
        for g, bt in self.shared_types():
            self.em.line(f"var a_{g}: {bt}; var b_{g}: {bt}; var c_{g}: {bt};")
        self.em.line("var tid: int; assume tid > 0;")
        sa = {**{g: f"a_{g}" for g in gl}, "tid": "tid"}
        sb = {**{g: f"b_{g}" for g in gl}, "tid": "tid"}
        sc = {**{g: f"c_{g}" for g in gl}, "tid": "tid"}
        # interference steps also satisfy the built-in semantic facts
        # (allocation is monotone), so they may be assumed as hypotheses
        for conj in self._builtin_rely("b", "a") + self._builtin_rely("c", "b"):
            self.em.line(f"assume {conj};")
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
