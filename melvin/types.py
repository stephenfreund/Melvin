"""Type checking and action classification for Mover Logic programs.

Responsibilities:

  * Build the table of global variables and locks with their Boogie types.
  * Infer the types of thread-local variables (any identifier that is not a
    declared global is a thread-local, per the paper's `r_tid` convention).
  * Classify each assignment as a *global write*, a *global read*, or a purely
    *local computation*.  This classification determines the mover of the
    action and is required for a well-defined mover specification: the paper
    requires that the right-hand side of a global write only mentions locals,
    and that a global read has the form `local = global`.
  * Reject obvious errors: assigning through a lock, recursion in atomic
    functions, calls to unknown functions, multiple globals in one action.

The result is a `TypeInfo` consumed by the verification-condition generator.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from . import ast_nodes as A
from .diagnostics import TypeError_, Span

# Boogie-level type names.
INT = "int"
BOOL = "bool"
VALUE = "Value"       # generic uninterpreted value (used for list payloads)
LISTT = "List"
OPTION = "Optional"


class TVar:
    """A unification variable for inferring local/return types."""

    _n = 0

    def __init__(self):
        TVar._n += 1
        self.id = TVar._n
        self.ref: Optional[object] = None  # str type name or another TVar

    def find(self):
        t = self
        while isinstance(t, TVar) and t.ref is not None:
            t = t.ref
        return t


def resolve(t) -> object:
    if isinstance(t, TVar):
        r = t.find()
        return r if not isinstance(r, TVar) else r
    return t


def unify(a, b, span: Span, ctx: str = "") -> None:
    a, b = _prune(a), _prune(b)
    if isinstance(a, TVar):
        a.ref = b
        return
    if isinstance(b, TVar):
        b.ref = a
        return
    if a != b:
        raise TypeError_(f"type mismatch: {a} vs {b}" + (f" ({ctx})" if ctx else ""), span)


def _prune(t):
    if isinstance(t, TVar):
        return t.find()
    return t


def type_to_boogie(t: A.TypeExpr) -> str:
    """Map a surface type to a Boogie type name."""
    name = t.name
    if name == "lock_t":
        base = INT
    elif name == "int":
        base = INT
    elif name == "bool":
        base = BOOL
    elif name == "value":
        base = VALUE
    elif name == "Optional":
        base = OPTION
    elif name == "List":
        base = LISTT
    else:
        base = name
    if t.is_array:
        return f"[int]{base}"
    return base


@dataclass
class TypeInfo:
    globals: Dict[str, str]                       # name -> boogie type
    lock_names: Set[str]
    array_names: Set[str]
    func_return: Dict[str, str]                   # function -> result boogie type
    locals: Dict[str, Dict[str, str]]             # scope-key -> {local -> boogie type}
    assign_kind: Dict[int, Tuple[str, Optional[str]]]  # id(Assign) -> (kind, gvar)
    call_graph: Dict[str, Set[str]] = field(default_factory=dict)
    classes: Dict[str, Dict[str, str]] = field(default_factory=dict)  # C -> {field -> boogie type}
    field_locks: Set[Tuple[str, str]] = field(default_factory=set)    # (C, field) lock fields
    expr_class: Dict[int, str] = field(default_factory=dict)          # id(expr) -> class/array type
    call_target: Dict[int, str] = field(default_factory=dict)         # id(Call_) -> resolved fn name
    arrays: Dict[str, str] = field(default_factory=dict)              # array type -> elem boogie type
    array_fields: Dict[Tuple[str, str], str] = field(default_factory=dict)  # (C, f) -> array type

    def scope_locals(self, key: str) -> Dict[str, str]:
        return self.locals.get(key, {})


# Names a class may not take (they are built-in Boogie/prelude types).
RESERVED_TYPE_NAMES = {"int", "bool", "lock_t", "value", "List", "Optional", "Value"}


class TypeChecker:
    def __init__(self, prog: A.Program):
        self.prog = prog
        self.globals: Dict[str, str] = {}
        self.lock_names: Set[str] = set()
        self.array_names: Set[str] = set()
        self.func_return: Dict[str, str] = {}
        self.locals: Dict[str, Dict[str, str]] = {}
        self.assign_kind: Dict[int, Tuple[str, Optional[str]]] = {}
        self.call_graph: Dict[str, Set[str]] = {}
        self.classes: Dict[str, Dict[str, str]] = {}
        self.field_locks: Set[Tuple[str, str]] = set()
        self.expr_class: Dict[int, str] = {}
        self.call_target: Dict[int, str] = {}
        self.null_sites: List[Tuple[A.NullLit, TVar]] = []
        self.arrays: Dict[str, str] = {}
        self.array_fields: Dict[Tuple[str, str], str] = {}
        self.newarray_sites: List[Tuple[A.NewArray, TVar]] = []

    # -- entry --------------------------------------------------------------
    def check(self) -> TypeInfo:
        self._collect_classes()
        self._collect_globals()
        self._desugar_call_assigns()
        for f in self.prog.funcs:
            self.func_return[f.name] = INT  # default; result is int unless used otherwise
        self._check_specs_and_bodies()
        self._check_atomic_non_recursive()
        self._resolve_nulls()
        self._resolve_newarrays()
        return TypeInfo(
            globals=self.globals,
            lock_names=self.lock_names,
            array_names=self.array_names,
            func_return=self.func_return,
            locals=self.locals,
            assign_kind=self.assign_kind,
            call_graph=self.call_graph,
            classes=self.classes,
            field_locks=self.field_locks,
            expr_class=self.expr_class,
            call_target=self.call_target,
            arrays=self.arrays,
            array_fields=self.array_fields,
        )

    def _collect_classes(self) -> None:
        for c in self.prog.classes:
            if c.name in RESERVED_TYPE_NAMES:
                raise TypeError_(f"{c.name!r} is a reserved type name", c.span)
            if c.name in self.classes:
                raise TypeError_(f"duplicate class {c.name!r}", c.span)
            fields: Dict[str, str] = {}
            for fld in c.fields:
                if fld.name in fields:
                    raise TypeError_(
                        f"duplicate field {fld.name!r} in class {c.name!r}", fld.span)
                if fld.type.is_array:
                    # an array field introduces its own array reference type;
                    # its [i] clauses give the element access spec
                    if fld.type.name not in ("int", "bool"):
                        raise TypeError_(
                            f"array fields must have scalar elements "
                            f"(int[] or bool[]), not {fld.type.name}[]", fld.span)
                    at = f"Arr_{c.name}_{fld.name}"
                    self.arrays[at] = fld.type.name
                    self.array_fields[(c.name, fld.name)] = at
                    fields[fld.name] = at
                else:
                    fields[fld.name] = self._surface_type(fld.type, fld.span)
                if fld.is_lock:
                    self.field_locks.add((c.name, fld.name))
            self.classes[c.name] = fields

    def _surface_type(self, t: A.TypeExpr, span: Span) -> str:
        base = type_to_boogie(t)
        core = t.name
        if core not in ("int", "bool", "lock_t", "value", "Optional", "List") \
                and core not in self.classes \
                and self.prog.find_class(core) is None:
            raise TypeError_(f"unknown type {core!r}", span)
        return base

    def _collect_globals(self) -> None:
        for v in self.prog.vars:
            if v.name in self.globals:
                raise TypeError_(f"duplicate global {v.name!r}", v.span)
            self.globals[v.name] = self._surface_type(v.type, v.span)
            if v.is_lock:
                self.lock_names.add(v.name)
            if v.type.is_array:
                self.array_names.add(v.name)

    # -- desugaring ----------------------------------------------------------
    def _desugar_call_assigns(self) -> None:
        """Rewrite `x = f(args);` and `x = e.m(args);` into Call_ statements
        with `assign_to`, so all calls flow through one code path."""
        fn_names = {f.name for f in self.prog.funcs if f.cls is None}

        def rewrite(stmts: List[A.Stmt]) -> None:
            for i, s in enumerate(stmts):
                if isinstance(s, A.Assign):
                    r = s.rhs
                    if isinstance(r, A.MCall):
                        stmts[i] = A.Call_(r.name, s.span, args=list(r.args),
                                           receiver=r.receiver, assign_to=s.lhs)
                    elif isinstance(r, A.Call) and r.name in fn_names:
                        stmts[i] = A.Call_(r.name, s.span, args=list(r.args),
                                           assign_to=s.lhs)
                elif isinstance(s, A.If):
                    rewrite(s.then_body); rewrite(s.else_body)
                elif isinstance(s, A.While):
                    rewrite(s.body)

        for f in self.prog.funcs:
            rewrite(f.body)
        for th in self.prog.threads:
            rewrite(th.body)

    # -- specs + bodies -----------------------------------------------------
    def _check_specs_and_bodies(self) -> None:
        # mover-clause conditions are two-store predicates over globals + tid.
        for v in self.prog.vars:
            env = _Env(self, scope=None)
            for cl in v.clauses:
                self._infer(cl.cond, BOOL, env)

        # the init predicate is a one-store predicate over the globals
        if self.prog.init is not None:
            self._infer(self.prog.init.pred, BOOL, _Env(self, scope=None))

        # field mover-clause conditions: over this, this's fields, and tid only.
        # Element ([i]) clauses of array fields are state-independent: they may
        # mention only tid and the index variable.
        for c in self.prog.classes:
            for fld in c.fields:
                for cl in fld.clauses:
                    if cl.index is not None:
                        if (c.name, fld.name) not in self.array_fields:
                            raise TypeError_(
                                f"[{cl.index}] element clauses are only allowed "
                                f"on array fields", cl.span)
                        env = _Env(self, scope=None)
                        env.push_bound(cl.index, INT)
                        self._infer(cl.cond, BOOL, env)
                        env.pop_bound(cl.index)
                    else:
                        env = _Env(self, scope=None, this_cls=c.name)
                        self._infer(cl.cond, BOOL, env)

        for f in self.prog.funcs:
            scope = f"fn:{f.name}"
            self.locals[scope] = {}
            if f.cls is not None:
                self.locals[scope]["this"] = f.cls
            for p in f.params:
                if p.name in self.locals[scope]:
                    raise TypeError_(f"duplicate parameter {p.name!r}", p.span)
                if p.name in self.globals:
                    raise TypeError_(
                        f"parameter {p.name!r} shadows a global variable", p.span)
                self.locals[scope][p.name] = self._surface_type(p.type, p.span)
            env = _Env(self, scope=scope, func=f)
            self._check_fn_spec(f, env)
            self.call_graph.setdefault(f.name, set())
            self._check_block(f.body, env)
            self._finalize_locals(scope)

        for i, th in enumerate(self.prog.threads):
            scope = f"thread:{i}"
            self.locals[scope] = {}
            env = _Env(self, scope=scope, func=None)
            self._check_block(th.body, env)
            self._finalize_locals(scope)

    def _check_fn_spec(self, f: A.FnDecl, env: "_Env") -> None:
        s = f.spec
        if isinstance(s, A.AtomicSpec):
            self._infer(s.requires, BOOL, env)
            self._infer(s.ensures, BOOL, env)
        else:
            self._infer(s.relies, BOOL, env)
            self._infer(s.guarantees, BOOL, env)
            self._infer(s.requires, BOOL, env)
            self._infer(s.ensures, BOOL, env)

    def _finalize_locals(self, scope: str) -> None:
        for name, t in list(self.locals[scope].items()):
            r = _prune(t)
            self.locals[scope][name] = r if isinstance(r, str) else INT  # default unresolved -> int

    # -- statements ---------------------------------------------------------
    def _check_block(self, body: List[A.Stmt], env: "_Env") -> None:
        for s in body:
            self._check_stmt(s, env)

    def _check_stmt(self, s: A.Stmt, env: "_Env") -> None:
        if isinstance(s, (A.Skip, A.Yield, A.Wrong)):
            return
        if isinstance(s, A.Assert):
            self._infer(s.expr, BOOL, env)
            return
        if isinstance(s, A.Acquire) or isinstance(s, A.Release):
            if s.lock_expr is not None:
                cls, fname = self._check_field_target(s.lock_expr, env, "lock")
                if (cls, fname) not in self.field_locks:
                    raise TypeError_(
                        f"{fname!r} is not a lock field of class {cls!r}", s.span)
                return
            lk = s.lock
            if lk not in self.lock_names:
                raise TypeError_(f"{lk!r} is not a declared lock", s.span)
            return
        if isinstance(s, A.Assign):
            self._check_assign(s, env)
            return
        if isinstance(s, A.FieldWrite):
            self._check_field_write(s, env)
            return
        if isinstance(s, A.ArrayWrite):
            bt = _prune(self._infer_expr(s.base, env))
            if not (isinstance(bt, str) and bt in self.arrays):
                raise TypeError_(
                    "the target of an element write must be a heap array "
                    "reference", s.span)
            self._require_local_expr(s.base, env, "the array of an element write")
            self._require_local_expr(s.index, env, "an array index")
            self._require_local_expr(s.rhs, env, "the right-hand side of an element write")
            self._infer(s.index, INT, env)
            self._infer(s.rhs, self.arrays[bt], env)
            self.expr_class[id(s)] = bt
            self.assign_kind[id(s)] = ("elemwrite", bt)
            return
        if isinstance(s, A.UnstableRead):
            if s.source_expr is not None:
                cls, fname = self._check_field_target(s.source_expr, env, "unstable read")
                unify(env.local_type(s.lhs, s.span), self.classes[cls][fname],
                      s.span, "unstable read")
                self.assign_kind[id(s)] = ("fieldread", f"{cls}.{fname}")
                return
            if s.source not in self.globals:
                raise TypeError_(f"unstable read source {s.source!r} is not a global", s.span)
            gt = self.globals[s.source]
            env.local_type(s.lhs, s.span)
            unify(env.local_type(s.lhs, s.span), gt, s.span, "unstable read")
            self.assign_kind[id(s)] = ("read", s.source)
            return
        if isinstance(s, A.If):
            self._check_cond(s.cond, env)
            self._check_block(s.then_body, env)
            self._check_block(s.else_body, env)
            return
        if isinstance(s, A.While):
            self._check_cond(s.cond, env)
            if s.invariant is not None:
                self._infer(s.invariant, BOOL, env)
            self._check_block(s.body, env)
            return
        if isinstance(s, A.Call_):
            self._check_call(s, env)
            return
        raise TypeError_(f"cannot type-check statement {type(s).__name__}", s.span)

    def _check_call(self, s: A.Call_, env: "_Env") -> None:
        if s.receiver is not None:
            self._require_local_expr(s.receiver, env, "the receiver of a method call")
            rc = _prune(self._infer_expr(s.receiver, env))
            if not isinstance(rc, str) or rc not in self.classes:
                raise TypeError_(
                    "cannot determine the class of this method-call receiver",
                    s.receiver.span)
            target = f"{rc}.{s.name}"
        else:
            target = s.name
        f = self.prog.find_func(target)
        if f is None:
            what = "method" if s.receiver is not None else "function"
            raise TypeError_(f"call to unknown {what} {target!r}", s.span)
        if f.cls is not None and s.receiver is None:
            raise TypeError_(
                f"method {f.name!r} must be called on a receiver (use this.{s.name}(...))",
                s.span)
        if len(s.args) != len(f.params):
            raise TypeError_(
                f"{target}() takes {len(f.params)} argument(s) but got {len(s.args)}",
                s.span)
        for a, p in zip(s.args, f.params):
            self._require_local_expr(a, env, "a call argument")
            self._infer(a, self._surface_type(p.type, p.span), env)
        if s.assign_to is not None and s.assign_to != "result":
            if s.assign_to in self.globals:
                raise TypeError_(
                    "cannot assign a call result directly to a global; "
                    "assign it to a local first", s.span)
            unify(env.local_type(s.assign_to, s.span), self.func_return[target],
                  s.span, "call result")
        self.call_target[id(s)] = target
        if env.func is not None:
            self.call_graph.setdefault(env.func.name, set()).add(target)

    def _check_field_target(self, e: A.Expr, env: "_Env", what: str) -> Tuple[str, str]:
        """Type-check a FieldAccess used as an action target; return (class, field)."""
        assert isinstance(e, A.FieldAccess)
        self._require_local_expr(e.base, env, f"the receiver of a {what}")
        self._infer_expr(e, env)          # types the access, records expr_class
        return self.expr_class[id(e)], e.field

    def _check_field_write(self, s: A.FieldWrite, env: "_Env") -> None:
        self._require_local_expr(s.base, env, "the receiver of a field write")
        bt = _prune(self._infer_expr(s.base, env))
        if not isinstance(bt, str) or bt not in self.classes:
            raise TypeError_("cannot determine the class of this receiver", s.base.span)
        if s.field not in self.classes[bt]:
            raise TypeError_(f"class {bt!r} has no field {s.field!r}", s.span)
        if (bt, s.field) in self.field_locks:
            raise TypeError_(
                f"cannot assign directly to lock field {s.field!r}; use acquire/release",
                s.span)
        self._require_local_expr(s.rhs, env, "the right-hand side of a field write")
        if isinstance(s.rhs, (A.New, A.MCall)):
            raise TypeError_(
                "allocate or call into a local first, then write the local to the field",
                s.rhs.span)
        self._infer(s.rhs, self.classes[bt][s.field], env)
        self.assign_kind[id(s)] = ("fieldwrite", f"{bt}.{s.field}")

    def _require_local_expr(self, e: A.Expr, env: "_Env", what: str) -> None:
        """Enforce the one-shared-access-per-action rule: `e` may not read
        globals or object fields."""
        gs = self._globals_in(e)
        if gs:
            raise TypeError_(
                f"{what} may only reference thread-local variables (found global "
                f"{sorted(gs)[0]!r}); read it into a local first", e.span)
        fa = self._field_reads_in(e)
        if fa:
            raise TypeError_(
                f"{what} may only reference thread-local variables (found field "
                f"access .{fa[0].field}); read it into a local first", e.span)

    def _check_assign(self, s: A.Assign, env: "_Env") -> None:
        lhs = s.lhs
        if lhs == "this":
            raise TypeError_("cannot assign to 'this'", s.span)
        if env.func is not None and any(p.name == lhs for p in env.func.params):
            raise TypeError_(f"cannot assign to parameter {lhs!r} (parameters "
                             f"are immutable)", s.span)
        globals_in_rhs = self._globals_in(s.rhs)
        field_reads = self._field_reads_in(s.rhs)
        if lhs in self.lock_names:
            raise TypeError_(f"cannot assign directly to lock {lhs!r}; use acquire/release", s.span)
        # allocation: local = new C
        if isinstance(s.rhs, A.New):
            if s.rhs.cls not in self.classes:
                raise TypeError_(f"unknown class {s.rhs.cls!r}", s.rhs.span)
            if lhs in self.globals:
                raise TypeError_(
                    "cannot allocate directly into a global; assign new to a "
                    "local first", s.span)
            unify(env.local_type(lhs, s.span), s.rhs.cls, s.span, "allocation")
            self.expr_class[id(s.rhs)] = s.rhs.cls
            self.assign_kind[id(s)] = ("new", s.rhs.cls)
            return
        # array allocation: local = new T[n]
        if isinstance(s.rhs, A.NewArray):
            if lhs in self.globals:
                raise TypeError_(
                    "cannot allocate directly into a global; assign new to a "
                    "local first", s.span)
            self._require_local_expr(s.rhs.size, env, "an array allocation size")
            self._infer(s.rhs.size, INT, env)
            lt = env.local_type(lhs, s.span)
            tv = TVar()
            unify(lt, tv, s.span, "array allocation")
            self.newarray_sites.append((s.rhs, tv))
            self.assign_kind[id(s)] = ("newarray", None)
            return
        if lhs in self.globals:
            # global write: rhs must mention only locals (paper requirement)
            if globals_in_rhs or field_reads:
                raise TypeError_(
                    f"the right-hand side of a write to global {lhs!r} may only "
                    f"reference thread-local variables; read shared state into "
                    f"a local first",
                    s.span,
                )
            self._infer(s.rhs, self.globals[lhs], env)
            self.assign_kind[id(s)] = ("write", lhs)
            return
        # field read: local = e.f  (e local-only)
        if isinstance(s.rhs, A.FieldAccess) and lhs != "result":
            cls, fname = self._check_field_target(s.rhs, env, "field read")
            unify(env.local_type(lhs, s.span), self.classes[cls][fname],
                  s.span, "field read")
            self.assign_kind[id(s)] = ("fieldread", f"{cls}.{fname}")
            return
        # element read: local = a[i]  (a, i local-only; heap arrays only)
        if isinstance(s.rhs, A.Index) and lhs != "result":
            bt = _prune(self._infer_expr(s.rhs.base, env))
            if isinstance(bt, str) and bt in self.arrays:
                self._require_local_expr(s.rhs.base, env, "the array of an element read")
                self._require_local_expr(s.rhs.index, env, "an array index")
                self._infer(s.rhs.index, INT, env)
                unify(env.local_type(lhs, s.span), self.arrays[bt],
                      s.span, "element read")
                self.expr_class[id(s.rhs)] = bt
                self.assign_kind[id(s)] = ("elemread", bt)
                return
        # lhs is a local
        if lhs == "result":
            if globals_in_rhs or field_reads:
                # `result = <shared>` would be a shared read with no mover
                # check: reject it like any other compound shared read
                raise TypeError_(
                    "the right-hand side of an assignment to result may only "
                    "reference thread-local variables; read shared state into "
                    "a local first", s.span)
            fn = env.func
            rt = self.func_return[fn.name] if fn else INT
            self._infer(s.rhs, rt, env)
            self.assign_kind[id(s)] = ("local", None)
            return
        if len(globals_in_rhs) == 1 and isinstance(s.rhs, A.Var):
            # global read: local = global
            g = s.rhs.name
            unify(env.local_type(lhs, s.span), self.globals[g], s.span, "read")
            self.assign_kind[id(s)] = ("read", g)
            return
        if globals_in_rhs or field_reads:
            raise TypeError_(
                f"a shared read must have the form `local = global` or "
                f"`local = expr.field`; decompose this expression into simple reads",
                s.span,
            )
        # pure local computation
        lt = env.local_type(lhs, s.span)
        self._infer(s.rhs, lt, env)
        self.assign_kind[id(s)] = ("local", None)

    def _check_cond(self, c: A.Cond, env: "_Env") -> None:
        if isinstance(c, A.BoolCond):
            self._infer(c.expr, BOOL, env)
        elif isinstance(c, A.NotCond):
            self._check_cond(c.inner, env)
        elif isinstance(c, A.CasCond):
            if c.target_expr is not None:
                cls, fname = self._check_field_target(c.target_expr, env, "cas")
                ft = self.classes[cls][fname]
                self._require_local_expr(c.expected, env, "a cas operand")
                self._require_local_expr(c.new, env, "a cas operand")
                self._infer(c.expected, ft, env)
                self._infer(c.new, ft, env)
                return
            if c.target not in self.globals:
                raise TypeError_(f"cas target {c.target!r} is not a global", c.span)
            gt = self.globals[c.target]
            self._infer(c.expected, gt, env)
            self._infer(c.new, gt, env)
        else:
            raise TypeError_("unknown conditional action", c.span)

    # -- helpers ------------------------------------------------------------
    def _globals_in(self, e: A.Expr) -> Set[str]:
        found: Set[str] = set()

        def walk(x: A.Expr):
            if isinstance(x, A.Var) and x.name in self.globals:
                found.add(x.name)
            for child in _children(x):
                walk(child)

        walk(e)
        return found

    def _field_reads_in(self, e: A.Expr) -> List[A.FieldAccess]:
        found: List[A.FieldAccess] = []

        def walk(x: A.Expr):
            if isinstance(x, A.FieldAccess):
                found.append(x)
                return                     # nested accesses reported via the outermost
            for child in _children(x):
                walk(child)

        walk(e)
        return found

    def _resolve_nulls(self) -> None:
        for e, tv in self.null_sites:
            r = _prune(tv)
            if isinstance(r, str) and (r in self.classes or r in self.arrays):
                self.expr_class[id(e)] = r
            else:
                raise TypeError_(
                    "cannot determine the class of this 'null' from context",
                    e.span)

    def _resolve_newarrays(self) -> None:
        for e, tv in self.newarray_sites:
            r = _prune(tv)
            if not (isinstance(r, str) and r in self.arrays):
                raise TypeError_(
                    "cannot determine which array field this allocation is for "
                    "(store it into an array field or a typed local first)",
                    e.span)
            if self.arrays[r] != e.elem:
                raise TypeError_(
                    f"array element type mismatch: allocating {e.elem}[] for a "
                    f"{self.arrays[r]}[] field", e.span)
            self.expr_class[id(e)] = r

    def _check_atomic_non_recursive(self) -> None:
        # M-def-atomic requires atomic functions to be non-recursive.
        def reaches(start: str, target: str, seen: Set[str]) -> bool:
            for callee in self.call_graph.get(start, set()):
                if callee == target:
                    return True
                if callee not in seen:
                    seen.add(callee)
                    if reaches(callee, target, seen):
                        return True
            return False

        for f in self.prog.funcs:
            if f.is_atomic and reaches(f.name, f.name, set()):
                raise TypeError_(f"atomic function {f.name!r} must not be recursive", f.span)

    # -- expression inference ----------------------------------------------
    def _infer(self, e: A.Expr, expected, env: "_Env") -> object:
        t = self._infer_expr(e, env)
        if expected is not None:
            unify(t, expected, e.span, "expression")
        return t

    def _infer_expr(self, e: A.Expr, env: "_Env") -> object:
        if isinstance(e, A.Num):
            return INT
        if isinstance(e, A.BoolLit):
            return BOOL
        if isinstance(e, A.NilLit):
            return LISTT
        if isinstance(e, A.NoneLit):
            return OPTION
        if isinstance(e, A.NullLit):
            tv = TVar()
            self.null_sites.append((e, tv))
            return tv
        if isinstance(e, (A.New, A.NewArray)):
            raise TypeError_(
                "'new' may only appear as the entire right-hand side of an "
                "assignment to a local", e.span)
        if isinstance(e, A.MCall):
            raise TypeError_(
                "a method call may only appear as a statement or as the entire "
                "right-hand side of an assignment", e.span)
        if isinstance(e, A.FieldAccess):
            if env.scope is None and not (isinstance(e.base, A.Var) and e.base.name == "this"):
                raise TypeError_(
                    "mover specifications may only dereference 'this'", e.span)
            bt = _prune(self._infer_expr(e.base, env))
            if not isinstance(bt, str) or bt not in self.classes:
                raise TypeError_(
                    f"cannot determine the class of the receiver of .{e.field} "
                    f"(assign the receiver from `new`, a parameter, or a typed "
                    f"field first)", e.span)
            if e.field not in self.classes[bt]:
                raise TypeError_(f"class {bt!r} has no field {e.field!r}", e.span)
            self.expr_class[id(e)] = bt
            return self.classes[bt][e.field]
        if isinstance(e, A.Tid):
            return INT
        if isinstance(e, A.Result):
            fn = env.func
            return self.func_return[fn.name] if fn else INT
        if isinstance(e, A.Old):
            return self._infer_expr(e.inner, env)
        if isinstance(e, A.Var):
            if e.name in self.globals:
                if env.this_cls is not None:
                    raise TypeError_(
                        f"field mover specifications may only mention this, "
                        f"this's fields, and tid (found global {e.name!r})", e.span)
                return self.globals[e.name]
            return env.local_type(e.name, e.span)
        if isinstance(e, A.Unary):
            ot = self._infer_expr(e.operand, env)
            if e.op == "!":
                unify(ot, BOOL, e.span); return BOOL
            unify(ot, INT, e.span); return INT
        if isinstance(e, A.Binary):
            return self._infer_binary(e, env)
        if isinstance(e, A.Index):
            it = self._infer_expr(e.index, env)
            unify(it, INT, e.span)
            # heap array indexing: base resolves to an array reference type
            bt = _prune(self._infer_expr(e.base, env))
            if isinstance(bt, str) and bt in self.arrays:
                self.expr_class[id(e)] = bt
                return self.arrays[bt]
            # legacy value-semantics arrays (top-level globals of type T[])
            return INT
        if isinstance(e, A.Call):
            return self._infer_call(e, env)
        if isinstance(e, A.Quant):
            if e.cls is not None:
                if "." in e.cls:
                    cname, fname = e.cls.split(".", 1)
                    at = self.array_fields.get((cname, fname))
                    if at is None:
                        raise TypeError_(
                            f"{e.cls!r} is not an array field", e.span)
                    env.push_bound(e.var, at)
                elif e.cls == "int":
                    env.push_bound(e.var, INT)
                elif e.cls in self.classes:
                    env.push_bound(e.var, e.cls)
                else:
                    raise TypeError_(f"unknown class {e.cls!r} in quantifier", e.span)
            else:
                unify(self._infer_expr(e.lo, env), INT, e.span)
                unify(self._infer_expr(e.hi, env), INT, e.span)
                env.push_bound(e.var, INT)
            unify(self._infer_expr(e.body, env), BOOL, e.span)
            env.pop_bound(e.var)
            return BOOL
        raise TypeError_(f"cannot infer type of {type(e).__name__}", e.span)

    def _infer_binary(self, e: A.Binary, env: "_Env") -> object:
        op = e.op
        lt = self._infer_expr(e.left, env)
        rt = self._infer_expr(e.right, env)
        if op in ("&&", "||", "==>", "<==>"):
            unify(lt, BOOL, e.span); unify(rt, BOOL, e.span); return BOOL
        if op in ("+", "-", "*", "/", "%"):
            unify(lt, INT, e.span); unify(rt, INT, e.span); return INT
        if op in ("<", "<=", ">", ">="):
            unify(lt, INT, e.span); unify(rt, INT, e.span); return BOOL
        if op in ("==", "!="):
            unify(lt, rt, e.span, "equality"); return BOOL
        if op == "::":
            # elem :: list -> list ;  keep list payload uniform
            unify(rt, LISTT, e.span); return LISTT
        raise TypeError_(f"unknown operator {op!r}", e.span)

    def _infer_call(self, e: A.Call, env: "_Env") -> object:
        name = e.name
        if name == "length":
            if len(e.args) != 1:
                raise TypeError_("length() takes one array argument", e.span)
            at = _prune(self._infer_expr(e.args[0], env))
            if not isinstance(at, str) or at not in self.arrays:
                raise TypeError_("length() expects a heap array reference", e.span)
            self.expr_class[id(e)] = at
            return INT
        args = [self._infer_expr(a, env) for a in e.args]
        if name == "head":
            unify(args[0], LISTT, e.span); return INT
        if name == "tail":
            unify(args[0], LISTT, e.span); return LISTT
        if name == "Some":
            unify(args[0], INT, e.span); return OPTION
        if name == "even":
            unify(args[0], INT, e.span); return BOOL
        # unknown uninterpreted predicate/function: treat as bool over ints
        for a in args:
            unify(a, INT, e.span)
        return BOOL


class _Env:
    def __init__(self, tc: TypeChecker, scope: Optional[str],
                 func: Optional[A.FnDecl] = None, this_cls: Optional[str] = None):
        self.tc = tc
        self.scope = scope
        self.func = func
        self.this_cls = this_cls       # set inside a field mover clause
        self.bound: Dict[str, object] = {}

    def local_type(self, name: str, span: Span) -> object:
        if name in self.bound:
            return self.bound[name]
        if name == "this":
            if self.this_cls is not None:
                return self.this_cls
            if self.scope is not None and "this" in self.tc.locals[self.scope]:
                return self.tc.locals[self.scope]["this"]
            raise TypeError_("'this' may only be used inside a method or a "
                             "field mover specification", span)
        if self.scope is None:
            if self.this_cls is not None:
                # field mover-clause context
                raise TypeError_(
                    f"identifier {name!r} is not allowed here; field mover "
                    f"specifications may only mention this, this's fields, and tid",
                    span)
            # global mover-clause context: only globals + tid allowed
            raise TypeError_(
                f"identifier {name!r} is not a global; mover specifications may "
                f"only mention globals and tid", span)
        table = self.tc.locals[self.scope]
        if name not in table:
            table[name] = TVar()
        return table[name]

    def push_bound(self, name: str, t: object) -> None:
        self.bound[name] = t

    def pop_bound(self, name: str) -> None:
        self.bound.pop(name, None)


def _children(e: A.Expr) -> List[A.Expr]:
    if isinstance(e, A.Old):
        return [e.inner]
    if isinstance(e, A.Unary):
        return [e.operand]
    if isinstance(e, A.Binary):
        return [e.left, e.right]
    if isinstance(e, A.Call):
        return list(e.args)
    if isinstance(e, A.Index):
        return [e.base, e.index]
    if isinstance(e, A.FieldAccess):
        return [e.base]
    if isinstance(e, A.NewArray):
        return [e.size]
    if isinstance(e, A.MCall):
        return [e.receiver] + list(e.args)
    if isinstance(e, A.Quant):
        return ([e.lo, e.hi, e.body] if e.cls is None else [e.body])
    return []


def check_types(prog: A.Program) -> TypeInfo:
    return TypeChecker(prog).check()
