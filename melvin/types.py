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

    def scope_locals(self, key: str) -> Dict[str, str]:
        return self.locals.get(key, {})


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

    # -- entry --------------------------------------------------------------
    def check(self) -> TypeInfo:
        self._collect_globals()
        for f in self.prog.funcs:
            self.func_return[f.name] = INT  # default; result is int unless used otherwise
        self._check_specs_and_bodies()
        self._check_atomic_non_recursive()
        return TypeInfo(
            globals=self.globals,
            lock_names=self.lock_names,
            array_names=self.array_names,
            func_return=self.func_return,
            locals=self.locals,
            assign_kind=self.assign_kind,
            call_graph=self.call_graph,
        )

    def _collect_globals(self) -> None:
        for v in self.prog.vars:
            if v.name in self.globals:
                raise TypeError_(f"duplicate global {v.name!r}", v.span)
            self.globals[v.name] = type_to_boogie(v.type)
            if v.is_lock:
                self.lock_names.add(v.name)
            if v.type.is_array:
                self.array_names.add(v.name)

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

        for f in self.prog.funcs:
            scope = f"fn:{f.name}"
            self.locals[scope] = {}
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
            lk = s.lock
            if lk not in self.lock_names:
                raise TypeError_(f"{lk!r} is not a declared lock", s.span)
            return
        if isinstance(s, A.Assign):
            self._check_assign(s, env)
            return
        if isinstance(s, A.UnstableRead):
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
            if self.prog.find_func(s.name) is None:
                raise TypeError_(f"call to unknown function {s.name!r}", s.span)
            if env.func is not None:
                self.call_graph.setdefault(env.func.name, set()).add(s.name)
            return
        raise TypeError_(f"cannot type-check statement {type(s).__name__}", s.span)

    def _check_assign(self, s: A.Assign, env: "_Env") -> None:
        lhs = s.lhs
        globals_in_rhs = self._globals_in(s.rhs)
        if lhs in self.lock_names:
            raise TypeError_(f"cannot assign directly to lock {lhs!r}; use acquire/release", s.span)
        if lhs in self.globals:
            # global write: rhs must mention only locals (paper requirement)
            if globals_in_rhs:
                raise TypeError_(
                    f"the right-hand side of a write to global {lhs!r} may only "
                    f"reference thread-local variables (found global "
                    f"{sorted(globals_in_rhs)[0]!r}); read it into a local first",
                    s.span,
                )
            self._infer(s.rhs, self.globals[lhs], env)
            self.assign_kind[id(s)] = ("write", lhs)
            return
        # lhs is a local
        if lhs == "result":
            if globals_in_rhs:
                # `result = <global>` would be a shared read with no mover
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
        if globals_in_rhs:
            raise TypeError_(
                f"a global read must have the form `local = global`; "
                f"decompose this expression into simple reads",
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
        if isinstance(e, A.Tid):
            return INT
        if isinstance(e, A.Result):
            fn = env.func
            return self.func_return[fn.name] if fn else INT
        if isinstance(e, A.Old):
            return self._infer_expr(e.inner, env)
        if isinstance(e, A.Var):
            if e.name in self.globals:
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
            # base is an array; result is element type (approximate as int/value)
            if isinstance(e.base, A.Var) and e.base.name in self.array_names:
                return INT
            self._infer_expr(e.base, env)
            return INT
        if isinstance(e, A.Call):
            return self._infer_call(e, env)
        if isinstance(e, A.Quant):
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
    def __init__(self, tc: TypeChecker, scope: Optional[str], func: Optional[A.FnDecl] = None):
        self.tc = tc
        self.scope = scope
        self.func = func
        self.bound: Dict[str, object] = {}

    def local_type(self, name: str, span: Span) -> object:
        if name in self.bound:
            return self.bound[name]
        if self.scope is None:
            # mover-clause context: only globals + tid allowed
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
    if isinstance(e, A.Quant):
        return [e.lo, e.hi, e.body]
    return []


def check_types(prog: A.Program) -> TypeInfo:
    return TypeChecker(prog).check()
