"""Abstract syntax tree for the Mover Logic Language.

The AST mirrors the formal grammar of MLL (Figure "Mover Logic Language" in the
paper) with lightweight surface sugar (types, curly braces, named locals) added
for readability, exactly as the paper does in its examples.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional

from .diagnostics import Span
from .effects import Effect


# ===========================================================================
# Expressions  (used inside actions, conditions, and one-/two-store predicates)
# ===========================================================================

class Expr:
    span: Span


@dataclass
class Num(Expr):
    value: int
    span: Span


@dataclass
class BoolLit(Expr):
    value: bool
    span: Span


@dataclass
class NilLit(Expr):
    span: Span


@dataclass
class NoneLit(Expr):
    span: Span


@dataclass
class Var(Expr):
    name: str
    span: Span


@dataclass
class Tid(Expr):
    """The identifier of the currently executing thread."""
    span: Span


@dataclass
class Result(Expr):
    """The function result, passed via the thread-local `result` variable."""
    span: Span


@dataclass
class Old(Expr):
    """`\\old(e)`: the value of e in the pre-store of the current context.

    In a statement judgement this is the store at the start of the current
    reducible sequence; in a rely/guarantee it is the pre-store of an
    interference step; in a mover-spec clause it is the pre-store of the access.
    """
    inner: Expr
    span: Span


@dataclass
class Unary(Expr):
    op: str            # ! -
    operand: Expr
    span: Span


@dataclass
class Binary(Expr):
    op: str            # && || ==> <==> == != < <= > >= + - * / % ::
    left: Expr
    right: Expr
    span: Span


@dataclass
class Call(Expr):
    """Uninterpreted/among-prelude function application: head, tail, Some, even."""
    name: str
    args: List[Expr]
    span: Span


@dataclass
class Index(Expr):
    """Array indexing a[i]."""
    base: Expr
    index: Expr
    span: Span


@dataclass
class Quant(Expr):
    """forall/exists  v in [lo, hi) . body"""
    kind: str          # "forall" | "exists"
    var: str
    lo: Expr
    hi: Expr
    body: Expr
    span: Span


# ===========================================================================
# Conditional actions   (b = A1 <> A2)  used by `if` and `while`
# ===========================================================================

class Cond:
    span: Span


@dataclass
class BoolCond(Cond):
    """A pure predicate test: success = assume(e), failure = assume(!e)."""
    expr: Expr
    span: Span


@dataclass
class CasCond(Cond):
    """cas(x, old_val, new_val): success writes x, failure is identity."""
    target: str
    expected: Expr
    new: Expr
    span: Span


@dataclass
class NotCond(Cond):
    """Negation of a conditional action: swaps the success/failure actions."""
    inner: Cond
    span: Span


# ===========================================================================
# Statements
# ===========================================================================

class Stmt:
    span: Span


@dataclass
class Skip(Stmt):
    span: Span


@dataclass
class Yield(Stmt):
    span: Span


@dataclass
class Wrong(Stmt):
    span: Span


@dataclass
class Assert(Stmt):
    """assert e   ==   if (e) skip else wrong"""
    expr: Expr
    span: Span


@dataclass
class Assign(Stmt):
    """lhs = rhs.

    Classified during type-checking into a global write, a global read, or a
    purely local computation, which determines the mover of the action.
    """
    lhs: str
    rhs: Expr
    span: Span


@dataclass
class UnstableRead(Stmt):
    """r = *x : an unstable read of global x into local r (any value)."""
    lhs: str
    source: str
    span: Span


@dataclass
class Acquire(Stmt):
    lock: str
    span: Span


@dataclass
class Release(Stmt):
    lock: str
    span: Span


@dataclass
class If(Stmt):
    cond: Cond
    then_body: List[Stmt]
    else_body: List[Stmt]
    span: Span


@dataclass
class While(Stmt):
    cond: Cond
    body: List[Stmt]
    invariant: Optional[Expr]     # optional explicit loop invariant
    span: Span


@dataclass
class Call_(Stmt):
    name: str
    span: Span


# ===========================================================================
# Declarations
# ===========================================================================

@dataclass
class MoverClause:
    access: Optional[str]         # "read" | "write" | None (both)
    index: Optional[str]          # element-access variable name for a[i] clauses
    mover: Effect
    cond: Expr                    # the guard P (may be BoolLit(True))
    span: Span


@dataclass
class VarDecl:
    name: str
    type: "TypeExpr"
    is_lock: bool
    clauses: List[MoverClause]
    span: Span


@dataclass
class AtomicSpec:
    mover: Effect                 # declared atomic effect (default N)
    requires: Expr
    ensures: Expr


@dataclass
class NonAtomicSpec:
    relies: Expr
    guarantees: Expr
    requires: Expr
    ensures: Expr


@dataclass
class FnDecl:
    name: str
    spec: object                  # AtomicSpec | NonAtomicSpec
    body: List[Stmt]
    span: Span

    @property
    def is_atomic(self) -> bool:
        return isinstance(self.spec, AtomicSpec)


@dataclass
class ThreadDecl:
    body: List[Stmt]
    span: Span


@dataclass
class InitDecl:
    """`init P;` -- the predicate satisfied by the program's initial store."""
    pred: Expr
    span: Span


# ===========================================================================
# Types
# ===========================================================================

@dataclass
class TypeExpr:
    name: str                     # "int" | "bool" | "lock_t" | "value" | "Optional" | "List"
    args: List["TypeExpr"] = field(default_factory=list)
    is_array: bool = False

    def __str__(self) -> str:
        base = self.name
        if self.args:
            base += "[" + ", ".join(str(a) for a in self.args) + "]"
        if self.is_array:
            base += "[]"
        return base


@dataclass
class Program:
    decls: List[object]           # VarDecl | FnDecl | ThreadDecl

    @property
    def vars(self) -> List[VarDecl]:
        return [d for d in self.decls if isinstance(d, VarDecl)]

    @property
    def funcs(self) -> List[FnDecl]:
        return [d for d in self.decls if isinstance(d, FnDecl)]

    @property
    def threads(self) -> List[ThreadDecl]:
        return [d for d in self.decls if isinstance(d, ThreadDecl)]

    @property
    def init(self) -> Optional["InitDecl"]:
        for d in self.decls:
            if isinstance(d, InitDecl):
                return d
        return None

    def find_var(self, name: str) -> Optional[VarDecl]:
        for d in self.vars:
            if d.name == name:
                return d
        return None

    def find_func(self, name: str) -> Optional[FnDecl]:
        for d in self.funcs:
            if d.name == name:
                return d
        return None
