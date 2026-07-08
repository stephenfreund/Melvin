"""Recursive-descent parser for the Mover Logic Language.

Grammar (informal):

    program     := decl*
    decl        := var_decl | lock_decl | class_decl | fn_decl | thread_decl
    var_decl    := 'var' type IDENT mover_clause* ';'
    lock_decl   := 'lock' IDENT mover_clause* ';'
    class_decl  := 'class' IDENT '{' (var_decl | lock_decl | fn_decl)* '}'
    mover_clause:= ('[' IDENT ']')? ('read'|'write')? MOVER ('if' pred)?
    fn_decl     := fn_spec IDENT '(' params? ')' block
    params      := type IDENT (',' type IDENT)*
    fn_spec     := 'atomic' MOVER? 'requires' pred 'ensures' pred
                 | 'relies' pred 'guarantees' pred 'requires' pred 'ensures' pred
    thread_decl := 'thread' block
    block       := '{' stmt* '}'
    stmt        := 'skip' ';' | 'yield' ';' | 'wrong' ';'
                 | 'assert' pred ';'
                 | 'acquire' '(' lvalue ')' ';' | 'release' '(' lvalue ')' ';'
                 | 'if' '(' cond ')' block ('else' block)?
                 | 'while' '(' cond ')' ('invariant' pred)? block
                 | postfix ';'                         (call: f(a) / e.m(a))
                 | IDENT '=' postfix '(' args ')' ';'  (call with result bind)
                 | IDENT '=' '*' lvalue ';'            (unstable read)
                 | IDENT '=' 'new' IDENT ';'           (allocation)
                 | lvalue '=' expr ';'                 (assignment / field write)
    lvalue      := IDENT | postfix '.' IDENT
    cond        := '!' cond | 'cas' '(' lvalue ',' expr ',' expr ')' | expr
    pred, expr  := standard precedence climbing (see below);
                   postfix adds '.' field selection and 'e.m(args)' calls;
                   quantifiers: forall/exists v in [lo, hi) . p   (int range)
                                forall/exists v : C . p           (references)
"""

from __future__ import annotations

from typing import List, Optional

from . import ast_nodes as A
from .diagnostics import ParseError, Span
from .effects import Effect
from .lexer import Token, lex

MOVER_KW = {
    "both-mover": Effect.B,
    "right-mover": Effect.R,
    "left-mover": Effect.L,
    "non-mover": Effect.N,
}


class Parser:
    def __init__(self, tokens: List[Token]):
        self.toks = tokens
        self.p = 0

    # -- token helpers ------------------------------------------------------
    @property
    def cur(self) -> Token:
        return self.toks[self.p]

    def at(self, text: str) -> bool:
        return self.cur.text == text and self.cur.kind in ("kw", "op")

    def at_kind(self, kind: str) -> bool:
        return self.cur.kind == kind

    def advance(self) -> Token:
        t = self.toks[self.p]
        if t.kind != "eof":
            self.p += 1
        return t

    def expect(self, text: str) -> Token:
        if not self.at(text):
            raise ParseError(f"expected {text!r} but found {self.cur.text!r}", self.cur.span)
        return self.advance()

    def expect_kind(self, kind: str, what: str) -> Token:
        if self.cur.kind != kind:
            raise ParseError(f"expected {what} but found {self.cur.text!r}", self.cur.span)
        return self.advance()

    def eof(self) -> bool:
        return self.cur.kind == "eof"

    # -- program ------------------------------------------------------------
    def parse_program(self) -> A.Program:
        decls: List[object] = []
        while not self.eof():
            decls.append(self.parse_decl())
        return A.Program(decls)

    def parse_decl(self) -> object:
        if self.at("var"):
            return self.parse_var_decl()
        if self.at("lock"):
            return self.parse_lock_decl()
        if self.at("class"):
            return self.parse_class_decl()
        if self.at("thread"):
            return self.parse_thread_decl()
        if self.at("init"):
            start = self.advance().span
            pred = self.parse_expr()
            end = self.expect(";").span
            return A.InitDecl(pred, Span.merge(start, end))
        if self.at("atomic") or self.at("relies"):
            return self.parse_fn_decl()
        raise ParseError(
            f"expected a declaration (var, lock, class, thread, atomic, relies) "
            f"but found {self.cur.text!r}",
            self.cur.span,
        )

    def parse_class_decl(self) -> A.ClassDecl:
        start = self.expect("class").span
        name = self.expect_kind("id", "class name").text
        self.expect("{")
        fields: List[A.VarDecl] = []
        methods: List[A.FnDecl] = []
        while not self.at("}"):
            if self.eof():
                raise ParseError("unexpected end of file inside class body", self.cur.span)
            if self.at("var"):
                fields.append(self.parse_var_decl(owner=name))
            elif self.at("lock"):
                fields.append(self.parse_lock_decl(owner=name))
            elif self.at("atomic") or self.at("relies"):
                methods.append(self.parse_fn_decl(owner=name))
            else:
                raise ParseError(
                    f"expected a field (var, lock) or method (atomic, relies) "
                    f"declaration but found {self.cur.text!r}",
                    self.cur.span,
                )
        end = self.expect("}").span
        return A.ClassDecl(name, fields, methods, Span.merge(start, end))

    # -- variable / lock declarations --------------------------------------
    def parse_type(self) -> A.TypeExpr:
        start = self.cur.span
        name = self.cur.text
        if self.cur.kind == "kw" and name in ("int", "bool", "lock_t", "value"):
            self.advance()
        elif self.cur.kind == "id":
            self.advance()
        else:
            raise ParseError(f"expected a type but found {name!r}", start)
        args: List[A.TypeExpr] = []
        if self.at("["):
            # could be Type[Arg] generic or Type[] array; peek
            self.advance()
            if self.at("]"):
                self.advance()
                return A.TypeExpr(name, [], is_array=True)
            args.append(self.parse_type())
            self.expect("]")
        is_array = False
        if self.at("["):
            self.advance()
            self.expect("]")
            is_array = True
        return A.TypeExpr(name, args, is_array=is_array)

    def parse_var_decl(self, owner: Optional[str] = None) -> A.VarDecl:
        start = self.expect("var").span
        ty = self.parse_type()
        name = self.expect_kind("id", "variable name").text
        clauses = self.parse_mover_clauses(owner)
        end = self.expect(";").span
        return A.VarDecl(name, ty, False, clauses, Span.merge(start, end), owner=owner)

    def parse_lock_decl(self, owner: Optional[str] = None) -> A.VarDecl:
        start = self.expect("lock").span
        name = self.expect_kind("id", "lock name").text
        clauses = self.parse_mover_clauses(owner)
        end = self.expect(";").span
        span = Span.merge(start, end)
        if not clauses:
            # `lock m;` defaults to the standard mutex discipline
            clauses = self._default_lock_clauses(name, owner, span)
        return A.VarDecl(name, A.TypeExpr("lock_t"), True, clauses, span,
                         owner=owner)

    def _lock_ref(self, lname: str, owner: Optional[str], span: Span) -> A.Expr:
        if owner is None:
            return A.Var(lname, span)
        return A.FieldAccess(A.Var("this", span), lname, span)

    def _default_lock_clauses(self, name: str, owner: Optional[str],
                              span: Span) -> List[A.MoverClause]:
        """acquire (0 -> tid) is a right-mover, release (tid -> 0) a
        left-mover, and the holder may read the lock."""
        l = lambda: self._lock_ref(name, owner, span)
        zero = lambda: A.Num(0, span)
        tid = lambda: A.Tid(span)
        eq = lambda a, b: A.Binary("==", a, b, span)
        conj = lambda a, b: A.Binary("&&", a, b, span)
        return [
            A.MoverClause("write", None, Effect.R,
                          conj(eq(A.Old(l(), span), zero()), eq(l(), tid())), span),
            A.MoverClause("write", None, Effect.L,
                          conj(eq(A.Old(l(), span), tid()), eq(l(), zero())), span),
            A.MoverClause("read", None, Effect.B, eq(l(), tid()), span),
        ]

    def parse_mover_clauses(self, owner: Optional[str] = None) -> List[A.MoverClause]:
        clauses: List[A.MoverClause] = []
        while True:
            index = None
            access = None
            if self.at("guarded_by"):
                # sugar: both-mover while the named lock is held
                start = self.advance().span
                lname = self.expect_kind("id", "lock name").text
                guard = A.Binary("==", self._lock_ref(lname, owner, start),
                                 A.Tid(start), start)
                clauses.append(A.MoverClause(None, None, Effect.B, guard, start))
                continue
            if self.at("["):
                self.advance()
                index = self.expect_kind("id", "index variable").text
                self.expect("]")
            if self.at("read") or self.at("write"):
                access = self.advance().text
            if self.cur.text in MOVER_KW:
                start = self.cur.span
                mover = MOVER_KW[self.cur.text]
                self.advance()
                if self.at("if"):
                    self.advance()
                    cond = self.parse_expr()
                else:
                    cond = A.BoolLit(True, start)
                end = cond.span
                clauses.append(A.MoverClause(access, index, mover, cond, Span.merge(start, end)))
            elif index is not None or access is not None:
                raise ParseError("expected a mover keyword", self.cur.span)
            else:
                break
        return clauses

    # -- thread ------------------------------------------------------------
    def parse_thread_decl(self) -> A.ThreadDecl:
        start = self.expect("thread").span
        body = self.parse_block()
        return A.ThreadDecl(body, Span.merge(start, self.toks[self.p - 1].span))

    # -- function ----------------------------------------------------------
    def parse_fn_decl(self, owner: Optional[str] = None) -> A.FnDecl:
        start = self.cur.span
        if self.at("atomic"):
            self.advance()
            mover = Effect.N
            if self.cur.text in MOVER_KW:
                mover = MOVER_KW[self.cur.text]
                self.advance()
            self.expect("requires")
            req = self.parse_expr()
            self.expect("ensures")
            ens = self.parse_expr()
            spec: object = A.AtomicSpec(mover, req, ens)
        else:
            self.expect("relies")
            relies = self.parse_expr()
            self.expect("guarantees")
            guarantees = self.parse_expr()
            self.expect("requires")
            req = self.parse_expr()
            self.expect("ensures")
            ens = self.parse_expr()
            spec = A.NonAtomicSpec(relies, guarantees, req, ens)
        name = self.expect_kind("id", "function name").text
        self.expect("(")
        params: List[A.Param] = []
        if not self.at(")"):
            params.append(self.parse_param())
            while self.at(","):
                self.advance()
                params.append(self.parse_param())
        self.expect(")")
        body = self.parse_block()
        if owner is not None:
            name = f"{owner}.{name}"
        return A.FnDecl(name, spec, body, Span.merge(start, self.toks[self.p - 1].span),
                        params=params, cls=owner)

    def parse_param(self) -> A.Param:
        start = self.cur.span
        ty = self.parse_type()
        name = self.expect_kind("id", "parameter name").text
        return A.Param(name, ty, Span.merge(start, self.toks[self.p - 1].span))

    # -- statements --------------------------------------------------------
    def parse_block(self) -> List[A.Stmt]:
        self.expect("{")
        stmts: List[A.Stmt] = []
        while not self.at("}"):
            if self.eof():
                raise ParseError("unexpected end of file inside block", self.cur.span)
            stmts.append(self.parse_stmt())
        self.expect("}")
        return stmts

    def parse_stmt(self) -> A.Stmt:
        t = self.cur
        if self.at("skip"):
            self.advance(); self.expect(";")
            return A.Skip(t.span)
        if self.at("yield"):
            self.advance(); self.expect(";")
            return A.Yield(t.span)
        if self.at("wrong"):
            self.advance(); self.expect(";")
            return A.Wrong(t.span)
        if self.at("assert"):
            self.advance()
            e = self.parse_expr()
            self.expect(";")
            return A.Assert(e, Span.merge(t.span, e.span))
        if self.at("acquire"):
            self.advance(); self.expect("(")
            lk = self.parse_postfix()
            self.expect(")"); self.expect(";")
            if isinstance(lk, A.Var):
                return A.Acquire(lk.name, t.span)
            if isinstance(lk, A.FieldAccess):
                return A.Acquire(lk.field, t.span, lock_expr=lk)
            raise ParseError("acquire expects a lock name or a lock field", lk.span)
        if self.at("release"):
            self.advance(); self.expect("(")
            lk = self.parse_postfix()
            self.expect(")"); self.expect(";")
            if isinstance(lk, A.Var):
                return A.Release(lk.name, t.span)
            if isinstance(lk, A.FieldAccess):
                return A.Release(lk.field, t.span, lock_expr=lk)
            raise ParseError("release expects a lock name or a lock field", lk.span)
        if self.at("if"):
            return self.parse_if()
        if self.at("while"):
            return self.parse_while()
        if self.at_kind("id") or self.at("this"):
            return self.parse_id_stmt()
        if self.at("result") or self.at("\\result"):
            self.advance()
            self.expect("=")
            rhs = self.parse_expr()
            end = self.expect(";").span
            return A.Assign("result", rhs, Span.merge(t.span, end))
        raise ParseError(f"expected a statement but found {self.cur.text!r}", self.cur.span)

    def parse_if(self) -> A.If:
        start = self.expect("if").span
        self.expect("(")
        cond = self.parse_cond()
        self.expect(")")
        then_body = self.parse_block()
        else_body: List[A.Stmt] = []
        if self.at("else"):
            self.advance()
            else_body = self.parse_block()
        return A.If(cond, then_body, else_body, Span.merge(start, self.toks[self.p - 1].span))

    def parse_while(self) -> A.While:
        start = self.expect("while").span
        self.expect("(")
        cond = self.parse_cond()
        self.expect(")")
        inv = None
        if self.at("invariant"):
            self.advance()
            inv = self.parse_expr()
        body = self.parse_block()
        return A.While(cond, body, inv, Span.merge(start, self.toks[self.p - 1].span))

    def parse_id_stmt(self) -> A.Stmt:
        start = self.cur.span
        e = self.parse_postfix()
        # call statements:  f(args);   e.m(args);
        if self.at(";") and isinstance(e, (A.Call, A.MCall)):
            self.advance()
            if isinstance(e, A.Call):
                return A.Call_(e.name, e.span, args=list(e.args))
            return A.Call_(e.name, e.span, args=list(e.args), receiver=e.receiver)
        if not self.at("="):
            raise ParseError(f"expected '=' or ';' but found {self.cur.text!r}",
                             self.cur.span)
        self.advance()
        # unstable read:  r = *x;   r = *e.f;
        if self.at("*"):
            if not isinstance(e, A.Var):
                raise ParseError("the target of an unstable read must be a local",
                                 e.span)
            self.advance()
            src = self.parse_postfix()
            end = self.expect(";").span
            span = Span.merge(start, end)
            if isinstance(src, A.Var):
                return A.UnstableRead(e.name, src.name, span)
            if isinstance(src, A.FieldAccess):
                return A.UnstableRead(e.name, src.field, span, source_expr=src)
            raise ParseError("the source of an unstable read must be a variable "
                             "or a field", src.span)
        rhs = self.parse_expr()
        end = self.expect(";").span
        span = Span.merge(start, end)
        if isinstance(e, A.Var):
            return A.Assign(e.name, rhs, span)
        if isinstance(e, A.FieldAccess):
            return A.FieldWrite(e.base, e.field, rhs, span)
        if isinstance(e, A.Index):
            return A.ArrayWrite(e.base, e.index, rhs, span)
        raise ParseError("invalid assignment target", e.span)

    # -- conditional actions ------------------------------------------------
    def parse_cond(self) -> A.Cond:
        if self.at("!"):
            start = self.advance().span
            inner = self.parse_cond()
            return A.NotCond(inner, Span.merge(start, inner.span))
        if self.at("cas"):
            start = self.advance().span
            self.expect("(")
            tgt = self.parse_postfix()
            self.expect(",")
            expected = self.parse_expr()
            self.expect(",")
            new = self.parse_expr()
            end = self.expect(")").span
            span = Span.merge(start, end)
            if isinstance(tgt, A.Var):
                return A.CasCond(tgt.name, expected, new, span)
            if isinstance(tgt, A.FieldAccess):
                return A.CasCond(tgt.field, expected, new, span, target_expr=tgt)
            raise ParseError("cas target must be a variable or a field", tgt.span)
        e = self.parse_expr()
        return A.BoolCond(e, e.span)

    # ======================================================================
    # Expression parsing  (precedence climbing)
    # ======================================================================
    # Lowest to highest:
    #   <==>  |  ==>  |  ||  |  &&  |  == != < <= > >=  |  + -  |  * / %  |  ::  |  unary
    def parse_expr(self) -> A.Expr:
        return self.parse_iff()

    def _binary_level(self, ops, sub):
        left = sub()
        while self.cur.kind == "op" and self.cur.text in ops:
            op = self.advance().text
            right = sub()
            left = A.Binary(op, left, right, Span.merge(left.span, right.span))
        return left

    def parse_iff(self) -> A.Expr:
        return self._binary_level({"<==>"}, self.parse_implies)

    def parse_implies(self) -> A.Expr:
        # right-associative
        left = self.parse_or()
        if self.at("==>"):
            self.advance()
            right = self.parse_implies()
            return A.Binary("==>", left, right, Span.merge(left.span, right.span))
        return left

    def parse_or(self) -> A.Expr:
        return self._binary_level({"||"}, self.parse_and)

    def parse_and(self) -> A.Expr:
        return self._binary_level({"&&"}, self.parse_cmp)

    def parse_cmp(self) -> A.Expr:
        return self._binary_level({"==", "!=", "<", "<=", ">", ">="}, self.parse_add)

    def parse_add(self) -> A.Expr:
        return self._binary_level({"+", "-"}, self.parse_mul)

    def parse_mul(self) -> A.Expr:
        return self._binary_level({"*", "/", "%"}, self.parse_cons)

    def parse_cons(self) -> A.Expr:
        # right-associative list cons  v :: s
        left = self.parse_unary()
        if self.at("::"):
            self.advance()
            right = self.parse_cons()
            return A.Binary("::", left, right, Span.merge(left.span, right.span))
        return left

    def parse_unary(self) -> A.Expr:
        if self.at("!") or self.at("-"):
            t = self.advance()
            operand = self.parse_unary()
            return A.Unary(t.text, operand, Span.merge(t.span, operand.span))
        return self.parse_postfix()

    def parse_postfix(self) -> A.Expr:
        e = self.parse_atom()
        while True:
            if self.at("["):
                self.advance()
                idx = self.parse_expr()
                end = self.expect("]").span
                e = A.Index(e, idx, Span.merge(e.span, end))
            elif self.at("."):
                self.advance()
                fname = self.expect_kind("id", "field or method name").text
                if self.at("("):
                    self.advance()
                    args: List[A.Expr] = []
                    if not self.at(")"):
                        args.append(self.parse_expr())
                        while self.at(","):
                            self.advance()
                            args.append(self.parse_expr())
                    end = self.expect(")").span
                    e = A.MCall(e, fname, args, Span.merge(e.span, end))
                else:
                    e = A.FieldAccess(e, fname, Span.merge(e.span, self.toks[self.p - 1].span))
            else:
                break
        return e

    def parse_atom(self) -> A.Expr:
        t = self.cur
        if self.at("("):
            self.advance()
            e = self.parse_expr()
            self.expect(")")
            return e
        if t.kind == "num":
            self.advance()
            return A.Num(int(t.text), t.span)
        if self.at("true"):
            self.advance(); return A.BoolLit(True, t.span)
        if self.at("false"):
            self.advance(); return A.BoolLit(False, t.span)
        if self.at("Nil"):
            self.advance(); return A.NilLit(t.span)
        if self.at("None"):
            self.advance(); return A.NoneLit(t.span)
        if self.at("null"):
            self.advance(); return A.NullLit(t.span)
        if self.at("this"):
            self.advance(); return A.Var("this", t.span)
        if self.at("new"):
            self.advance()
            if self.at("int") or self.at("bool"):
                elem = self.advance().text
                self.expect("[")
                size = self.parse_expr()
                end = self.expect("]").span
                return A.NewArray(elem, size, Span.merge(t.span, end))
            cls = self.expect_kind("id", "class name").text
            return A.New(cls, Span.merge(t.span, self.toks[self.p - 1].span))
        if self.at("tid"):
            self.advance(); return A.Tid(t.span)
        if self.at("result") or self.at("\\result"):
            self.advance(); return A.Result(t.span)
        if self.at("\\old"):
            self.advance()
            self.expect("(")
            inner = self.parse_expr()
            end = self.expect(")").span
            return A.Old(inner, Span.merge(t.span, end))
        if self.at("forall") or self.at("exists"):
            return self.parse_quant()
        # prelude functions and general calls: head(x), tail(x), Some(x), even(x)
        if t.kind in ("id", "kw") and t.text in ("head", "tail", "Some", "even") or \
                (t.kind == "id" and self._peek_is_lparen()):
            name = self.advance().text
            self.expect("(")
            args: List[A.Expr] = []
            if not self.at(")"):
                args.append(self.parse_expr())
                while self.at(","):
                    self.advance()
                    args.append(self.parse_expr())
            end = self.expect(")").span
            return A.Call(name, args, Span.merge(t.span, end))
        if t.kind == "id":
            self.advance()
            return A.Var(t.text, t.span)
        raise ParseError(f"expected an expression but found {t.text!r}", t.span)

    def _peek_is_lparen(self) -> bool:
        return self.p + 1 < len(self.toks) and self.toks[self.p + 1].text == "("

    def parse_quant(self) -> A.Expr:
        kw = self.advance()
        kind = kw.text
        var = self.expect_kind("id", "quantifier variable").text
        if self.at(":"):
            # typed form: forall o : C . body  (a class) or forall j : int . body
            self.advance()
            if self.at("int"):
                cls = self.advance().text
            else:
                cls = self.expect_kind("id", "class name").text
            self.expect(".")
            body = self.parse_expr()
            return A.Quant(kind, var, None, None, body,
                           Span.merge(kw.span, body.span), cls=cls)
        self.expect("in")
        if not self.at("["):
            # array form: forall a in C.f . body  ranges over field C.f's arrays
            cls = self.expect_kind("id", "class name").text
            self.expect(".")
            cls += "." + self.expect_kind("id", "array field name").text
            self.expect(".")
            body = self.parse_expr()
            return A.Quant(kind, var, None, None, body,
                           Span.merge(kw.span, body.span), cls=cls)
        self.expect("[")
        lo = self.parse_expr()
        self.expect(",")
        hi = self.parse_expr()
        self.expect(")")
        self.expect(".")
        body = self.parse_expr()
        return A.Quant(kind, var, lo, hi, body, Span.merge(kw.span, body.span))


def parse(source: str, filename: str = "<input>") -> A.Program:
    tokens = lex(source, filename)
    return Parser(tokens).parse_program()
