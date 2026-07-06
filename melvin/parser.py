"""Recursive-descent parser for the Mover Logic Language.

Grammar (informal):

    program     := decl*
    decl        := var_decl | lock_decl | fn_decl | thread_decl
    var_decl    := 'var' type IDENT mover_clause* ';'
    lock_decl   := 'lock' IDENT mover_clause* ';'
    mover_clause:= ('[' IDENT ']')? ('read'|'write')? MOVER ('if' pred)?
    fn_decl     := fn_spec IDENT '(' ')' block
    fn_spec     := 'atomic' MOVER? 'requires' pred 'ensures' pred
                 | 'relies' pred 'guarantees' pred 'requires' pred 'ensures' pred
    thread_decl := 'thread' block
    block       := '{' stmt* '}'
    stmt        := 'skip' ';' | 'yield' ';' | 'wrong' ';'
                 | 'assert' pred ';'
                 | 'acquire' '(' IDENT ')' ';' | 'release' '(' IDENT ')' ';'
                 | 'if' '(' cond ')' block ('else' block)?
                 | 'while' '(' cond ')' ('invariant' pred)? block
                 | IDENT '(' ')' ';'
                 | IDENT '=' '*' IDENT ';'            (unstable read)
                 | IDENT '=' expr ';'
    cond        := '!' cond | 'cas' '(' IDENT ',' expr ',' expr ')' | expr
    pred, expr  := standard precedence climbing (see below)
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
            f"expected a declaration (var, lock, thread, atomic, relies) "
            f"but found {self.cur.text!r}",
            self.cur.span,
        )

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

    def parse_var_decl(self) -> A.VarDecl:
        start = self.expect("var").span
        ty = self.parse_type()
        name = self.expect_kind("id", "variable name").text
        clauses = self.parse_mover_clauses()
        end = self.expect(";").span
        return A.VarDecl(name, ty, False, clauses, Span.merge(start, end))

    def parse_lock_decl(self) -> A.VarDecl:
        start = self.expect("lock").span
        name = self.expect_kind("id", "lock name").text
        clauses = self.parse_mover_clauses()
        end = self.expect(";").span
        return A.VarDecl(name, A.TypeExpr("lock_t"), True, clauses, Span.merge(start, end))

    def parse_mover_clauses(self) -> List[A.MoverClause]:
        clauses: List[A.MoverClause] = []
        while True:
            index = None
            access = None
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
    def parse_fn_decl(self) -> A.FnDecl:
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
        self.expect(")")
        body = self.parse_block()
        return A.FnDecl(name, spec, body, Span.merge(start, self.toks[self.p - 1].span))

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
            lk = self.expect_kind("id", "lock name").text
            self.expect(")"); self.expect(";")
            return A.Acquire(lk, t.span)
        if self.at("release"):
            self.advance(); self.expect("(")
            lk = self.expect_kind("id", "lock name").text
            self.expect(")"); self.expect(";")
            return A.Release(lk, t.span)
        if self.at("if"):
            return self.parse_if()
        if self.at("while"):
            return self.parse_while()
        if self.at_kind("id"):
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
        ident = self.advance()
        # function call:  f();
        if self.at("("):
            self.advance()
            self.expect(")")
            self.expect(";")
            return A.Call_(ident.text, ident.span)
        # assignment
        self.expect("=")
        if self.at("*"):
            self.advance()
            src = self.expect_kind("id", "variable name").text
            end = self.expect(";").span
            return A.UnstableRead(ident.text, src, Span.merge(ident.span, end))
        rhs = self.parse_expr()
        end = self.expect(";").span
        return A.Assign(ident.text, rhs, Span.merge(ident.span, end))

    # -- conditional actions ------------------------------------------------
    def parse_cond(self) -> A.Cond:
        if self.at("!"):
            start = self.advance().span
            inner = self.parse_cond()
            return A.NotCond(inner, Span.merge(start, inner.span))
        if self.at("cas"):
            start = self.advance().span
            self.expect("(")
            target = self.expect_kind("id", "cas target").text
            self.expect(",")
            expected = self.parse_expr()
            self.expect(",")
            new = self.parse_expr()
            end = self.expect(")").span
            return A.CasCond(target, expected, new, Span.merge(start, end))
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
        while self.at("["):
            self.advance()
            idx = self.parse_expr()
            end = self.expect("]").span
            e = A.Index(e, idx, Span.merge(e.span, end))
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
        self.expect("in")
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
