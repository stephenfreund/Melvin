"""Unit tests for melvin.parser."""

import pytest

from melvin import ast_nodes as A
from melvin.effects import Effect
from melvin.parser import parse, Parser
from melvin.lexer import lex
from melvin.diagnostics import ParseError


def parse_expr(text):
    p = Parser(lex(text))
    e = p.parse_expr()
    return e


# ----------------------------------------------------------- declarations

def test_var_decl_with_clauses():
    prog = parse("var int x  both-mover if m == tid read non-mover;")
    vd = prog.find_var("x")
    assert vd is not None and not vd.is_lock
    assert vd.type.name == "int"
    assert len(vd.clauses) == 2
    assert vd.clauses[0].mover == Effect.B
    assert vd.clauses[0].access is None
    assert vd.clauses[1].access == "read"
    assert vd.clauses[1].mover == Effect.N


def test_var_clause_default_true_guard():
    prog = parse("var int x  both-mover;")
    cl = prog.find_var("x").clauses[0]
    assert isinstance(cl.cond, A.BoolLit) and cl.cond.value is True


def test_lock_decl():
    prog = parse(r"lock m write right-mover if \old(m)==0 && m==tid;")
    vd = prog.find_var("m")
    assert vd.is_lock and vd.type.name == "lock_t"
    assert vd.clauses[0].access == "write"
    assert vd.clauses[0].mover == Effect.R


def test_indexed_mover_clause():
    # arrays use type-side brackets: `int[] a`
    prog = parse("var int[] a  [i] both-mover if tid == i;")
    cl = prog.find_var("a").clauses[0]
    assert cl.index == "i"
    assert prog.find_var("a").type.is_array


def test_array_and_generic_types():
    prog = parse("var int[] a both-mover; var Optional buf non-mover;")
    assert prog.find_var("a").type.is_array
    assert prog.find_var("buf").type.name == "Optional"


def test_atomic_fn_default_mover_is_N():
    prog = parse("atomic requires true ensures true f() { skip; }")
    f = prog.find_func("f")
    assert f.is_atomic
    assert isinstance(f.spec, A.AtomicSpec)
    assert f.spec.mover == Effect.N


def test_atomic_fn_explicit_mover():
    prog = parse("atomic right-mover requires true ensures true f() { skip; }")
    assert prog.find_func("f").spec.mover == Effect.R


def test_nonatomic_fn():
    prog = parse("relies true guarantees true requires true ensures true f() { yield; }")
    f = prog.find_func("f")
    assert not f.is_atomic
    assert isinstance(f.spec, A.NonAtomicSpec)


def test_thread_and_init_decls():
    prog = parse("init x == 0; thread { skip; }")
    assert prog.init is not None
    assert len(prog.threads) == 1


def test_unknown_decl_raises():
    with pytest.raises(ParseError):
        parse("bogus x;")


# ------------------------------------------------------------- statements

def test_all_simple_statements():
    prog = parse("""
        atomic requires true ensures true f() {
            skip;
            yield;
            wrong;
            assert true;
            acquire(m);
            release(m);
            r = *x;
            y = 1;
            g();
            result = 3;
        }
    """)
    body = prog.find_func("f").body
    types = [type(s).__name__ for s in body]
    assert types == ["Skip", "Yield", "Wrong", "Assert", "Acquire", "Release",
                     "UnstableRead", "Assign", "Call_", "Assign"]
    assert body[6].lhs == "r" and body[6].source == "x"
    assert body[9].lhs == "result"


def test_if_else_and_while_invariant():
    prog = parse("""
        atomic requires true ensures true f() {
            if (x < 3) { skip; } else { wrong; }
            while (cas(x, 0, 1)) invariant x == 0 { skip; }
        }
    """)
    body = prog.find_func("f").body
    iff = body[0]
    assert isinstance(iff, A.If)
    assert len(iff.then_body) == 1 and len(iff.else_body) == 1
    wh = body[1]
    assert isinstance(wh, A.While)
    assert wh.invariant is not None
    assert isinstance(wh.cond, A.CasCond)


def test_if_without_else():
    prog = parse("atomic requires true ensures true f() { if (x < 3) { skip; } }")
    assert prog.find_func("f").body[0].else_body == []


def test_conditions_bool_cas_not():
    prog = parse("""
        atomic requires true ensures true f() {
            if (!cas(x, 1, 2)) { skip; }
            while (a && b) { skip; }
        }
    """)
    body = prog.find_func("f").body
    assert isinstance(body[0].cond, A.NotCond)
    assert isinstance(body[0].cond.inner, A.CasCond)
    assert isinstance(body[1].cond, A.BoolCond)


def test_missing_semicolon_raises():
    with pytest.raises(ParseError):
        parse("atomic requires true ensures true f() { skip }")


def test_unexpected_eof_in_block_raises():
    with pytest.raises(ParseError):
        parse("atomic requires true ensures true f() { skip;")


def test_bad_statement_raises():
    with pytest.raises(ParseError):
        parse("atomic requires true ensures true f() { 3 = x; }")


# ----------------------------------------------------------- expressions

def test_operator_precedence_arithmetic():
    e = parse_expr("1 + 2 * 3")
    assert isinstance(e, A.Binary) and e.op == "+"
    assert isinstance(e.right, A.Binary) and e.right.op == "*"


def test_precedence_logical_over_implies():
    e = parse_expr("a && b ==> c")
    assert e.op == "==>"
    assert e.left.op == "&&"


def test_implies_right_associative():
    e = parse_expr("a ==> b ==> c")
    assert e.op == "==>"
    assert isinstance(e.right, A.Binary) and e.right.op == "==>"


def test_cons_right_associative():
    e = parse_expr("1 :: 2 :: Nil")
    assert isinstance(e, A.Binary) and e.op == "::"
    assert isinstance(e.right, A.Binary) and e.right.op == "::"
    assert isinstance(e.right.right, A.NilLit)


def test_comparison_and_equality():
    assert parse_expr("x <= y").op == "<="
    assert parse_expr("x == y").op == "=="
    assert parse_expr("x != y").op == "!="


def test_unary_operators():
    assert isinstance(parse_expr("!b"), A.Unary)
    assert parse_expr("-x").op == "-"


def test_atoms():
    assert isinstance(parse_expr("42"), A.Num)
    assert isinstance(parse_expr("true"), A.BoolLit)
    assert isinstance(parse_expr("false"), A.BoolLit)
    assert isinstance(parse_expr("Nil"), A.NilLit)
    assert isinstance(parse_expr("None"), A.NoneLit)
    assert isinstance(parse_expr("tid"), A.Tid)
    assert isinstance(parse_expr("result"), A.Result)
    assert isinstance(parse_expr("x"), A.Var)


def test_old_and_calls():
    e = parse_expr(r"\old(x) + head(s)")
    assert isinstance(e.left, A.Old)
    assert isinstance(e.right, A.Call) and e.right.name == "head"


def test_parenthesised():
    e = parse_expr("(1 + 2) * 3")
    assert e.op == "*"
    assert e.left.op == "+"


def test_index_postfix():
    e = parse_expr("a[i]")
    assert isinstance(e, A.Index)
    assert isinstance(e.base, A.Var) and isinstance(e.index, A.Var)


def test_quantifiers():
    e = parse_expr("forall i in [0, N) . a[i] == 0")
    assert isinstance(e, A.Quant) and e.kind == "forall"
    assert e.var == "i"
    e2 = parse_expr("exists i in [0, N) . a[i] == tid")
    assert e2.kind == "exists"


def test_generic_predicate_call():
    e = parse_expr("even(x)")
    assert isinstance(e, A.Call) and e.name == "even"
    e2 = parse_expr("p(x, y)")
    assert isinstance(e2, A.Call) and len(e2.args) == 2


def test_bad_expression_raises():
    with pytest.raises(ParseError):
        parse_expr(";")
