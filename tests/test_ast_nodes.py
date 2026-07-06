"""Unit tests for melvin.ast_nodes helper accessors."""

from melvin.parser import parse
from melvin import ast_nodes as A


def test_program_accessors():
    prog = parse("""
        var int x both-mover;
        lock m write right-mover if m == tid;
        atomic requires true ensures true f() { skip; }
        relies true guarantees true requires true ensures true g() { yield; }
        init x == 0;
        thread { f(); }
        thread { g(); }
    """)
    assert {v.name for v in prog.vars} == {"x", "m"}
    assert {f.name for f in prog.funcs} == {"f", "g"}
    assert len(prog.threads) == 2
    assert prog.init is not None


def test_find_helpers_return_none_for_missing():
    prog = parse("var int x both-mover;")
    assert prog.find_var("x") is not None
    assert prog.find_var("nope") is None
    assert prog.find_func("nope") is None


def test_init_is_none_when_absent():
    prog = parse("var int x both-mover;")
    assert prog.init is None


def test_fndecl_is_atomic():
    prog = parse("""
        atomic requires true ensures true a() { skip; }
        relies true guarantees true requires true ensures true b() { yield; }
    """)
    assert prog.find_func("a").is_atomic
    assert not prog.find_func("b").is_atomic


def test_typeexpr_str():
    assert str(A.TypeExpr("int")) == "int"
    assert str(A.TypeExpr("int", is_array=True)) == "int[]"
    assert str(A.TypeExpr("Optional", [A.TypeExpr("int")])) == "Optional[int]"
