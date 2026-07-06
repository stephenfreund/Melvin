"""Unit tests for moverlogic.types."""

import pytest

from moverlogic.parser import parse
from moverlogic.types import check_types, type_to_boogie, TVar, unify, resolve
from moverlogic.ast_nodes import TypeExpr, Assign
from moverlogic.diagnostics import TypeError_, Span, Position

SP = Span("t", Position(1, 1), Position(1, 1))


# --------------------------------------------------------- type_to_boogie

def test_type_to_boogie_scalars():
    assert type_to_boogie(TypeExpr("int")) == "int"
    assert type_to_boogie(TypeExpr("bool")) == "bool"
    assert type_to_boogie(TypeExpr("lock_t")) == "int"
    assert type_to_boogie(TypeExpr("value")) == "Value"
    assert type_to_boogie(TypeExpr("Optional")) == "Optional"
    assert type_to_boogie(TypeExpr("List")) == "List"


def test_type_to_boogie_array():
    assert type_to_boogie(TypeExpr("int", is_array=True)) == "[int]int"


# ------------------------------------------------------------ unification

def test_tvar_unify_and_resolve():
    a, b = TVar(), TVar()
    unify(a, "int", SP)
    assert resolve(a) == "int"
    unify(b, a, SP)
    assert resolve(b) == "int"


def test_unify_conflict_raises():
    with pytest.raises(TypeError_):
        unify("int", "bool", SP)


# --------------------------------------------------------------- globals

def test_collect_globals_and_locks():
    prog = parse("""
        var int x both-mover;
        var int[] a both-mover;
        lock m write right-mover if m == tid;
    """)
    ti = check_types(prog)
    assert ti.globals == {"x": "int", "a": "[int]int", "m": "int"}
    assert ti.lock_names == {"m"}
    assert ti.array_names == {"a"}


def test_duplicate_global_rejected():
    with pytest.raises(TypeError_):
        check_types(parse("var int x both-mover; var int x both-mover;"))


# ------------------------------------------------ action classification

def _add_program():
    return parse(r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        atomic requires true ensures true f() {
            acquire(m);
            t = x;
            t = t + n;
            x = t;
            result = t;
            release(m);
        }
    """)


def test_action_classification():
    prog = _add_program()
    ti = check_types(prog)
    f = prog.find_func("f")
    kinds = {}
    for s in f.body:
        if isinstance(s, Assign):
            kinds[s.lhs, type(s.rhs).__name__] = ti.assign_kind[id(s)][0]
    assert kinds[("t", "Var")] == "read"           # t = x
    assert kinds[("t", "Binary")] == "local"       # t = t + n
    assert kinds[("x", "Var")] == "write"          # x = t
    assert kinds[("result", "Var")] == "local"     # result = t


def test_local_type_inference():
    prog = _add_program()
    ti = check_types(prog)
    assert ti.locals["fn:f"]["t"] == "int"
    assert ti.locals["fn:f"]["n"] == "int"


def test_bool_local_inference():
    prog = parse("""
        var int x both-mover;
        atomic requires true ensures true f() {
            if (b) { skip; }
        }
    """)
    ti = check_types(prog)
    assert ti.locals["fn:f"]["b"] == "bool"


# ----------------------------------------------------------- error cases

def test_assign_to_lock_rejected():
    src = r"""
        lock m write right-mover if m == tid;
        atomic requires true ensures true f() { m = 1; }
    """
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_global_in_write_rhs_rejected():
    src = """
        var int x both-mover; var int y both-mover;
        atomic requires true ensures true f() { x = y; }
    """
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_compound_global_read_rejected():
    src = """
        var int x both-mover;
        atomic requires true ensures true f() { r = x + 1; }
    """
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_call_unknown_function_rejected():
    src = "atomic requires true ensures true f() { g(); }"
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_atomic_recursion_rejected():
    with pytest.raises(TypeError_):
        check_types(parse("atomic requires true ensures true f() { f(); }"))


def test_indirect_atomic_recursion_rejected():
    src = """
        atomic requires true ensures true f() { g(); }
        atomic requires true ensures true g() { f(); }
    """
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_unstable_read_from_non_global_rejected():
    src = "atomic requires true ensures true f() { r = *nope; }"
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_acquire_of_non_lock_rejected():
    src = "atomic requires true ensures true f() { acquire(nope); }"
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_mover_clause_referencing_local_rejected():
    # mover specs may only mention globals and tid
    src = "var int x both-mover if q == 1;"
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_type_mismatch_rejected():
    src = """
        var int x both-mover;
        atomic requires (x + true) ensures true f() { skip; }
    """
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_func_return_default_int():
    prog = parse("atomic requires true ensures true f() { skip; }")
    ti = check_types(prog)
    assert ti.func_return["f"] == "int"


# --------------------------------------- prelude-call / quantifier inference

def test_infer_list_calls_and_quantifiers():
    src = r"""
        var List top non-mover;
        var int[] a both-mover;
        atomic requires top != Nil ensures head(top) == 1 && tail(top) == \old(top)
        f() { skip; }
        atomic requires (forall i in [0, 3) . a[i] == 0) ensures true
        g() { skip; }
    """
    check_types(parse(src))          # exercises head/tail/Nil/index/quant inference


def test_infer_optional_calls():
    src = "var Optional buf non-mover;\n" \
          "atomic requires buf == None ensures buf == Some(1) f() { skip; }"
    check_types(parse(src))


def test_unknown_predicate_infers_bool():
    src = "var int x both-mover;\n" \
          "atomic requires mypred(x) ensures true f() { skip; }"
    check_types(parse(src))


def test_existential_quantifier_inference():
    src = r"""
        var int[] locks both-mover;
        atomic requires (exists i in [0, 4) . locks[i] == tid) ensures true
        f() { skip; }
    """
    check_types(parse(src))
