"""Tests for the object extension: classes, fields, methods, new, this.

Front-end tests run without Boogie; end-to-end tests self-skip without it.
"""

import pytest

from melvin import ast_nodes as A
from melvin.checker import check_source
from melvin.diagnostics import MelvinError, TypeError_
from melvin.parser import parse
from melvin.types import check_types

from _util import EXAMPLES, needs_boogie


COUNTER = (EXAMPLES / "obj_counter.mml").read_text()


def tc(src):
    prog = parse(src, "t.mml")
    return prog, check_types(prog)


# ------------------------------------------------------------------ parsing

def test_parse_class_decl():
    prog = parse(COUNTER, "obj_counter.mml")
    assert [c.name for c in prog.classes] == ["Counter"]
    c = prog.classes[0]
    assert [f.name for f in c.fields] == ["x", "m"]
    assert c.find_field("m").is_lock
    assert [m.name for m in c.methods] == ["Counter.add"]
    m = c.methods[0]
    assert m.cls == "Counter"
    assert [p.name for p in m.params] == ["n"]


def test_parse_field_access_and_write():
    prog, _ = tc("""
class C { var int x  non-mover; }
atomic requires true ensures true f(C c) {
  t = c.x;
  c.x = t;
}
""")
    body = prog.find_func("f").body
    assert isinstance(body[0], A.Assign)
    assert isinstance(body[0].rhs, A.FieldAccess)
    assert isinstance(body[1], A.FieldWrite)


def test_parse_method_call_forms():
    prog, ti = tc("""
class C {
  var int x  non-mover;
  atomic requires true ensures result == n get(int n) { result = n; }
}
atomic requires true ensures true f() {
  c = new C;
  c.get(1);
  r = c.get(2);
}
""")
    body = prog.find_func("f").body
    assert isinstance(body[1], A.Call_) and body[1].assign_to is None
    assert isinstance(body[2], A.Call_) and body[2].assign_to == "r"
    assert ti.call_target[id(body[1])] == "C.get"


def test_parse_ref_quantifier():
    prog, _ = tc("""
class C { var int x  non-mover; }
relies forall o : C . \\old(o.x) == o.x
guarantees true requires true ensures true f() { yield; }
""")
    spec = prog.find_func("f").spec
    assert spec.relies.cls == "C"


# ------------------------------------------------------------------- typing

def test_field_types_collected():
    _, ti = tc("class C { var int x non-mover; lock m; }")
    assert ti.classes["C"] == {"x": "int", "m": "int"}
    assert ("C", "m") in ti.field_locks


def test_this_outside_method_rejected():
    with pytest.raises(MelvinError, match="this"):
        tc("atomic requires true ensures true f() { t = this.x; }")


def test_field_guard_may_not_mention_globals():
    with pytest.raises(MelvinError, match="field mover specifications"):
        tc("var int g non-mover;\n"
           "class C { var int x  both-mover if g == 0; }")


def test_global_guard_may_not_dereference():
    with pytest.raises(MelvinError, match="'this'"):
        tc("class C { var int x non-mover; }\n"
           "var int g  both-mover if this.x == 0;")


def test_parameters_immutable():
    with pytest.raises(MelvinError, match="immutable"):
        tc("class C { var int x non-mover; }\n"
           "atomic requires true ensures true f(int n) { n = 3; }")


def test_cannot_assign_this():
    with pytest.raises(MelvinError, match="this"):
        tc("class C { var int x non-mover;\n"
           "atomic requires true ensures true m() { this = this; } }")


def test_new_must_target_local():
    with pytest.raises(MelvinError, match="local"):
        tc("class C { var int x non-mover; }\n"
           "var C g non-mover;\n"
           "atomic requires true ensures true f() { g = new C; }")


def test_field_write_rhs_must_be_local():
    with pytest.raises(MelvinError, match="local"):
        tc("class C { var int x non-mover; }\n"
           "atomic requires true ensures true f(C c) { c.x = c.x + 1; }")


def test_lock_field_not_assignable():
    with pytest.raises(MelvinError, match="acquire/release"):
        tc("class C { lock m; }\n"
           "atomic requires true ensures true f(C c) { c.m = 1; }")


def test_unknown_field_rejected():
    with pytest.raises(MelvinError, match="no field"):
        tc("class C { var int x non-mover; }\n"
           "atomic requires true ensures true f(C c) { t = c.y; }")


def test_null_needs_class_from_context():
    with pytest.raises(MelvinError, match="null"):
        tc("atomic requires true ensures true f() { x = null; }")


def test_null_resolves_from_comparison():
    _, ti = tc("class C { var int x non-mover; }\n"
               "atomic requires true ensures true f(C c) { b = c == null; }")
    assert "C" in ti.classes


def test_method_call_arity_checked():
    with pytest.raises(MelvinError, match="argument"):
        tc("class C { var int x non-mover;\n"
           "atomic requires true ensures true m(int a) { skip; } }\n"
           "atomic requires true ensures true f(C c) { c.m(); }")


def test_atomic_method_recursion_rejected():
    with pytest.raises(MelvinError, match="recursive"):
        tc("class C { var int x non-mover;\n"
           "atomic requires true ensures true m() { this.m(); } }")


# ------------------------------------------------------------- verification

@needs_boogie
def test_obj_counter_verifies():
    assert check_source(COUNTER, "obj_counter.mml").ok


@needs_boogie
def test_wrong_result_fails():
    res = check_source(COUNTER.replace("assert r == 2;", "assert r == 3;"), "m.mml")
    assert not res.ok
    assert any("assertion" in d.message for d in res.diagnostics)


@needs_boogie
def test_unlocked_write_is_race():
    src = COUNTER.replace("    acquire(this.m);\n", "").replace(
        "    release(this.m);\n", "")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("race" in d.message for d in res.diagnostics)


@needs_boogie
def test_two_atomic_calls_break_reducibility():
    src = COUNTER.replace("  r = c.add(2);\n  assert r == 2;",
                          "  r = c.add(2);\n  r = c.add(3);")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("reducib" in d.message for d in res.diagnostics)


@needs_boogie
def test_field_read_after_yield_with_true_rely_fails():
    src = COUNTER.replace(
        "  r = c.add(2);\n  assert r == 2;\n  yield;",
        "  r = c.add(2);\n  yield;\n  t2 = c.x;\n  yield;")
    res = check_source(src, "m.mml")
    assert not res.ok


@needs_boogie
def test_allocation_freshness():
    src = """
class C { var int x  non-mover; }
atomic requires true ensures true f() {
  a = new C;
  b = new C;
  assert !(a == b);
  t = a.x;
  assert t == 0;
}
"""
    assert check_source(src, "fresh.mml").ok


@needs_boogie
def test_two_objects_are_independent():
    src = """
class C { var int x  non-mover; }
atomic requires true ensures true f() {
  a = new C;
  b = new C;
  a.x = 1;
  b.x = 2;
  t = a.x;
  assert t == 1;
}
"""
    res = check_source(src, "indep.mml")
    assert not res.ok  # two non-mover writes + reads in one sequence break R*[N]L*


@needs_boogie
def test_two_objects_independent_with_guarded_fields():
    src = """
class C {
  var int x  both-mover if this.m == tid;
  lock m  write right-mover if \\old(this.m) == 0 && this.m == tid
          write left-mover  if \\old(this.m) == tid && this.m == 0;
}
atomic requires true ensures true f() {
  a = new C;
  b = new C;
  acquire(a.m);
  acquire(b.m);
  a.x = 1;
  b.x = 2;
  t = a.x;
  assert t == 1;
  release(b.m);
  release(a.m);
}
"""
    res = check_source(src, "indep2.mml")
    assert res.ok, res.render()


# -------------------------------------------------------------------- arrays

ARRAY = None  # loaded lazily so front-end tests do not require the file


def _array_src():
    return (EXAMPLES / "obj_array.mml").read_text()


def test_array_field_collected():
    _, ti = tc("class T { var int[] a  non-mover [i] both-mover if i == tid; }")
    assert ti.array_fields[("T", "a")] == "Arr_T_a"
    assert ti.arrays["Arr_T_a"] == "int"
    assert ti.classes["T"]["a"] == "Arr_T_a"


def test_element_clause_only_on_arrays():
    with pytest.raises(MelvinError, match="element clauses"):
        tc("class T { var int x  [i] both-mover; }")


def test_element_guard_may_not_mention_this():
    with pytest.raises(MelvinError, match="'this'"):
        tc("class T { var int m non-mover;\n"
           "var int[] a  [i] both-mover if this.m == tid; }")


def test_array_ref_fields_have_ref_semantics():
    prog, ti = tc("""
class T { var int[] a  non-mover [i] non-mover; }
atomic requires x != null ensures true f(T x) {
  b = x.a;
  n = length(b);
  b[0] = 1;
}
""")
    body = prog.find_func("f").body
    assert ti.assign_kind[id(body[0])] == ("fieldread", "T.a")
    assert isinstance(body[2], A.ArrayWrite)
    assert ti.assign_kind[id(body[2])] == ("elemwrite", "Arr_T_a")


def test_new_array_needs_nominal_type():
    with pytest.raises(MelvinError, match="array field"):
        tc("class T { var int[] a  non-mover [i] non-mover; }\n"
           "atomic requires true ensures true f() { b = new int[3]; }")


@needs_boogie
def test_obj_array_verifies():
    assert check_source(_array_src(), "obj_array.mml").ok


@needs_boogie
def test_wrong_slot_is_race():
    src = _array_src().replace("a[tid] = 5;", "a[tid + 1] = 5;") \
                      .replace("new int[tid + 1]", "new int[tid + 2]") \
                      .replace("v = a[tid];", "v = a[tid + 1];")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("element" in d.message and "race" in d.message
               for d in res.diagnostics)


@needs_boogie
def test_out_of_bounds_rejected():
    src = _array_src().replace("a = new int[tid + 1];", "a = new int[tid];")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("out of bounds" in d.message for d in res.diagnostics)


@needs_boogie
def test_unconditional_both_mover_elements_invalid():
    src = _array_src().replace("[i] both-mover if i == tid;", "[i] both-mover;")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("validity condition" in d.message for d in res.diagnostics)


@needs_boogie
def test_null_array_access_rejected():
    src = _array_src().replace(
        "  a = new int[tid + 1];    // big enough for this thread's slot\n"
        "  t.slots = a;             // non-mover: the commit of this sequence\n",
        "  a = t.slots;             // still null\n")
    res = check_source(src, "m.mml")
    assert not res.ok
    assert any("null" in d.message for d in res.diagnostics)


@needs_boogie
def test_slot_value_lost_without_rely():
    src = _array_src().replace(
        "relies     forall a in Table.slots . a[tid] == \\old(a[tid])",
        "relies     true")
    res = check_source(src, "m.mml")
    assert not res.ok


def test_untyped_null_receiver_is_type_error():
    with pytest.raises(MelvinError, match="cannot determine the class"):
        tc("class C { var int x  non-mover; }\n"
           "atomic requires true ensures true f() { c = null; t = c.x; }")


@needs_boogie
def test_quantified_rely_client_verifies():
    src = (EXAMPLES / "obj_counter_client.mml").read_text()
    assert check_source(src, "obj_counter_client.mml").ok


@needs_boogie
def test_quantified_rely_client_needs_even_rely():
    src = (EXAMPLES / "obj_counter_client.mml").read_text().replace(
        "relies     forall c : Counter . (even(\\old(c.x)) ==> even(c.x))",
        "relies     true")
    res = check_source(src, "m.mml")
    assert not res.ok


@needs_boogie
def test_field_validity3_rejects_data_dependent_mover():
    src = ("class C { var int x  both-mover if this.x == 0; }\n"
           "atomic requires c != null ensures true f(C c) { t = c.x; }\n")
    res = check_source(src, "v3.mml")
    assert not res.ok
    assert any("validity condition 3" in d.message for d in res.diagnostics)


@needs_boogie
def test_field_validity_commute_rejects_racy_both_mover():
    src = ("class C { var int x  both-mover; }\n"
           "atomic requires c != null ensures true f(C c) { c.x = 1; }\n")
    res = check_source(src, "vc.mml")
    assert not res.ok
    assert any("validity condition" in d.message for d in res.diagnostics)


@needs_boogie
def test_lock_discipline_field_spec_no_false_positive():
    # the per-object lock discipline must pass all field validity conditions
    res = check_source(COUNTER, "obj_counter.mml")
    assert res.ok, res.render()


@needs_boogie
def test_nontransitive_quantified_rely_rejected():
    src = ("class C { var int x  non-mover; }\n"
           "relies forall c : C . c.x <= \\old(c.x) + 1\n"
           "guarantees true\nrequires true ensures true f() { yield; }\n"
           "thread { f(); }\n")
    res = check_source(src, "rt.mml")
    assert not res.ok
    assert any("not transitive" in d.message for d in res.diagnostics)


@needs_boogie
def test_quantified_guarantee_must_imply_rely():
    src = ("class C { var int x  non-mover; }\n"
           "relies forall c : C . \\old(c.x) == c.x\n"
           "guarantees true\nrequires true ensures true f() { yield; }\n"
           "thread { f(); }\nthread { f(); }\n")
    res = check_source(src, "gr.mml")
    assert not res.ok
    assert any("G_t => R_u" in d.message for d in res.diagnostics)


@needs_boogie
def test_method_call_frames_other_objects():
    # calling set1() on `a` must not clobber `b`'s state: the callee writes
    # the heap only through `this`, so the call site havocs just a's entry
    src = """
class C {
  var int x  non-mover;
  atomic requires true ensures this.x == 1 set1() { this.x = 1; }
}
relies     forall c : C . \\old(c.x) == c.x
guarantees true
requires   true
ensures    true
f() {
  yield;
  a = new C;
  b = new C;
  b.x = 7;
  yield;
  a.set1();
  yield;
  t = b.x;
  assert t == 7;
  yield;
}
"""
    res = check_source(src, "frame.mml")
    assert res.ok, res.render()


@needs_boogie
def test_null_receiver_rejected():
    src = """
class C { var int x  non-mover; }
atomic requires c == null ensures true f(C c) {
  t = c.x;
}
"""
    res = check_source(src, "null.mml")
    assert not res.ok
    assert any("null" in d.message for d in res.diagnostics)
