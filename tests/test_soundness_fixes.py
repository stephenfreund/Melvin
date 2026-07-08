"""Regression tests for soundness fixes backported from the objects branch.

Each of the first three used to be a differential-oracle violation: the
verifier accepted a program in which the reference interpreter (melvin.interp)
finds a reachable `wrong`.
"""

import pytest

from melvin.checker import check_source
from melvin.diagnostics import MelvinError
from melvin.parser import parse
from melvin.types import check_types

from _util import needs_boogie


# 1. Loop exit paths must havoc the thread-locals the body writes; otherwise
#    the exit test runs over pre-loop values and can make everything after the
#    loop vacuously unreachable.

@needs_boogie
def test_loop_exit_havocs_modified_locals():
    src = """
var int g non-mover;
atomic requires true ensures true f() {
  i = 0;
  while (i < 3) invariant true { r = *g; i = i + 1; }
  assert false;
}
thread { f(); }
"""
    res = check_source(src, "loop.mml")
    assert not res.ok
    assert any("assertion" in d.message for d in res.diagnostics)


@needs_boogie
def test_loop_invariant_carries_local_facts():
    src = """
var int g non-mover;
atomic requires true ensures true f() {
  i = 0;
  while (i < 3) invariant i >= 0 && i <= 3 { r = *g; i = i + 1; }
  assert i == 3;
}
thread { f(); }
"""
    res = check_source(src, "loop2.mml")
    assert res.ok, res.render()


# 2. Callee write-sets are scanned transitively through nested calls: f writes
#    x only via g, but a call to f must still havoc x.

@needs_boogie
def test_callee_writes_scanned_transitively():
    src = """
var int x  read both-mover  write non-mover;
atomic requires true ensures true g() { x = 7; }
atomic requires true ensures true f() { g(); }
atomic requires x == 0 ensures true main() {
  f();
  t = x;
  assert t == 0;
}
init x == 0;
thread { main(); }
"""
    res = check_source(src, "trans.mml")
    assert not res.ok
    assert any("assertion" in d.message for d in res.diagnostics)


@needs_boogie
def test_transitive_scan_handles_recursion():
    # mutually recursive non-atomic functions must not loop the scanner
    src = """
var int x  non-mover;
relies true guarantees true requires true ensures true
a() { yield; x = 1; b(); yield; }
relies true guarantees true requires true ensures true
b() { yield; a(); yield; }
relies true guarantees true requires true ensures true
main() { yield; a(); yield; }
thread { main(); }
"""
    res = check_source(src, "rec.mml")
    # only termination of the front end matters here; the program itself may
    # verify or not
    assert res.tool_failure is None


# 3. `result = <global>` was classified as a local computation, bypassing the
#    mover/race check entirely.

def test_result_assignment_may_not_read_globals():
    with pytest.raises(MelvinError, match="local"):
        check_types(parse(
            "var int x non-mover;\n"
            "atomic requires true ensures true f() { result = x; }",
            "r.mml"))


# 4. init predicates are type-checked, so an ill-typed init yields a proper
#    source diagnostic instead of a Boogie-level failure.

def test_init_predicate_is_type_checked():
    with pytest.raises(MelvinError, match="type mismatch"):
        check_types(parse(
            "var int x non-mover;\ninit x == true;\n", "i.mml"))
