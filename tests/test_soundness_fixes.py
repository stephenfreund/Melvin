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


# 5. M-while's `e not <= L` premise is enforced at the loop HEAD (WP's
#    `p = R` head conjunct), unconditionally.  Previously it was enforced
#    only via a static bump plus an exit-path assert that sat after the
#    exit-action `assume`, so a post-commit loop whose static effect is not
#    <= L (a CAS exit joins R |_| L = N) and whose exit is infeasible was
#    accepted -- even though it spins forever after the commit point.

_CAS_LOOP = """
var int y  non-mover;
var int l  write right-mover if \\old(l) == 0 && l == tid
           write left-mover  if \\old(l) == tid && l == 0;
atomic requires l == tid ensures true
f() {{
  {body}
}}
"""


@needs_boogie
def test_post_commit_cas_loop_rejected():
    # commit first, then spin: the head-phase check must fire even though the
    # exit path is infeasible (cas(l,0,tid) can never succeed while l == tid).
    src = _CAS_LOOP.format(
        body="y = 1;\n  while (!cas(l, 0, tid)) invariant l == tid { skip; }")
    res = check_source(src, "pc_cas.mml")
    assert not res.ok
    assert any("after the commit point" in d.message for d in res.diagnostics), \
        res.render()


@needs_boogie
def test_pre_commit_cas_loop_still_verifies():
    # the same spin loop BEFORE the commit point is fine (head phase <= R);
    # from l == 0 the cas succeeds and the loop exits as a right-mover.
    src = """
var int y  non-mover;
var int l  write right-mover if \\old(l) == 0 && l == tid
           write left-mover  if \\old(l) == tid && l == 0;
atomic requires l == 0 ensures true
f() {
  while (!cas(l, 0, tid)) invariant true { skip; }
  y = 1;
}
"""
    res = check_source(src, "pre_cas.mml")
    assert res.ok, res.render()


@needs_boogie
def test_loop_after_yield_still_verifies():
    # a yield resets the phase (N;Y = R), so a loop after commit-then-yield
    # starts a fresh reducible sequence and passes the head check.
    src = """
var int y  non-mover;
relies true guarantees true requires true ensures true
f() {
  yield;
  y = 1;
  yield;
  i = 0;
  while (i < 3) invariant true { i = i + 1; }
}
thread { f(); }
"""
    res = check_source(src, "yield_loop.mml")
    assert res.ok, res.render()
