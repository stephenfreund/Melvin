"""Systematic mutation testing: a verified program, once semantically broken,
must be rejected.  This guards soundness -- the checker must not accept mutants
that drop synchronization, remove yields, or weaken/strengthen specs unsafely.
"""

import re

import pytest

from moverlogic.checker import check_source

from _util import EXAMPLES, needs_boogie

COUNTER = (EXAMPLES / "counter.mml").read_text() if (EXAMPLES / "counter.mml").exists() else ""


def apply(src, old, new, count=1):
    assert old in src, f"pattern not found: {old!r}"
    return src.replace(old, new, count)


# Each mutation should turn the verified counter into a REJECTED program.
MUTATIONS = {
    "drop acquire": ("  acquire(m);\n", ""),
    "drop release": ("  release(m);\n", ""),
    # dropping the yield BETWEEN the two add() calls merges two reducible
    # sequences (N ; N = error), so it must be rejected.  (The leading yield is
    # only the state-rule convention and is intentionally not tested here.)
    "drop middle yield": ("  add();\n  yield;\n  n = 2;", "  add();\n  n = 2;"),
    "weaken add ensures to true": (
        "ensures  x == \\old(x) + n && result == x && m == \\old(m)",
        "ensures  x == \\old(x) + n && result == x && m == \\old(m) || true"),
    "wrong increment amount": ("t = t + n;", "t = t + 1;"),
    "swap acquire/release movers": (
        "lock m  write right-mover if \\old(m) == 0 && m == tid\n"
        "        write left-mover  if \\old(m) == tid && m == 0;",
        "lock m  write left-mover  if \\old(m) == 0 && m == tid\n"
        "        write right-mover if \\old(m) == tid && m == 0;"),
}


@needs_boogie
@pytest.mark.parametrize("label", list(MUTATIONS))
def test_counter_mutant_is_rejected(label):
    old, new = MUTATIONS[label]
    mutant = apply(COUNTER, old, new)
    res = check_source(mutant, f"mutant[{label}].mml")
    assert not res.ok, f"mutation {label!r} was NOT rejected (soundness risk)"


@needs_boogie
def test_baseline_counter_still_verifies():
    # sanity: the unmutated program verifies, so rejections above are meaningful
    assert check_source(COUNTER, "counter.mml").ok


@needs_boogie
def test_removing_lock_from_spinlock_is_rejected():
    src = (EXAMPLES / "spinlock.mml").read_text()
    # make the shared variable unconditionally racy
    mutant = src.replace("var int x  both-mover if l == tid;",
                         "var int x  both-mover if true;")
    assert not check_source(mutant, "spin_mutant.mml").ok


@needs_boogie
def test_dropping_invariant_breaks_queue():
    src = (EXAMPLES / "queue.mml").read_text()
    mutant = src.replace("invariant buf == \\old(buf)", "invariant true")
    # without the pinning invariant the postcondition no longer follows
    assert not check_source(mutant, "queue_mutant.mml").ok
