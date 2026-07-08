"""End-to-end verification tests over the example programs.

These require a Boogie install and self-skip otherwise.
"""

import pytest

from melvin.checker import check_source

from _util import EXAMPLES, needs_boogie

# Programs that must verify cleanly.
VERIFYING = [
    "counter.mml",
    "counter_client2.mml",
    "spinlock.mml",
    "queue.mml",
    "stack.mml",
    "write_guarded.mml",
    "nested_control.mml",
    "assert_pass.mml",
    "nonatomic_two_yields.mml",
    "atomic_calls_atomic.mml",
    "obj_counter.mml",
    "obj_counter_client.mml",
    "obj_array.mml",
    "obj_oracle_safe.mml",
]

# Programs that must be rejected, with a substring expected in some diagnostic.
REJECTED = {
    "racy_bad.mml": "race",
    "assert_fail.mml": "assertion",
    "double_release.mml": "not permitted",
    "both_mover_loop.mml": "terminate",
    "rely_not_transitive.mml": "not transitive",
    "rely_not_reflexive.mml": "not reflexive",
    "obj_racy_bad.mml": "race",
    "obj_oracle_unsafe.mml": "assertion",
}


def run(name):
    return check_source((EXAMPLES / name).read_text(), name)


@needs_boogie
@pytest.mark.parametrize("name", VERIFYING)
def test_examples_verify(name):
    res = run(name)
    assert res.ok, res.render()


@needs_boogie
@pytest.mark.parametrize("name,needle", list(REJECTED.items()))
def test_examples_rejected(name, needle):
    res = run(name)
    assert not res.ok
    assert any(needle in d.message for d in res.diagnostics), res.render()


# --------------------------------------------------- mutation / robustness

@needs_boogie
def test_racy_error_maps_to_correct_line():
    res = run("racy_bad.mml")
    assert any(d.span and d.span.start.line == 18 for d in res.diagnostics)


@needs_boogie
def test_missing_yield_breaks_reducibility():
    src = (EXAMPLES / "counter.mml").read_text()
    lines, out, seen = src.splitlines(), [], 0
    for l in lines:
        if l.strip() == "yield;":
            seen += 1
            if seen == 2:
                continue
        out.append(l)
    res = check_source("\n".join(out), "no_yield.mml")
    assert not res.ok
    assert any("reducib" in d.message for d in res.diagnostics)


@needs_boogie
def test_wrong_postcondition_fails():
    src = (EXAMPLES / "counter.mml").read_text().replace(
        "x == \\old(x) + n", "x == \\old(x) + 1")
    assert not check_source(src, "wrongpost.mml").ok


@needs_boogie
def test_validity_condition3_rejects_data_dependent_mover():
    src = "var int x  both-mover if x == 0;\n" \
          "atomic requires true ensures true f() { t = x; }\n"
    res = check_source(src, "badspec3.mml")
    assert not res.ok
    assert any("validity" in d.message or "invalid" in d.message for d in res.diagnostics)


@needs_boogie
def test_validity_commuting_rejects_racy_both_mover():
    src = "var int x  both-mover if true;\n" \
          "atomic requires true ensures true f() { x = 1; }\nthread { f(); }\n"
    res = check_source(src, "badcommute.mml")
    assert not res.ok
    assert any("validity condition" in d.message for d in res.diagnostics)


@needs_boogie
def test_lock_discipline_valid_no_false_positive():
    res = run("counter.mml")
    assert res.ok, res.render()
