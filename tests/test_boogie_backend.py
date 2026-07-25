"""Unit tests for melvin.boogie_backend (Emitter, parsing, discovery, timeout)."""

import subprocess
import types

import pytest

from melvin.boogie_backend import (
    Emitter, Obligation, BoogieBackend, BoogieError, VerifyResult, DEFAULT_TIMEOUT,
)
from melvin.diagnostics import Span, Position


def span(line):
    return Span("f.mml", Position(line, 1), Position(line, 2))


# --------------------------------------------------------------- Emitter

def test_emitter_line_numbering_and_text():
    em = Emitter()
    n1 = em.line("a")
    n2 = em.line("b")
    assert (n1, n2) == (1, 2)
    assert em.text() == "a\nb\n"


def test_emitter_indentation():
    em = Emitter()
    em.line("top")
    em.indent()
    em.line("inner")
    em.dedent()
    em.line("back")
    assert em.lines == ["top", "  inner", "back"]


def test_emitter_dedent_floor():
    em = Emitter()
    em.dedent()          # should not go negative
    em.line("x")
    assert em.lines == ["x"]


def test_emitter_assert_records_obligation_at_line():
    em = Emitter()
    em.line("procedure P() {")
    ln = None
    em.assert_("1 == 1", span(7), "my message", good_note="note")
    ln = len(em.lines)
    ob = em.obligations[ln]
    assert ob.message == "my message"
    assert ob.span.start.line == 7
    assert em.lines[-1] == "assert 1 == 1;"


def test_emitter_raw_and_blank():
    em = Emitter()
    em.raw("verbatim")
    em.blank()
    assert em.lines == ["verbatim", ""]


# ------------------------------------------------- obligation resolution

def test_nearest_obligation_exact_and_preceding():
    em = Emitter()
    em.assert_("true", span(1), "first")     # line 1
    em.line("filler")                         # line 2
    em.assert_("true", span(3), "second")    # line 3
    assert BoogieBackend._nearest_obligation(em, 1).message == "first"
    # a reported line between obligations maps to the nearest preceding one
    assert BoogieBackend._nearest_obligation(em, 2).message == "first"
    assert BoogieBackend._nearest_obligation(em, 3).message == "second"
    # before any obligation -> None
    em2 = Emitter()
    em2.line("x")
    em2.assert_("true", span(5), "later")
    assert BoogieBackend._nearest_obligation(em2, 0) is None


# --------------------------------------------------- output interpretation

class FakeProc:
    def __init__(self, stdout="", stderr=""):
        self.stdout = stdout
        self.stderr = stderr


def make_backend():
    b = BoogieBackend.__new__(BoogieBackend)   # bypass discovery
    b.boogie_path = "/bin/true"
    b.extra_args = []
    return b


def test_interpret_success():
    em = Emitter()
    em.assert_("true", span(1), "obligation A")
    backend = make_backend()
    proc = FakeProc(stdout="Boogie program verifier finished with 3 verified, 0 errors")
    res = backend._interpret(proc, em, "prog.bpl")
    assert res.ok and res.verified == 3 and res.n_errors == 0


def test_interpret_maps_error_to_obligation():
    em = Emitter()
    em.line("procedure P() {")               # 1
    em.assert_("1 == 2", span(42), "bad thing")   # 2
    em.line("}")                              # 3
    backend = make_backend()
    proc = FakeProc(stdout=(
        "prog.bpl(2,3): Error BP5001: This assertion might not hold.\n"
        "Boogie program verifier finished with 0 verified, 1 error"))
    res = backend._interpret(proc, em, "prog.bpl")
    assert not res.ok and res.n_errors == 1
    assert res.diagnostics[0].message == "bad thing"
    assert res.diagnostics[0].span.start.line == 42


_MODEL_BLOCK = """*** MODEL
v_x -> 6
v_t -> 6
tid -> 1
*** END_MODEL"""


def _model_case(order):
    """Boogie 2.x prints the model before its error; 3.x prints it after."""
    em = Emitter()
    em.line("procedure P() {")                    # 1
    em.assert_("1 == 2", span(42), "bad thing")   # 2
    em.line("}")                                  # 3
    err = "prog.bpl(2,3): Error BP5001: This assertion might not hold."
    body = f"{_MODEL_BLOCK}\n{err}" if order == "before" else f"{err}\n{_MODEL_BLOCK}"
    proc = FakeProc(stdout=body + "\nBoogie program verifier finished with 0 verified, 1 error")
    return make_backend()._interpret(proc, em, "prog.bpl")


@pytest.mark.parametrize("order", ["before", "after"])
def test_interpret_attaches_model_in_either_order(order):
    res = _model_case(order)
    assert res.n_errors == 1
    rows = dict(res.diagnostics[0].model or [])
    assert rows.get("x") == "6", rows


def test_interpret_model_only_attaches_once():
    """A second block after an error that already has a model waits for the next."""
    em = Emitter()
    em.assert_("1 == 2", span(42), "first")     # line 1
    em.assert_("1 == 3", span(43), "second")    # line 2
    proc = FakeProc(stdout=(
        "prog.bpl(1,1): Error: nope\n" + _MODEL_BLOCK + "\n"
        + _MODEL_BLOCK.replace("v_x -> 6", "v_x -> 7") + "\n"
        "prog.bpl(2,1): Error: nope\n"
        "Boogie program verifier finished with 0 verified, 2 errors"))
    res = make_backend()._interpret(proc, em, "prog.bpl")
    assert [dict(d.model or []).get("x") for d in res.diagnostics] == ["6", "7"]


def test_interpret_deduplicates_repeated_error_lines():
    em = Emitter()
    em.assert_("x", span(1), "m")            # line 1
    backend = make_backend()
    proc = FakeProc(stdout=(
        "prog.bpl(1,1): Error: nope\n"
        "prog.bpl(1,1): Error: nope\n"
        "Boogie program verifier finished with 0 verified, 2 errors"))
    res = backend._interpret(proc, em, "prog.bpl")
    assert res.n_errors == 1                 # collapsed to one


def test_interpret_tool_failure_on_unparseable_error():
    # A prover failure with no `file(line,col):` obligation match becomes a
    # tool_failure rather than a source diagnostic.
    em = Emitter()
    backend = make_backend()
    proc = FakeProc(stdout="Fatal error: the prover crashed unexpectedly")
    res = backend._interpret(proc, em, "prog.bpl")
    assert not res.ok
    assert res.tool_failure is not None


def test_interpret_unmapped_error_line_still_reported():
    # An error line with no matching obligation is surfaced generically.
    em = Emitter()
    backend = make_backend()
    proc = FakeProc(stdout="prog.bpl(3,5): Error: undeclared identifier: foo")
    res = backend._interpret(proc, em, "prog.bpl")
    assert not res.ok and res.n_errors == 1


# ------------------------------------------- model dialects (Boogie 2.x / 3.x)

# Excerpt of a real Boogie 3.5.6 model: maps are `(_ (as-array) (k!n))` values
# whose graphs are separate `k!n` entries, not two-argument `Select_` graphs.
_AS_ARRAY_MODEL = """tid -> 1
v_b@0 -> T@Box!val!0
v_a@0 -> T@Arr_Box_data!val!0
null_Box -> T@Box!val!1
null_Arr_Box_data -> T@Arr_Box_data!val!2
v_f_Box_data@1 -> (_ (as-array) (k!0))
v_len_Box_data@0 -> (_ (as-array) (k!11))
v_elems_Box_data@1 -> (_ (as-array) (k!7))
k!0 -> {
  T@Box!val!0 -> T@Arr_Box_data!val!0
  else -> T@Arr_Box_data!val!2
}
k!11 -> {
  T@Arr_Box_data!val!0 -> 3
  else -> 9
}
k!6 -> {
  0 -> 4
  1 -> 7
  else -> 8
}
k!7 -> {
  T@Arr_Box_data!val!0 -> (_ (as-array) (k!6))
  else -> (_ (as-array) (k!6))
}"""


def test_model_table_decodes_as_array_maps():
    """Boogie 3.x map values resolve through their k!n graphs."""
    from melvin.boogie_backend import model_table, _parse_model_block
    raw, funcs = _parse_model_block(_AS_ARRAY_MODEL.splitlines())
    rows = dict(model_table(raw, funcs, {"Box": {"data": "Arr_Box_data"}}))
    assert rows["b"] == "Box#0"
    assert rows["Box#0.data"] == "Arr_Box_data#0"
    assert rows["Arr_Box_data#0.length"] == "3"
    # the failing comparison's elements, from the inner map's graph
    assert rows["Arr_Box_data#0[0]"] == "4"
    assert rows["Arr_Box_data#0[1]"] == "7"


def test_model_table_still_decodes_select_graphs():
    """The Boogie 2.x dialect (two-argument Select_ graphs) keeps working."""
    from melvin.boogie_backend import model_table, _parse_model_block
    text = """tid -> 1
v_b@0 -> T@Box!val!0
null_Box -> T@Box!val!1
v_f_Box_data@0 -> |T@[Box]int!val!0|
Select_[Box]$int -> {
  T@[Box]int!val!0 T@Box!val!0 -> 5
  else -> 0
}"""
    raw, funcs = _parse_model_block(text.splitlines())
    rows = dict(model_table(raw, funcs, {"Box": {"data": "int"}}))
    assert rows["Box#0.data"] == "5"


# ------------------------------------------------------------ discovery

def test_discovery_via_env(monkeypatch, tmp_path):
    fake = tmp_path / "boogie"
    fake.write_text("#!/bin/sh\n")
    monkeypatch.setenv("MELVIN_BOOGIE", str(fake))
    b = BoogieBackend()
    assert b.boogie_path == str(fake)


def test_discovery_failure(monkeypatch):
    monkeypatch.setattr("melvin.tools.find_boogie", lambda: None)
    with pytest.raises(BoogieError) as e:
        BoogieBackend()
    assert "melvin-install-boogie" in str(e.value)


def test_prover_path_passed_when_z3_off_path(monkeypatch, tmp_path):
    """Z3 from the `melvin[z3]` wheel need not be on PATH; Boogie is told where."""
    fake = tmp_path / "boogie"
    fake.write_text("#!/bin/sh\n")
    monkeypatch.setenv("MELVIN_BOOGIE", str(fake))
    monkeypatch.setattr("melvin.tools.z3_on_path", lambda: False)
    monkeypatch.setattr("melvin.tools.find_z3", lambda: "/somewhere/z3")
    b = BoogieBackend()
    assert b._prover_args() == ["/proverOpt:PROVER_PATH=/somewhere/z3"]

    monkeypatch.setattr("melvin.tools.z3_on_path", lambda: True)
    assert b._prover_args() == []


# -------------------------------------------------------------- timeout

def test_verify_timeout_sets_flag(monkeypatch, tmp_path):
    backend = make_backend()

    def fake_run(bpl_path, timeout, extra=None):
        raise subprocess.TimeoutExpired(cmd="boogie", timeout=timeout, output="partial")

    monkeypatch.setattr(backend, "run_raw", fake_run)
    em = Emitter()
    em.assert_("true", span(1), "x")
    bpl = tmp_path / "p.bpl"
    res = backend.verify(em, str(bpl), timeout=3)
    assert res.timed_out and not res.ok
    assert "timed out" in res.diagnostics[0].message
    assert "3s" in res.diagnostics[0].message


def test_default_timeout_is_five_minutes():
    assert DEFAULT_TIMEOUT == 300
