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


# ------------------------------------------------------------ discovery

def test_discovery_via_env(monkeypatch, tmp_path):
    fake = tmp_path / "boogie"
    fake.write_text("#!/bin/sh\n")
    monkeypatch.setenv("MELVIN_BOOGIE", str(fake))
    b = BoogieBackend()
    assert b.boogie_path == str(fake)


def test_discovery_failure(monkeypatch):
    monkeypatch.delenv("MELVIN_BOOGIE", raising=False)
    monkeypatch.setattr("shutil.which", lambda name: None)
    monkeypatch.setattr("os.path.exists", lambda p: False)
    with pytest.raises(BoogieError):
        BoogieBackend()


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
