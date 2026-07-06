"""Unit tests for moverlogic.checker (driver + result rendering)."""

import pytest

from moverlogic.checker import check_source, check_program, CheckResult
from moverlogic.diagnostics import Diagnostic, Span, Position

from _util import EXAMPLES, needs_boogie


# ------------------------------------------------------- front-end errors

def test_parse_error_reported_without_running_boogie():
    res = check_source("this is not valid", "bad.mml", boogie_path="/nonexistent")
    assert not res.ok
    assert res.diagnostics
    assert res.boogie_text == ""       # never got to codegen/prover


def test_type_error_reported():
    res = check_source("atomic requires true ensures true f() { f(); }",
                       "rec.mml", boogie_path="/nonexistent")
    assert not res.ok
    assert any("recursive" in d.message for d in res.diagnostics)


# ---------------------------------------------------------- render logic

def test_render_ok():
    r = CheckResult(ok=True, verified=5)
    assert "verified (5" in r.render()


def test_render_timeout():
    r = CheckResult(ok=False, timed_out=True,
                    diagnostics=[Diagnostic(None, "timed out after 300s")])
    out = r.render()
    assert "timed out" in out


def test_render_tool_failure():
    r = CheckResult(ok=False, tool_failure="undeclared identifier foo")
    assert "internal prover error" in r.render()


def test_render_diagnostics():
    span = Span("f.mml", Position(3, 1), Position(3, 2))
    r = CheckResult(ok=False, diagnostics=[Diagnostic(span, "nope")],
                    source_lines=["a", "b", "c"])
    assert "f.mml:3:1: error: nope" in r.render()


# ------------------------------------------------------------- end to end

@needs_boogie
def test_check_source_verifies_counter():
    res = check_source((EXAMPLES / "counter.mml").read_text(), "counter.mml")
    assert res.ok, res.render()
    assert res.verified > 0
    assert res.boogie_text                       # generated Boogie retained


@needs_boogie
def test_check_program_reads_file():
    res = check_program(str(EXAMPLES / "counter.mml"))
    assert res.ok, res.render()
