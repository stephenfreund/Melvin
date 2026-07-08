"""Tests for the usability features: elidable spec clauses / `func`, traces
with source lines, JSON output, final-state enumeration, counterexamples."""

import json

import pytest

from melvin import ast_nodes as A
from melvin.checker import check_source
from melvin.diagnostics import MelvinError
from melvin.interp import Interpreter, main as run_main
from melvin.parser import parse
from melvin.types import check_types

from _util import EXAMPLES, needs_boogie


# --------------------------------------------- F1: elidable spec clauses

def test_atomic_requires_elidable():
    prog = parse("atomic ensures x == 1 f() { x = 1; }\nvar int x non-mover;", "t.mml")
    spec = prog.find_func("f").spec
    assert isinstance(spec, A.AtomicSpec)
    assert isinstance(spec.requires, A.BoolLit) and spec.requires.value


def test_atomic_all_elided():
    prog = parse("atomic f() { skip; }", "t.mml")
    spec = prog.find_func("f").spec
    assert spec.requires.value and spec.ensures.value


def test_nonatomic_partial_clauses():
    prog = parse("guarantees true ensures true f() { yield; }", "t.mml")
    spec = prog.find_func("f").spec
    assert isinstance(spec, A.NonAtomicSpec)
    assert isinstance(spec.relies, A.BoolLit) and spec.relies.value


def test_func_keyword():
    prog = parse("func f() { yield; }", "t.mml")
    spec = prog.find_func("f").spec
    assert isinstance(spec, A.NonAtomicSpec)
    assert all(isinstance(c, A.BoolLit) and c.value
               for c in (spec.relies, spec.guarantees, spec.requires, spec.ensures))


@needs_boogie
def test_elided_spec_verifies_like_true():
    src = """
var int x  both-mover if m == tid;
lock m  write right-mover if \\old(m) == 0 && m == tid
        write left-mover  if \\old(m) == tid && m == 0;
atomic
ensures  x == \\old(x) + 1
inc() {
  acquire(m); t = x; t = t + 1; x = t; release(m);
}
thread { inc(); }
"""
    res = check_source(src, "elide.mml")
    assert res.ok, res.render()


# ------------------------------------------- F0: traces with source lines

def _unsafe_result():
    src = (EXAMPLES / "oracle_unsafe.mml").read_text()
    prog = parse(src, "oracle_unsafe.mml")
    check_types(prog)
    return Interpreter(prog, source=src).explore(want_trace=True)


def test_trace_steps_have_lines_and_source():
    r = _unsafe_result()
    assert r.wrong_reachable and r.trace
    step = r.trace[-1]
    assert step["line"] > 0
    assert "assert" in step["source"]
    assert "globals" in step["store"]


def test_trace_cli_output(capsys):
    rc = run_main([str(EXAMPLES / "oracle_unsafe.mml"), "--trace"])
    out = capsys.readouterr().out
    assert rc == 1
    assert "oracle_unsafe.mml:" in out


def test_json_output(capsys):
    rc = run_main([str(EXAMPLES / "oracle_unsafe.mml"), "--json"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 1
    assert out["result"] == "unsafe"
    assert out["trace"][-1]["line"] > 0


def test_json_safe(capsys):
    rc = run_main([str(EXAMPLES / "oracle_safe.mml"), "--json"])
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert out["result"] == "safe"
