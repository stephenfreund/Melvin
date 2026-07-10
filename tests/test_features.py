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


# --------------------------------------------- F3: final-state enumeration

def _explore(src, **kw):
    prog = parse(src, "t.mml")
    check_types(prog)
    return Interpreter(prog, source=src, **kw).explore()


def test_single_final_state():
    src = (EXAMPLES / "oracle_safe.mml").read_text()
    r = _explore(src)
    assert r.finals_complete
    assert len(r.finals) == 1
    assert r.finals[0]["globals"] == {"m": 0, "x": 4}


def test_racing_writers_two_finals():
    src = """
var int x  non-mover;
func w1() { yield; x = 1; yield; }
func w2() { yield; x = 2; yield; }
thread { w1(); }
thread { w2(); }
"""
    r = _explore(src)
    assert r.finals_complete
    assert sorted(f["globals"]["x"] for f in r.finals) == [1, 2]


def test_finals_incomplete_when_bounded():
    src = (EXAMPLES / "oracle_safe.mml").read_text()
    prog = parse(src, "t.mml")
    check_types(prog)
    r = Interpreter(prog, max_states=5, source=src).explore()
    assert r.hit_bound and not r.finals_complete


def test_finals_cli_output(capsys):
    rc = run_main([str(EXAMPLES / "oracle_safe.mml")])
    out = capsys.readouterr().out
    assert rc == 0
    assert "1 distinct final store(s):" in out
    assert "x = 4" in out


def test_no_finals_flag(capsys):
    run_main([str(EXAMPLES / "oracle_safe.mml"), "--no-finals"])
    out = capsys.readouterr().out
    assert "final store" not in out


# -------------------------------- F2: explanations + schematic stores

def test_line_details_explain_acquire():
    from melvin.annotate import line_details
    src = (EXAMPLES / "counter.mml").read_text()
    prog = parse(src, "counter.mml")
    ti = check_types(prog)
    by_line = {d["line"]: d for d in line_details(prog, ti, src)}
    acq = next(d for d in by_line.values()
               if d["explain"] and d["explain"]["action"].startswith("acquire"))
    assert acq["effect"] == "R"
    assert "0 → tid" in acq["explain"]["transition"]
    statuses = {c["status"] for c in acq["explain"]["clauses"]}
    assert "matches" in statuses and "ruled out" in statuses


def test_line_details_store_tracks_lock():
    from melvin.annotate import line_details
    src = (EXAMPLES / "counter.mml").read_text()
    prog = parse(src, "counter.mml")
    ti = check_types(prog)
    by_line = {d["line"]: d for d in line_details(prog, ti, src)}
    # inside add()'s critical section the lock is known held
    lines = src.splitlines()
    in_cs = [n for n, txt in enumerate(lines, 1) if "t = x" in txt][0]
    assert by_line[in_cs]["store"]["m"] == "tid"
    # a read under the held lock has its clause marked as matching
    assert by_line[in_cs]["explain"]["clauses"][0]["status"] == "matches"


def test_line_details_yield_drops_values_keeps_nothing_unheld():
    from melvin.annotate import line_details
    src = """
var int x  non-mover;
lock m  write right-mover if \\old(m) == 0 && m == tid
        write left-mover  if \\old(m) == tid && m == 0;
func f() {
  yield;
  x = 1;
  yield;
  x = 2;
  yield;
}
thread { f(); }
"""
    prog = parse(src, "t.mml")
    ti = check_types(prog)
    by_line = {d["line"]: d for d in line_details(prog, ti, src)}
    # before `x = 2` (line 9), the previous write of 1 was dropped at the yield
    assert by_line[9]["store"]["x"] == "?"


# --------------------------------------------- F4: Boogie counterexamples

BAD_POST = """
var int x  both-mover if m == tid;
lock m  write right-mover if \\old(m) == 0 && m == tid
        write left-mover  if \\old(m) == tid && m == 0;
atomic
ensures  x == \\old(x) + 1
inc() {
  acquire(m); t = x; t = t + 2; x = t; release(m);
}
thread { inc(); }
"""


@needs_boogie
def test_counterexample_attached_on_request():
    res = check_source(BAD_POST, "bad.mml", counterexample=True)
    assert not res.ok
    d = res.diagnostics[0]
    assert d.model, "expected counterexample rows"
    names = [n for n, _v in d.model]
    assert "tid" in names and "eff" in names
    assert any(n == "x" for n in names)


@needs_boogie
def test_no_counterexample_by_default():
    res = check_source(BAD_POST, "bad.mml")
    assert not res.ok
    assert res.diagnostics[0].model is None


@needs_boogie
def test_counterexample_rendered():
    res = check_source(BAD_POST, "bad.mml", counterexample=True)
    out = res.render()
    assert "counterexample:" in out
    assert "eff = " in out


def test_model_table_mapping():
    from melvin.boogie_backend import model_table, _parse_model_block
    block = ["tid -> 1", "eff@0 -> 2", "eff@1 -> 4", "v_x -> (- 2)",
             "v_t@0 -> 0", "o_x -> (- 2)", "Nil -> T@List!val!0",
             "cons -> {", "  else -> T@List!val!0", "}"]
    rows = dict(model_table(_parse_model_block(block)))
    assert rows["tid"] == "1"
    assert rows["eff"] == "N"          # highest incarnation, decoded
    assert rows["x"] == "-2"
    assert rows["t"] == "0"
    assert "\\old(x)" not in rows      # equal to current value, so elided


def test_model_table_missing_values_labeled():
    # In-scope variables the model never mentions surface as explicit `?`
    # rows instead of silently disappearing from the table.
    from melvin.boogie_backend import model_table, _parse_model_block
    block = ["tid -> 1", "v_x -> 3"]
    rows = model_table(_parse_model_block(block),
                       in_scope=frozenset({"x", "y", "m"}))
    d = dict(rows)
    assert d["x"] == "3"
    assert d["y"] == "?" and d["m"] == "?"
    # without a scope there is no variable universe, so no `?` rows
    assert "?" not in dict(model_table(_parse_model_block(block))).values()


def test_counterexample_render_notes_unknowns():
    from melvin.diagnostics import Diagnostic
    d = Diagnostic(None, "boom", model=[("x", "3"), ("y", "?")])
    out = d.render()
    assert "y = ?" in out
    assert "not constrained" in out


def test_finals_in_json(capsys):
    run_main([str(EXAMPLES / "oracle_safe.mml"), "--json"])
    out = json.loads(capsys.readouterr().out)
    assert len(out["finals"]) == 1
    final = out["finals"][0]
    assert final["globals"] == {"m": 0, "x": 4}
    assert final["objects"] == []
    # each final carries a representative interleaving that reaches it
    assert final["trace"]
    assert out["finals_complete"] is True


def test_trace_stores_show_call_stack():
    # trace-step stores show each thread as a stack of call frames, each
    # frame holding its own scope's locals
    src = (EXAMPLES / "oracle_safe.mml").read_text()
    r = _explore(src)
    steps = r.finals[0]["trace"]
    deep = [s for s in steps
            if [f["fn"] for f in s["store"]["threads"][str(s["tid"])]]
            == ["thread", "w", "add2"]]
    assert deep, "expected steps inside thread -> w -> add2"
    inner = deep[-1]["store"]["threads"][str(deep[-1]["tid"])][-1]
    assert inner["fn"] == "add2"
    assert "t" in inner["locals"]


def test_trace_has_call_and_return_steps():
    # traces mark calls ("call") and returns ("return from f()" at the
    # call-site line); in a completed trace they balance
    src = (EXAMPLES / "oracle_safe.mml").read_text()
    r = _explore(src)
    steps = r.finals[0]["trace"]
    kinds = [s["kind"] for s in steps]
    assert "call" in kinds and "return" in kinds
    assert kinds.count("call") == kinds.count("return")
    ret = next(s for s in steps if s["kind"] == "return")
    assert ret["source"].startswith("return from ")
    assert ret["line"] > 0
    # indentation data: a callee's steps are one level deeper than the call
    i = kinds.index("call")
    assert steps[i + 1]["depth"] == steps[i]["depth"] + 1
    # the matching return closes at the callee's depth
    assert ret["depth"] >= 1


def test_callee_locals_do_not_clobber_caller():
    # every call saves/restores its whole frame, so a callee writing a
    # same-named local cannot change the caller's value
    src = """
var int x  non-mover;
func g() { t = 99; x = t; }
func f() {
  yield;
  t = 1;
  g();
  assert t == 1;
  yield;
}
thread { f(); }
"""
    r = _explore(src)
    assert not r.wrong_reachable
    # and while g runs, f's frame still shows its own t
    steps = r.finals[0]["trace"]
    in_g = next(s for s in steps
                if [f["fn"] for f in s["store"]["threads"]["1"]][-1] == "g"
                and s["store"]["threads"]["1"][-1]["locals"].get("t") == 99)
    assert in_g["store"]["threads"]["1"][-2]["locals"]["t"] == 1


def test_finals_have_representative_traces():
    src = """
var int x  non-mover;
func w1() { yield; x = 1; yield; }
func w2() { yield; x = 2; yield; }
thread { w1(); }
thread { w2(); }
"""
    r = _explore(src)
    assert r.finals_complete and len(r.finals) == 2
    for f in r.finals:
        steps = f["trace"]
        assert steps, "every final should carry a trace"
        for s in steps:
            assert s["tid"] in (1, 2) and "source" in s and "store" in s
        # replaying the trace ends in this very final store
        assert steps[-1]["store"]["globals"] == f["globals"]


def test_finals_trace_in_cli_output(capsys):
    rc = run_main([str(EXAMPLES / "oracle_safe.mml"), "--trace"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "via:" in out
    assert "oracle_safe.mml:" in out
