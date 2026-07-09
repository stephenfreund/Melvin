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


# ---------------------------------------- heap-aware feature extensions

def test_finals_isomorphic_heaps_collapse():
    src = """
class Cell { var int v  non-mover; }
var Cell shared  non-mover;
func w() {
  yield;
  a = new Cell;
  a.v = 7;
  yield;
  shared = a;
  yield;
}
init shared == null;
thread { w(); }
thread { w(); }
"""
    r = _explore(src)
    # Each thread still holds its own cell in the local `a`, so both cells are
    # live (rooted at the locals) and are labelled with their allocating
    # thread.  Address renumbering still collapses the many interleavings, but
    # the two outcomes -- t1 published vs t2 published -- stay distinct because
    # the published cell (#1) records a different allocator in each.
    assert r.finals_complete
    assert len(r.finals) == 2
    for f in r.finals:
        assert f["globals"] == {"shared": "#1"}
        assert [(o["id"], o["class"], o["fields"]) for o in f["objects"]] == [
            ("#1", "Cell", {"v": 7}), ("#2", "Cell", {"v": 7})]
    # #1 is the published cell; across the two finals it is allocated by each
    # thread in turn.
    assert sorted(f["objects"][0]["allocated_by"] for f in r.finals) == [1, 2]


def test_finals_root_at_locals_identify_allocator():
    # Objects a thread allocates and still holds via a local appear in the
    # finals even with no globals, each tagged with its allocating thread.
    src = (EXAMPLES / "obj_counter_client.mml").read_text()
    r = _explore(src)
    assert r.finals_complete and len(r.finals) == 1
    objs = r.finals[0]["objects"]
    assert r.finals[0]["globals"] == {}
    assert sorted((o["class"], o["allocated_by"]) for o in objs) == [
        ("Counter", 1), ("Counter", 2)]


def test_finals_true_garbage_still_collapses():
    # An object no root can reach (the local is overwritten with null) is
    # dropped, so the owner-blind collapse of unreachable garbage still holds.
    src = """
class Cell { var int v  non-mover; }
var Cell shared  non-mover;
func w() {
  yield;
  a = new Cell;
  a.v = 7;
  shared = a;
  a = null;
  yield;
}
init shared == null;
thread { w(); }
thread { w(); }
"""
    r = _explore(src)
    # The loser's cell is unreachable (its local is null) and dropped, so every
    # final has exactly ONE object -- the published cell.  The two finals differ
    # only by which thread published last (recorded as the allocator).
    assert r.finals_complete and len(r.finals) == 2
    for f in r.finals:
        assert f["globals"] == {"shared": "#1"}
        assert [(o["id"], o["fields"]) for o in f["objects"]] == [("#1", {"v": 7})]
    assert sorted(f["objects"][0]["allocated_by"] for f in r.finals) == [1, 2]


def test_trace_store_shows_objects():
    src = (EXAMPLES / "obj_oracle_unsafe.mml").read_text()
    prog = parse(src, "t.mml")
    check_types(prog)
    r = Interpreter(prog, source=src).explore(want_trace=True)
    assert r.wrong_reachable
    last = r.trace[-1]["store"]
    assert any(o["class"] == "Cell" for o in last["objects"])


def test_line_details_field_lock_flow():
    from melvin.annotate import line_details
    src = (EXAMPLES / "obj_counter.mml").read_text()
    prog = parse(src, "t.mml")
    ti = check_types(prog)
    by = {d["line"]: d for d in line_details(prog, ti, src)}
    lines = src.splitlines()
    in_cs = [n for n, txt in enumerate(lines, 1) if "t = this.x" in txt][0]
    assert by[in_cs]["store"]["this.m"] == "tid"
    assert by[in_cs]["explain"]["clauses"][0]["status"] == "matches"


@needs_boogie
def test_heap_counterexample_rows():
    src = (EXAMPLES / "obj_counter.mml").read_text().replace(
        "assert r == 2;", "assert r == 3;")
    res = check_source(src, "m.mml", counterexample=True)
    assert not res.ok
    rows = dict(res.diagnostics[0].model or [])
    assert any(k.endswith(".x") for k in rows), rows


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
    entries, funcs = _parse_model_block(block)
    rows = dict(model_table(entries, funcs))
    assert rows["tid"] == "1"
    assert rows["eff"] == "N"          # highest incarnation, decoded
    assert rows["x"] == "-2"
    assert rows["t"] == "0"
    assert "\\old(x)" not in rows      # equal to current value, so elided


def test_model_table_heap_rows():
    from melvin.boogie_backend import model_table, _parse_model_block
    block = ["tid -> 1",
             "v_f_Counter_x -> |T@[Counter]Int!val!1|",
             "Select_[Counter]$int -> {",
             "  |T@[Counter]Int!val!1| T@Counter!val!0 -> 2",
             "  else -> 0",
             "}"]
    entries, funcs = _parse_model_block(block)
    rows = dict(model_table(entries, funcs, {"Counter": {"x": "int"}}))
    assert rows["Counter#0.x"] == "2"


def test_model_table_missing_values_labeled():
    # In-scope variables the model never mentions surface as explicit `?`
    # rows instead of silently disappearing from the table.
    from melvin.boogie_backend import model_table, _parse_model_block
    block = ["tid -> 1", "v_x -> 3"]
    entries, funcs = _parse_model_block(block)
    rows = model_table(entries, funcs,
                       in_scope=frozenset({"x", "y", "m"}))
    d = dict(rows)
    assert d["x"] == "3"
    assert d["y"] == "?" and d["m"] == "?"
    # without a scope there is no variable universe, so no `?` rows
    assert "?" not in dict(model_table(entries, funcs)).values()


def test_counterexample_render_notes_unknowns():
    from melvin.diagnostics import Diagnostic
    d = Diagnostic(None, "boom", model=[("x", "3"), ("y", "?")])
    out = d.render()
    assert "y = ?" in out
    assert "not constrained" in out


def test_finals_in_json(capsys):
    run_main([str(EXAMPLES / "oracle_safe.mml"), "--json"])
    out = json.loads(capsys.readouterr().out)
    assert out["finals"] == [{"globals": {"m": 0, "x": 4}, "objects": []}]
    assert out["finals_complete"] is True
