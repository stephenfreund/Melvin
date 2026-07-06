"""End-to-end and unit tests for the Mover Logic verifier.

Tests that need the Boogie prover are skipped automatically if Boogie cannot be
located (set MOVERLOGIC_BOOGIE or put `boogie` on PATH to run them).
"""

import os
import pathlib

import pytest

from moverlogic import effects as E
from moverlogic.parser import parse
from moverlogic.types import check_types
from moverlogic.boogie_backend import BoogieBackend, BoogieError
from moverlogic.checker import check_source

EXAMPLES = pathlib.Path(__file__).resolve().parent.parent / "examples"


def boogie_available() -> bool:
    try:
        BoogieBackend()
        return True
    except BoogieError:
        return False


needs_boogie = pytest.mark.skipif(not boogie_available(), reason="Boogie not found")


# --------------------------------------------------------------------------
# Effect algebra (transcribed identities from the paper)
# --------------------------------------------------------------------------

def test_effect_seq_identities():
    assert E.seq(E.R, E.L) == E.N          # right then left = non-mover
    assert E.seq(E.N, E.N) == E.E          # two non-movers = error
    assert E.seq(E.R, E.B) == E.R
    assert E.seq(E.Y, E.N) == E.L
    assert E.seq(E.L, E.R) == E.E


def test_effect_star_and_join():
    assert E.star(E.N) == E.E
    assert E.star(E.R) == E.R
    assert E.join(E.R, E.L) == E.N
    assert E.leq(E.B, E.N) and not E.leq(E.N, E.B)


def test_add_body_and_spinloop_effects():
    # acquire;read;write;release = R;B;B;L = N   (an atomic non-mover)
    assert E.seq_all([E.R, E.B, E.B, E.L]) == E.N
    # spin loop:  (failed-cas B ; skip B)* ; successful-cas R  =  R
    assert E.seq(E.star(E.seq(E.B, E.B)), E.R) == E.R


# --------------------------------------------------------------------------
# Front end
# --------------------------------------------------------------------------

def test_parse_and_typecheck_counter():
    src = (EXAMPLES / "counter.mml").read_text()
    prog = parse(src, "counter.mml")
    ti = check_types(prog)
    assert set(ti.globals) == {"x", "m"}
    assert "m" in ti.lock_names
    add = prog.find_func("add")
    kinds = {ti.assign_kind[id(s)][0] for s in add.body if type(s).__name__ == "Assign"}
    assert kinds == {"read", "write", "local"}


def test_atomic_recursion_rejected():
    src = """
    atomic requires true ensures true f() { f(); }
    """
    from moverlogic.diagnostics import TypeError_
    with pytest.raises(TypeError_):
        check_types(parse(src))


def test_global_read_in_write_rejected():
    src = """
    var int x  both-mover if true;
    var int y  both-mover if true;
    atomic requires true ensures true f() { x = y; }
    """
    from moverlogic.diagnostics import TypeError_
    with pytest.raises(TypeError_):
        check_types(parse(src))


# --------------------------------------------------------------------------
# End-to-end verification of the paper's examples
# --------------------------------------------------------------------------

VERIFYING = ["counter.mml", "counter_client2.mml", "spinlock.mml",
             "queue.mml", "stack.mml"]


@needs_boogie
@pytest.mark.parametrize("name", VERIFYING)
def test_examples_verify(name):
    result = check_source((EXAMPLES / name).read_text(), name)
    assert result.ok, result.render()


@needs_boogie
def test_racy_example_is_rejected():
    result = check_source((EXAMPLES / "racy_bad.mml").read_text(), "racy_bad.mml")
    assert not result.ok
    assert any("race" in d.message for d in result.diagnostics)
    # the error maps to the read of x
    assert any(d.span and d.span.start.line == 18 for d in result.diagnostics)


# --------------------------------------------------------------------------
# Mutation tests: verified programs must fail when broken
# --------------------------------------------------------------------------

@needs_boogie
def test_missing_yield_breaks_reducibility():
    src = (EXAMPLES / "counter.mml").read_text()
    # remove the middle yield between the two add() calls in client()
    lines = src.splitlines()
    out, seen = [], 0
    for l in lines:
        if l.strip() == "yield;":
            seen += 1
            if seen == 2:
                continue
        out.append(l)
    result = check_source("\n".join(out), "no_yield.mml")
    assert not result.ok
    assert any("reducib" in d.message for d in result.diagnostics)


@needs_boogie
def test_wrong_postcondition_fails():
    src = (EXAMPLES / "counter.mml").read_text().replace(
        "x == \\old(x) + n", "x == \\old(x) + 1")
    result = check_source(src, "wrongpost.mml")
    assert not result.ok


@needs_boogie
def test_bad_mover_spec_invalidity():
    # x's mover depends on x itself, which another thread can change -> validity(3)
    src = """
    var int x  both-mover if x == 0;
    atomic requires true ensures true f() { t = x; }
    """
    result = check_source(src, "badspec.mml")
    assert not result.ok
    assert any("validity" in d.message or "invalid" in d.message
               for d in result.diagnostics)
