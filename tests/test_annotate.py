"""Tests for melvin.annotate (per-statement mover letters).

Pure front-end: no Boogie required.
"""

from melvin.annotate import mover_annotations, render_listing
from melvin.parser import parse
from melvin.types import check_types

from _util import EXAMPLES


def annotate(name):
    src = (EXAMPLES / name).read_text()
    prog = parse(src, name)
    return src, mover_annotations(prog, check_types(prog))


def line_of(src, needle, nth=1):
    hits = [i for i, l in enumerate(src.splitlines(), 1) if needle in l]
    return hits[nth - 1]


# --------------------------------------------------------------- counter.mml

def test_counter_matches_paper_figure():
    src, ann = annotate("counter.mml")
    assert ann[line_of(src, "acquire(m);")] == "R"      # lock acquire
    assert ann[line_of(src, "release(m);")] == "L"      # lock release
    assert ann[line_of(src, "t = x;")] == "B"           # read under lock
    assert ann[line_of(src, "x = t;")] == "B"           # write under lock
    assert ann[line_of(src, "yield;")] == "Y"
    assert ann[line_of(src, "add();")] == "N"           # atomic call (default N)


def test_counter_locals_are_both_movers():
    src, ann = annotate("counter.mml")
    assert ann[line_of(src, "n = 2;")] == "B"
    assert ann[line_of(src, "result = t;")] == "B"


def test_declarations_and_comments_unannotated():
    src, ann = annotate("counter.mml")
    for needle in ("var int x", "lock m", "relies", "init x == 0"):
        assert line_of(src, needle) not in ann


def test_nonatomic_call_in_thread_has_no_letter():
    src, ann = annotate("counter.mml")
    assert line_of(src, "thread { client(); }") not in ann


# -------------------------------------------------------------- spinlock.mml

def test_spinlock_cas_loop_is_right_mover():
    # while (!cas(l, 0, tid)) ...: the committing cas is the 0 -> tid
    # transition, so the refined letter is R, not the clause join N.
    src, ann = annotate("spinlock.mml")
    assert ann[line_of(src, "while (!cas(l, 0, tid))")] == "R"


def test_spinlock_release_write_is_left_mover():
    # `l = 0` cannot be the acquire transition (l == tid), so only the
    # left-mover clause survives.
    src, ann = annotate("spinlock.mml")
    assert ann[line_of(src, "l = 0;")] == "L"


# -------------------------------------------------------------- racy_bad.mml

def test_racy_read_letter_is_static_clause_join():
    # The static letter reflects the spec (B); the race itself is caught
    # semantically by Boogie, not by the annotation.
    src, ann = annotate("racy_bad.mml")
    assert ann[18] == "B"


# ----------------------------------------------------------------- rendering

def test_render_listing_margins():
    src, ann = annotate("counter.mml")
    listing = render_listing(src, ann)
    lines = listing.splitlines()
    assert len(lines) == len(src.splitlines())
    assert any(l.startswith(" R | ") for l in lines)
    assert any(l.startswith(" L | ") for l in lines)
    assert any(l.startswith(" Y | ") for l in lines)
    assert any(l.startswith("   | ") for l in lines)     # unannotated lines
