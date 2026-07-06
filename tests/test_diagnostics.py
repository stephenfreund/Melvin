"""Unit tests for melvin.diagnostics."""

import pytest

from melvin.diagnostics import (
    Position, Span, NO_SPAN, MelvinError, LexError, ParseError, TypeError_,
    Diagnostic,
)


def test_position_str():
    assert str(Position(3, 7)) == "3:7"


def test_span_str_and_merge():
    a = Span("f.mml", Position(1, 1), Position(1, 5))
    b = Span("f.mml", Position(2, 1), Position(2, 9))
    assert str(a) == "f.mml:1:1"
    merged = Span.merge(a, b)
    assert merged.start == Position(1, 1)
    assert merged.end == Position(2, 9)
    assert merged.filename == "f.mml"


def test_no_span_sentinel():
    assert NO_SPAN.filename == "<synthetic>"
    assert NO_SPAN.start == Position(0, 0)


def test_error_render_with_and_without_span():
    span = Span("f.mml", Position(4, 2), Position(4, 3))
    e = MelvinError("boom", span)
    assert e.render() == "f.mml:4:2: error: boom"
    assert "error: boom" in str(e)
    e2 = MelvinError("no location")
    assert e2.render() == "error: no location"


def test_error_subclasses():
    for cls in (LexError, ParseError, TypeError_):
        e = cls("msg")
        assert isinstance(e, MelvinError)


def test_diagnostic_render_plain():
    d = Diagnostic(None, "something", kind="warning")
    assert d.render() == "warning: something"


def test_diagnostic_render_with_source_caret():
    span = Span("f.mml", Position(2, 3), Position(2, 4))
    src = ["first line", "  x = y;", "third"]
    d = Diagnostic(span, "bad", kind="error")
    out = d.render(src)
    assert "f.mml:2:3: error: bad" in out
    assert "  x = y;" in out
    # caret sits under column 3
    caret_line = out.splitlines()[-1]
    assert caret_line.strip() == "^"
    assert caret_line.index("^") == 4 + (3 - 1)  # 4-space indent + (col-1)


def test_diagnostic_render_ignores_out_of_range_line():
    span = Span("f.mml", Position(99, 1), Position(99, 2))
    d = Diagnostic(span, "x")
    out = d.render(["only one line"])
    assert "^" not in out              # no source snippet emitted


def test_diagnostic_related():
    span = Span("f.mml", Position(1, 1), Position(1, 2))
    child = Diagnostic(None, "see also")
    d = Diagnostic(span, "main", related=[child])
    out = d.render()
    assert "main" in out and "see also" in out
