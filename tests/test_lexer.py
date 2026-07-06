"""Unit tests for melvin.lexer."""

import pytest

from melvin.lexer import lex, Lexer, KEYWORDS
from melvin.diagnostics import LexError


def kinds_texts(src):
    toks = lex(src)
    return [(t.kind, t.text) for t in toks if t.kind != "eof"]


def test_empty_and_whitespace_only():
    assert lex("")[-1].kind == "eof"
    assert lex("   \n\t ")[-1].kind == "eof"
    assert len(lex("")) == 1           # just EOF


def test_identifiers_and_keywords():
    assert kinds_texts("foo bar_baz x1") == [("id", "foo"), ("id", "bar_baz"), ("id", "x1")]
    assert kinds_texts("var lock if while") == [
        ("kw", "var"), ("kw", "lock"), ("kw", "if"), ("kw", "while")]


def test_numbers():
    assert kinds_texts("0 42 1000") == [("num", "0"), ("num", "42"), ("num", "1000")]


def test_hyphenated_mover_keywords():
    for kw in ("both-mover", "right-mover", "left-mover", "non-mover"):
        assert kinds_texts(kw) == [("kw", kw)]


def test_hyphen_not_forming_keyword_rolls_back():
    # `foo-bar` is not a keyword: lexes as id, op '-', id
    assert kinds_texts("foo-bar") == [("id", "foo"), ("op", "-"), ("id", "bar")]


def test_multichar_operators_longest_match():
    assert kinds_texts("==> <==> == != <= >= && || ::") == [
        ("op", "==>"), ("op", "<==>"), ("op", "=="), ("op", "!="),
        ("op", "<="), ("op", ">="), ("op", "&&"), ("op", "||"), ("op", "::")]


def test_single_char_operators():
    assert kinds_texts("= < > + - * / % ! ( ) { } [ ] , ; . @") == [
        ("op", c) for c in "= < > + - * / % ! ( ) { } [ ] , ; . @".split()]


def test_line_comment():
    assert kinds_texts("a // comment here\n b") == [("id", "a"), ("id", "b")]


def test_block_comment():
    assert kinds_texts("a /* multi\nline */ b") == [("id", "a"), ("id", "b")]


def test_old_and_result_escapes():
    assert kinds_texts(r"\old \result") == [("kw", "\\old"), ("kw", "\\result")]


def test_unknown_escape_raises():
    with pytest.raises(LexError):
        lex(r"\bogus")


def test_unexpected_character_raises():
    with pytest.raises(LexError):
        lex("a $ b")


def test_span_positions():
    toks = lex("ab\n  cd")
    ab, cd = toks[0], toks[1]
    assert (ab.span.start.line, ab.span.start.col) == (1, 1)
    assert (cd.span.start.line, cd.span.start.col) == (2, 3)


def test_eof_always_present():
    toks = lex("x")
    assert toks[-1].kind == "eof"
    assert toks[-1].text == ""


def test_keywords_set_membership():
    assert "both-mover" in KEYWORDS
    assert "acquire" in KEYWORDS and "yield" in KEYWORDS
