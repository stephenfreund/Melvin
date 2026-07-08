"""Hand-written lexer for the Mover Logic Language (MLL) surface syntax."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

from .diagnostics import LexError, Position, Span

KEYWORDS = {
    "var", "lock", "thread", "func", "init", "invariant",
    "atomic", "relies", "guarantees", "requires", "ensures",
    "read", "write",
    "both-mover", "right-mover", "left-mover", "non-mover",
    "if", "else", "while", "skip", "yield", "wrong", "assert",
    "acquire", "release", "cas",
    "true", "false", "tid", "result",
    "int", "bool", "lock_t", "value",
    "forall", "exists", "in",
    "head", "tail", "Nil", "None", "Some", "even",
    "class", "new", "null", "this", "guarded_by",
}

# Multi-character operators, longest first.
OPERATORS = [
    "==>", "<==>",
    "&&", "||", "==", "!=", "<=", ">=", "::", "->",
    "=", "<", ">", "+", "-", "*", "/", "%", "!", ":",
    "(", ")", "{", "}", "[", "]", ",", ";", ".", "@",
]


@dataclass
class Token:
    kind: str      # "kw", "id", "num", "op", "eof"
    text: str
    span: Span

    def __repr__(self) -> str:  # pragma: no cover
        return f"Token({self.kind}, {self.text!r}, {self.span})"


class Lexer:
    def __init__(self, source: str, filename: str = "<input>"):
        self.src = source
        self.filename = filename
        self.i = 0
        self.line = 1
        self.col = 1

    def _pos(self) -> Position:
        return Position(self.line, self.col)

    def _advance(self, n: int = 1) -> None:
        for _ in range(n):
            if self.i < len(self.src) and self.src[self.i] == "\n":
                self.line += 1
                self.col = 1
            else:
                self.col += 1
            self.i += 1

    def _span(self, start: Position) -> Span:
        return Span(self.filename, start, self._pos())

    def tokens(self) -> List[Token]:
        toks: List[Token] = []
        while True:
            self._skip_trivia()
            if self.i >= len(self.src):
                toks.append(Token("eof", "", self._span(self._pos())))
                return toks
            toks.append(self._next_token())

    def _skip_trivia(self) -> None:
        while self.i < len(self.src):
            c = self.src[self.i]
            if c in " \t\r\n":
                self._advance()
            elif self.src.startswith("//", self.i):
                while self.i < len(self.src) and self.src[self.i] != "\n":
                    self._advance()
            elif self.src.startswith("/*", self.i):
                self._advance(2)
                while self.i < len(self.src) and not self.src.startswith("*/", self.i):
                    self._advance()
                self._advance(2)
            else:
                return

    def _next_token(self) -> Token:
        start = self._pos()
        c = self.src[self.i]

        # \old(...) is written with a backslash; treat "\old" as a keyword-ish id.
        if c == "\\":
            self._advance()
            name = self._read_ident_body()
            text = "\\" + name
            if name not in ("old", "result"):
                raise LexError(f"unknown escape \\{name}", self._span(start))
            return Token("kw", "\\" + name, self._span(start))

        if c.isalpha() or c == "_":
            word = self._read_ident_body()
            # allow hyphenated mover keywords like both-mover
            if self.i < len(self.src) and self.src[self.i] == "-":
                # lookahead: only join if it forms a known keyword
                save_i, save_line, save_col = self.i, self.line, self.col
                self._advance()
                tail = self._read_ident_body()
                candidate = f"{word}-{tail}"
                if candidate in KEYWORDS:
                    return Token("kw", candidate, self._span(start))
                # roll back
                self.i, self.line, self.col = save_i, save_line, save_col
            kind = "kw" if word in KEYWORDS else "id"
            return Token(kind, word, self._span(start))

        if c.isdigit():
            num = ""
            while self.i < len(self.src) and self.src[self.i].isdigit():
                num += self.src[self.i]
                self._advance()
            return Token("num", num, self._span(start))

        for op in OPERATORS:
            if self.src.startswith(op, self.i):
                self._advance(len(op))
                return Token("op", op, self._span(start))

        raise LexError(f"unexpected character {c!r}", self._span(start))

    def _read_ident_body(self) -> str:
        word = ""
        while self.i < len(self.src) and (self.src[self.i].isalnum() or self.src[self.i] == "_"):
            word += self.src[self.i]
            self._advance()
        return word


def lex(source: str, filename: str = "<input>") -> List[Token]:
    return Lexer(source, filename).tokens()
