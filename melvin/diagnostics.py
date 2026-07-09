"""Source positions, spans, and diagnostics used throughout the tool.

Every AST node carries a `Span` so that verification failures reported by
Boogie can be mapped back to the exact location in the original Mover Logic
source (see `boogie_backend` and `checker`).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional


@dataclass(frozen=True)
class Position:
    line: int          # 1-based
    col: int           # 1-based

    def __str__(self) -> str:
        return f"{self.line}:{self.col}"


@dataclass(frozen=True)
class Span:
    filename: str
    start: Position
    end: Position

    def __str__(self) -> str:
        return f"{self.filename}:{self.start}"

    @staticmethod
    def merge(a: "Span", b: "Span") -> "Span":
        return Span(a.filename, a.start, b.end)


# A sentinel span for synthesised nodes with no real source location.
NO_SPAN = Span("<synthetic>", Position(0, 0), Position(0, 0))


class MelvinError(Exception):
    """Base class for all user-facing errors (lexing, parsing, typing, ...)."""

    def __init__(self, message: str, span: Optional[Span] = None):
        self.message = message
        self.span = span
        super().__init__(self.render())

    def render(self) -> str:
        loc = f"{self.span}: " if self.span else ""
        return f"{loc}error: {self.message}"


class LexError(MelvinError):
    pass


class ParseError(MelvinError):
    pass


class TypeError_(MelvinError):
    pass


@dataclass
class Diagnostic:
    """A verification result mapped back to source."""

    span: Optional[Span]
    message: str
    kind: str = "error"          # "error" | "warning" | "note"
    related: List["Diagnostic"] = field(default_factory=list)
    # Source-level counterexample rows [(name, value), ...] mapped from the
    # Boogie model, present only when model printing was requested.
    model: Optional[List] = None

    def render(self, source_lines: Optional[List[str]] = None) -> str:
        loc = f"{self.span}: " if self.span else ""
        out = f"{loc}{self.kind}: {self.message}"
        if source_lines and self.span and self.span is not NO_SPAN:
            ln = self.span.start.line
            if 1 <= ln <= len(source_lines):
                out += "\n    " + source_lines[ln - 1].rstrip("\n")
                out += "\n    " + " " * (self.span.start.col - 1) + "^"
        if self.model:
            out += "\n    counterexample:"
            for name, value in self.model:
                out += f"\n      {name} = {value}"
            if any(v == "?" for _n, v in self.model):
                out += "\n      (? = not constrained by the failing path)"
        for r in self.related:
            out += "\n  " + r.render()
        return out
