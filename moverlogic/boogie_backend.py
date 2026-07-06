"""Boogie prover backend.

This module is the *only* place that knows about the external theorem prover.
It runs the Boogie verifier on a generated `.bpl` program and maps Boogie's
`file(line,col): Error ...` diagnostics back to the Mover Logic source using an
obligation table keyed by the line number of each emitted `assert`.

Note on "Boogie Python bindings": there is no official Python binding for the
Boogie verifier (the `boogie` package on PyPI is an unrelated Django library).
We therefore shell out to the Boogie executable.  The backend is deliberately
small and self-contained so a real binding could be dropped in behind
`BoogieBackend.verify` without touching the rest of the tool.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from .diagnostics import Diagnostic, Span

# Default wall-clock budget for a single Boogie run: 5 minutes.
DEFAULT_TIMEOUT = 300


@dataclass
class Obligation:
    """A single verification condition, tracked so failures map back to source."""
    span: Optional[Span]
    message: str
    good_note: str = ""      # optional note printed when this obligation holds


@dataclass
class Emitter:
    """Accumulates Boogie source and remembers where each obligation lives.

    `assert_` emits a Boogie assertion and records the obligation at the line it
    occupies, so a Boogie error at that line can be reported against the right
    Mover Logic construct.
    """
    lines: List[str] = field(default_factory=list)
    obligations: Dict[int, Obligation] = field(default_factory=dict)
    _indent: int = 0

    def line(self, text: str = "") -> int:
        self.lines.append(("  " * self._indent) + text if text else "")
        return len(self.lines)  # 1-based line number of what we just wrote

    def raw(self, text: str) -> int:
        self.lines.append(text)
        return len(self.lines)

    def indent(self) -> None:
        self._indent += 1

    def dedent(self) -> None:
        self._indent = max(0, self._indent - 1)

    def blank(self) -> None:
        self.lines.append("")

    def assert_(self, expr: str, span: Optional[Span], message: str, good_note: str = "") -> None:
        ln = self.line(f"assert {expr};")
        self.obligations[ln] = Obligation(span, message, good_note)

    def text(self) -> str:
        return "\n".join(self.lines) + "\n"


_ERROR_RE = re.compile(r"^(?P<file>.*?)\((?P<line>\d+),(?P<col>\d+)\):\s*(?:Error|error)\b.*?:?\s*(?P<msg>.*)$")
_SUMMARY_RE = re.compile(r"(?P<verified>\d+)\s+verified,\s+(?P<errors>\d+)\s+error")


class BoogieError(RuntimeError):
    pass


class BoogieBackend:
    def __init__(self, boogie_path: Optional[str] = None, extra_args: Optional[List[str]] = None):
        self.boogie_path = boogie_path or self._discover()
        self.extra_args = extra_args or []

    @staticmethod
    def _discover() -> str:
        env = os.environ.get("MOVERLOGIC_BOOGIE")
        if env and os.path.exists(env):
            return env
        for cand in ("boogie", "Boogie"):
            found = shutil.which(cand)
            if found:
                return found
        # Fall back to the Boogie shipped with the Synchronicity workspace.
        guesses = [
            os.path.expanduser(
                "~/other/Synchronicity/workspace/Synchronicity/boogie/Binaries/boogie"
            ),
        ]
        for g in guesses:
            if os.path.exists(g):
                return g
        raise BoogieError(
            "could not find the Boogie executable; set MOVERLOGIC_BOOGIE to its path"
        )

    def run_raw(self, bpl_path: str, timeout: int = 120) -> subprocess.CompletedProcess:
        cmd = [self.boogie_path, *self.extra_args, bpl_path]
        try:
            return subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout
            )
        except FileNotFoundError as e:  # pragma: no cover
            raise BoogieError(f"failed to launch Boogie ({self.boogie_path}): {e}")

    def verify(
        self,
        emitter: Emitter,
        bpl_path: str,
        timeout: int = DEFAULT_TIMEOUT,
    ) -> "VerifyResult":
        """Write the emitter's program to `bpl_path`, run Boogie, map results.

        If Boogie does not finish within `timeout` seconds it is killed and a
        result with `timed_out=True` (and `ok=False`) is returned rather than
        propagating the exception.
        """
        with open(bpl_path, "w") as f:
            f.write(emitter.text())
        try:
            proc = self.run_raw(bpl_path, timeout=timeout)
        except subprocess.TimeoutExpired as e:
            partial = ""
            if e.stdout:
                partial = e.stdout if isinstance(e.stdout, str) else e.stdout.decode(errors="replace")
            return VerifyResult(
                ok=False,
                diagnostics=[Diagnostic(
                    None,
                    f"verification timed out after {timeout}s "
                    f"(raise the limit with --timeout)")],
                verified=0,
                n_errors=0,
                raw_output=partial,
                timed_out=True,
            )
        return self._interpret(proc, emitter, bpl_path)

    def _interpret(self, proc, emitter: Emitter, bpl_path: str) -> "VerifyResult":
        out = (proc.stdout or "") + "\n" + (proc.stderr or "")
        diagnostics: List[Diagnostic] = []
        n_errors = 0
        verified = None
        seen_lines = set()
        base = os.path.basename(bpl_path)
        for raw in out.splitlines():
            m = _SUMMARY_RE.search(raw)
            if m:
                verified = int(m.group("verified"))
                continue
            m = _ERROR_RE.match(raw.strip())
            if m and (base in m.group("file") or m.group("file").endswith(".bpl")):
                bline = int(m.group("line"))
                if bline in seen_lines:
                    continue
                seen_lines.add(bline)
                oblig = self._nearest_obligation(emitter, bline)
                if oblig is not None:
                    diagnostics.append(Diagnostic(oblig.span, oblig.message))
                else:
                    diagnostics.append(
                        Diagnostic(None, f"Boogie error at {base}({bline}): {m.group('msg')}")
                    )
                n_errors += 1

        # Detect Boogie parse/type errors (no summary line, unexpected output).
        tool_failure = None
        if verified is None and "error" in out.lower() and not diagnostics:
            tool_failure = out.strip()

        return VerifyResult(
            ok=(n_errors == 0 and tool_failure is None),
            diagnostics=diagnostics,
            verified=verified or 0,
            n_errors=n_errors,
            raw_output=out,
            tool_failure=tool_failure,
            timed_out=False,
        )

    @staticmethod
    def _nearest_obligation(emitter: Emitter, bline: int) -> Optional[Obligation]:
        if bline in emitter.obligations:
            return emitter.obligations[bline]
        # Boogie sometimes reports the enclosing block line; take the nearest
        # obligation at or before the reported line.
        best = None
        for ln in sorted(emitter.obligations):
            if ln <= bline:
                best = emitter.obligations[ln]
            else:
                break
        return best


@dataclass
class VerifyResult:
    ok: bool
    diagnostics: List[Diagnostic]
    verified: int
    n_errors: int
    raw_output: str
    tool_failure: Optional[str] = None
    timed_out: bool = False
