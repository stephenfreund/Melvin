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
from typing import Dict, List, Optional, Tuple

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

# Boogie model entries: `name -> value` (function/map entries open a `{` block).
_MODEL_ENTRY_RE = re.compile(r"^(?P<name>\S+)\s+->\s+(?P<value>.*)$")
# Opaque model values like T@List!val!0.
_OPAQUE_RE = re.compile(r"^T@(?P<type>\w+)!val!(?P<n>\d+)$")

# Effect codes (prelude.py) back to mover letters, for eff/mv model values.
_EFF_LETTER = {0: "Y", 1: "B", 2: "R", 3: "L", 4: "N", 5: "E"}


def _parse_model_block(lines: List[str]) -> Dict[str, str]:
    """Parse the scalar entries of a `*** MODEL` block into name -> value.
    Function/map entries (`name -> { ... }`) are skipped."""
    out: Dict[str, str] = {}
    depth = 0
    for raw in lines:
        line = raw.strip()
        if depth > 0:
            depth -= line.count("}")
            depth += line.count("{")
            continue
        m = _MODEL_ENTRY_RE.match(line)
        if not m:
            continue
        value = m.group("value").strip()
        if value.endswith("{"):
            depth = 1
            continue
        out[m.group("name")] = value
    return out


def _clean_value(v: str) -> str:
    """Normalize a Boogie model value for display."""
    v = v.strip()
    m = re.match(r"^\(-\s*(\d+)\)$", v)
    if m:
        return f"-{m.group(1)}"
    m = _OPAQUE_RE.match(v)
    if m:
        return f"{m.group('type')}#{m.group('n')}"
    return v


def _last_incarnation(raw: Dict[str, str], base: str) -> Optional[str]:
    """Boogie models list SSA incarnations (`v_x`, `v_x@0`, `v_x@1`, ...);
    the highest incarnation is the value at the end of the failing path."""
    best_k, best = -1, None
    for name, value in raw.items():
        stem, _, idx = name.partition("@")
        if stem != base:
            continue
        k = int(idx) if idx.isdigit() else -0.5  # bare name = initial value
        if best is None or k >= best_k:
            best_k, best = k, value
    return best


def model_table(raw: Dict[str, str]) -> List[Tuple[str, str]]:
    """Map a raw Boogie model to source-level rows for the failing procedure:
    tid, the running effect as a mover letter, then each store variable's
    current value and (when the model constrains it) its `\\old` value."""
    rows: List[Tuple[str, str]] = []
    tid = _last_incarnation(raw, "tid")
    if tid is not None:
        rows.append(("tid", _clean_value(tid)))
    eff = _last_incarnation(raw, "eff")
    if eff is not None and _clean_value(eff).lstrip("-").isdigit():
        code = int(_clean_value(eff))
        rows.append(("eff", _EFF_LETTER.get(code, str(code))))
    bases = sorted({name.partition("@")[0] for name in raw})
    for base in bases:
        if base.startswith("v_"):
            var = base[2:]
            cur = _last_incarnation(raw, base)
            if cur is not None:
                rows.append((var, _clean_value(cur)))
            old = _last_incarnation(raw, f"o_{var}")
            if old is not None and old != cur:
                rows.append((f"\\old({var})", _clean_value(old)))
    return rows


class BoogieError(RuntimeError):
    pass


class BoogieBackend:
    def __init__(self, boogie_path: Optional[str] = None, extra_args: Optional[List[str]] = None):
        self.boogie_path = boogie_path or self._discover()
        self.extra_args = extra_args or []

    @staticmethod
    def _discover() -> str:
        env = os.environ.get("MELVIN_BOOGIE")
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
            "could not find the Boogie executable; set MELVIN_BOOGIE to its path"
        )

    def run_raw(self, bpl_path: str, timeout: int = 120,
                extra: Optional[List[str]] = None) -> subprocess.CompletedProcess:
        cmd = [self.boogie_path, *self.extra_args, *(extra or []), bpl_path]
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
        want_model: bool = False,
    ) -> "VerifyResult":
        """Write the emitter's program to `bpl_path`, run Boogie, map results.

        With `want_model`, Boogie prints a counterexample model per error;
        each is parsed and attached to its diagnostic as source-level rows
        (unparseable models degrade to no counterexample, never a failure).

        If Boogie does not finish within `timeout` seconds it is killed and a
        result with `timed_out=True` (and `ok=False`) is returned rather than
        propagating the exception.
        """
        with open(bpl_path, "w") as f:
            f.write(emitter.text())
        try:
            proc = self.run_raw(bpl_path, timeout=timeout,
                                extra=["/printModel:1"] if want_model else None)
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
        # Boogie prints each counterexample model BEFORE the error it explains;
        # capture blocks and attach the pending one to the next error.
        pending_model: Optional[List[Tuple[str, str]]] = None
        model_lines: Optional[List[str]] = None
        for raw in out.splitlines():
            stripped = raw.strip()
            if stripped == "*** MODEL":
                model_lines = []
                continue
            if stripped == "*** END_MODEL":
                if model_lines is not None:
                    try:
                        pending_model = model_table(_parse_model_block(model_lines))
                    except Exception:            # malformed model: no cex, no crash
                        pending_model = None
                model_lines = None
                continue
            if model_lines is not None:
                model_lines.append(raw)
                continue
            m = _SUMMARY_RE.search(raw)
            if m:
                verified = int(m.group("verified"))
                continue
            m = _ERROR_RE.match(stripped)
            if m and (base in m.group("file") or m.group("file").endswith(".bpl")):
                bline = int(m.group("line"))
                if bline in seen_lines:
                    continue
                seen_lines.add(bline)
                oblig = self._nearest_obligation(emitter, bline)
                if oblig is not None:
                    diagnostics.append(Diagnostic(oblig.span, oblig.message,
                                                  model=pending_model))
                else:
                    diagnostics.append(
                        Diagnostic(None, f"Boogie error at {base}({bline}): {m.group('msg')}",
                                   model=pending_model)
                    )
                pending_model = None
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
