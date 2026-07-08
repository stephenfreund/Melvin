"""Top-level driver: parse -> type-check -> lower to Boogie -> map results back."""

from __future__ import annotations

import os
import tempfile
from dataclasses import dataclass, field
from typing import List, Optional

from .ast_nodes import Program
from .boogie_backend import BoogieBackend, Emitter, DEFAULT_TIMEOUT
from .diagnostics import Diagnostic, MelvinError
from .parser import parse
from .types import check_types
from .vcgen import lower_program


@dataclass
class CheckResult:
    ok: bool
    diagnostics: List[Diagnostic] = field(default_factory=list)
    boogie_text: str = ""
    raw_output: str = ""
    verified: int = 0
    source_lines: List[str] = field(default_factory=list)
    tool_failure: Optional[str] = None
    timed_out: bool = False

    def render(self) -> str:
        if self.timed_out:
            body = "\n".join(d.render(self.source_lines) for d in self.diagnostics)
            return "verification timed out:\n" + body if body else "verification timed out"
        if self.tool_failure:
            return "internal prover error:\n" + self.tool_failure
        if self.ok:
            return f"verified ({self.verified} Boogie proof obligation(s) discharged)"
        return "\n".join(d.render(self.source_lines) for d in self.diagnostics)


def check_source(
    source: str,
    filename: str = "<input>",
    boogie_path: Optional[str] = None,
    keep_bpl: Optional[str] = None,
    timeout: int = DEFAULT_TIMEOUT,
    counterexample: bool = False,
) -> CheckResult:
    source_lines = source.splitlines()
    # -- front end: parse + type-check + lower (may raise MelvinError) ----
    try:
        prog = parse(source, filename)
        ti = check_types(prog)
        emitter = lower_program(prog, ti)
    except MelvinError as e:
        return CheckResult(
            ok=False,
            diagnostics=[Diagnostic(e.span, e.message)],
            source_lines=source_lines,
        )

    boogie_text = emitter.text()

    # -- back end: run Boogie -------------------------------------------------
    if keep_bpl:
        bpl_path = keep_bpl
        with open(bpl_path, "w") as f:
            f.write(boogie_text)
    else:
        fd, bpl_path = tempfile.mkstemp(suffix=".bpl", prefix="melvin_")
        os.close(fd)

    try:
        backend = BoogieBackend(boogie_path=boogie_path)
        result = backend.verify(emitter, bpl_path, timeout=timeout,
                                want_model=counterexample,
                                class_fields=getattr(ti, "classes", None))
    finally:
        if not keep_bpl and os.path.exists(bpl_path):
            os.remove(bpl_path)

    return CheckResult(
        ok=result.ok,
        diagnostics=result.diagnostics,
        boogie_text=boogie_text,
        raw_output=result.raw_output,
        verified=result.verified,
        source_lines=source_lines,
        tool_failure=result.tool_failure,
        timed_out=result.timed_out,
    )


def check_program(path: str, **kwargs) -> CheckResult:
    with open(path) as f:
        source = f.read()
    return check_source(source, filename=os.path.basename(path), **kwargs)
