"""Unit tests for melvin.prelude."""

import itertools
import os
import subprocess
import tempfile

import pytest

from melvin import prelude as P
from melvin.effects import Effect, seq, leq
from melvin.boogie_backend import BoogieBackend

from _util import needs_boogie

ALL = [Effect.Y, Effect.B, Effect.R, Effect.L, Effect.N, Effect.E]


def test_prelude_contains_core_declarations():
    text = P.prelude()
    for needed in ("function {:inline} seqEff", "function {:inline} leqEff",
                   "function {:inline} even", "type List;", "const unique Nil: List;",
                   "type Optional;", "const unique None: Optional;"):
        assert needed in text


def test_effect_codes_are_distinct_and_complete():
    codes = P.EFF_CODE
    assert set(codes) == {"Y", "B", "R", "L", "N", "E"}
    assert len(set(codes.values())) == 6
    assert P.E_CODE == codes["E"]
    assert P.R_CODE == codes["R"]


def test_seq_and_leq_functions_are_wellformed_ite():
    # every 'if' has a matching 'then'/'else'; a crude balance check
    for fn in (P._seq_function(), P._leq_function()):
        assert fn.count("(if ") == fn.count(" then ")
        assert fn.count(" then ") == fn.count(" else ")


@needs_boogie
def test_boogie_seq_leq_match_python_algebra():
    """Prove the generated seqEff/leqEff agree with the Python effect algebra
    on all 36 pairs, by asserting each concrete value inside Boogie."""
    lines = [P.prelude(), "procedure {:entrypoint} Check() {"]
    for a in ALL:
        for b in ALL:
            ca, cb = P.EFF_CODE[a.name], P.EFF_CODE[b.name]
            lines.append(f"  assert seqEff({ca}, {cb}) == {P.EFF_CODE[seq(a, b).name]};")
            lv = "true" if leq(a, b) else "false"
            lines.append(f"  assert leqEff({ca}, {cb}) == {lv};")
    lines.append("}")
    text = "\n".join(lines)
    fd, path = tempfile.mkstemp(suffix=".bpl")
    os.close(fd)
    try:
        with open(path, "w") as f:
            f.write(text)
        proc = BoogieBackend().run_raw(path)
        assert "0 errors" in (proc.stdout or "") or "verified, 0 error" in (proc.stdout or ""), \
            proc.stdout
    finally:
        os.remove(path)
