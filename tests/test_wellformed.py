"""The code generator must always emit well-formed Boogie: Boogie should be
able to parse, resolve, and type-check every generated program (whether the
Mover Logic obligations hold or not).  A `tool_failure` means Boogie could not
even process our output -- a code-generation bug -- and must never happen.
"""

import pathlib

import pytest

from melvin.checker import check_source

from _util import EXAMPLES, needs_boogie

ALL_EXAMPLES = sorted(p.name for p in EXAMPLES.glob("*.mml"))


@needs_boogie
@pytest.mark.parametrize("name", ALL_EXAMPLES)
def test_generated_boogie_is_wellformed(name):
    res = check_source((EXAMPLES / name).read_text(), name)
    assert res.tool_failure is None, (
        f"Boogie could not process the generated program for {name}:\n"
        f"{res.tool_failure}")
    # a real result must have been produced (either verified or a mapped error)
    assert res.ok or res.diagnostics


@needs_boogie
def test_generated_boogie_has_no_resolution_errors():
    for name in ALL_EXAMPLES:
        res = check_source((EXAMPLES / name).read_text(), name)
        low = res.raw_output.lower()
        for bad in ("undeclared identifier", "not supported", "parse error",
                    "type check", "more than one declaration"):
            assert bad not in low, f"{name}: generated Boogie had a '{bad}' error"
