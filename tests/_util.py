"""Shared helpers for the test suite."""

import pathlib

import pytest

from moverlogic.boogie_backend import BoogieBackend, BoogieError

EXAMPLES = pathlib.Path(__file__).resolve().parent.parent / "examples"


def _boogie_available() -> bool:
    try:
        BoogieBackend()
        return True
    except BoogieError:
        return False


BOOGIE_AVAILABLE = _boogie_available()

# Marker for tests that need a real Boogie install.
needs_boogie = pytest.mark.skipif(not BOOGIE_AVAILABLE, reason="Boogie not found")
