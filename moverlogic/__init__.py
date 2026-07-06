"""Mover Logic: a verifier for reduction-based rely-guarantee reasoning.

A Python implementation of the Mover Logic system (Flanagan & Freund), which
extends rely-guarantee logic with Lipton reduction so that atomic functions get
precise, client-independent specifications.  Programs in the Mover Logic
Language (MLL) are parsed, type-checked, and lowered to Boogie verification
conditions; Boogie failures are mapped back to the original source.
"""

from .checker import check_program, check_source, CheckResult  # noqa: F401

__version__ = "0.1.0"
