"""The mover-effect lattice and its algebra.

This module implements the six-element effect domain from the Mover Logic paper
(Section "Mover Logic Effects and Specifications"):

    e ::= Y | R | L | B | N | E

    * Y  -- the effect of a `yield` annotation
    * R  -- right-mover actions
    * L  -- left-mover actions
    * B  -- both-mover actions (both left- and right-movers)
    * N  -- non-mover actions (neither left- nor right-movers)
    * E  -- error (e.g. two non-movers in a reducible sequence)

The DFA for a reducible sequence accepts R* [N] L* separated by yields Y, which
induces the ordering

    Y  <  B  <  {R, L}  <  N  <  E

with join `join`, sequential composition `seq` (e1 ; e2), and iterative
closure `star` (e*).  The composition and closure tables below are transcribed
directly from Figure "Mover Logic Effects" in the paper so that the
implementation is a faithful, checkable copy of the formal definitions.
"""

from __future__ import annotations

from enum import Enum


class Effect(Enum):
    Y = "Y"
    B = "B"
    R = "R"
    L = "L"
    N = "N"
    E = "E"

    def __str__(self) -> str:  # pragma: no cover - trivial
        return self.value

    @property
    def pretty(self) -> str:
        return {
            Effect.Y: "yield",
            Effect.B: "both-mover",
            Effect.R: "right-mover",
            Effect.L: "left-mover",
            Effect.N: "non-mover",
            Effect.E: "error",
        }[self]


Y, B, R, L, N, E = (Effect.Y, Effect.B, Effect.R, Effect.L, Effect.N, Effect.E)

# ---------------------------------------------------------------------------
# Partial order   Y <= B <= R,L <= N <= E
# ---------------------------------------------------------------------------

# Reachability in the Hasse diagram, encoded as the set of elements <= key.
_LE_SETS = {
    Y: {Y},
    B: {Y, B},
    R: {Y, B, R},
    L: {Y, B, L},
    N: {Y, B, R, L, N},
    E: {Y, B, R, L, N, E},
}


def leq(a: Effect, b: Effect) -> bool:
    """Return True iff a  <=  b in the effect lattice."""
    return a in _LE_SETS[b]


# The lattice is a total order along a single chain except that R and L are
# incomparable, so the join of R and L is N.
_JOIN_ORDER = [Y, B, R, L, N, E]


def join(a: Effect, b: Effect) -> Effect:
    """Least upper bound of two effects."""
    if leq(a, b):
        return b
    if leq(b, a):
        return a
    # a and b incomparable: the only such pair is {R, L}, whose lub is N.
    return N


def join_all(effects) -> Effect:
    """Least upper bound of a (possibly empty) iterable of effects.

    The join of no effects is the lattice bottom Y (a yield-only / empty run).
    """
    acc = Y
    for e in effects:
        acc = join(acc, e)
    return acc


# ---------------------------------------------------------------------------
# Sequential composition  e1 ; e2   (Figure "Mover Logic Effects")
#
#      ;   Y   B   R   L   N   E
#      Y   Y   Y   Y   L   L   E
#      B   Y   B   R   L   N   E
#      R   R   R   R   N   N   E
#      L   Y   L   E   L   E   E
#      N   R   N   E   N   E   E
#      E   E   E   E   E   E   E
# ---------------------------------------------------------------------------

_SEQ = {
    Y: {Y: Y, B: Y, R: Y, L: L, N: L, E: E},
    B: {Y: Y, B: B, R: R, L: L, N: N, E: E},
    R: {Y: R, B: R, R: R, L: N, N: N, E: E},
    L: {Y: Y, B: L, R: E, L: L, N: E, E: E},
    N: {Y: R, B: N, R: E, L: N, N: E, E: E},
    E: {Y: E, B: E, R: E, L: E, N: E, E: E},
}


def seq(a: Effect, b: Effect) -> Effect:
    """Sequential composition e1 ; e2."""
    return _SEQ[a][b]


def seq_all(effects) -> Effect:
    """Left-to-right sequential composition of a run of effects.

    The empty run composes to B (the identity of `;`, matching `skip`).
    """
    acc = B
    for e in effects:
        acc = seq(acc, e)
    return acc


# ---------------------------------------------------------------------------
# Iterative closure   e*
#
#      Y* = Y   B* = B   R* = R   L* = L   N* = E   E* = E
# ---------------------------------------------------------------------------

_STAR = {Y: Y, B: B, R: R, L: L, N: E, E: E}


def star(a: Effect) -> Effect:
    """Iterative (Kleene) closure e*."""
    return _STAR[a]


def is_reducible(e: Effect) -> bool:
    """A run/statement is reducible iff its overall effect is not the error E."""
    return e is not E
