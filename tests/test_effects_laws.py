"""Algebraic laws the effect domain must satisfy for the compositional analysis
to be sound.

These are exhaustive over the six-element domain (6^k combinations).  A failure
here means the paper's transcribed tables are internally inconsistent -- e.g. a
non-associative `;` would make statement sequencing order-dependent, and a
non-monotone `;`/`*`/`join` would break the rule of consequence (M-conseq).
"""

import itertools

import pytest

from melvin.effects import Effect, seq, star, join, leq

ALL = list(Effect)
TRIPLES = list(itertools.product(ALL, ALL, ALL))
PAIRS = list(itertools.product(ALL, ALL))


def test_seq_is_associative():
    for a, b, c in TRIPLES:
        assert seq(seq(a, b), c) == seq(a, seq(b, c)), (a, b, c)


def test_seq_has_both_identity():
    for a in ALL:
        assert seq(Effect.B, a) == a           # B is the identity of ;
        assert seq(a, Effect.B) == a


def test_seq_error_is_absorbing():
    for a in ALL:
        assert seq(Effect.E, a) == Effect.E
        assert seq(a, Effect.E) == Effect.E


def test_seq_is_monotone():
    for a, ap in PAIRS:
        if not leq(a, ap):
            continue
        for b, bp in PAIRS:
            if leq(b, bp):
                assert leq(seq(a, b), seq(ap, bp)), (a, ap, b, bp)


def test_join_is_associative_and_commutative():
    for a, b, c in TRIPLES:
        assert join(join(a, b), c) == join(a, join(b, c))
    for a, b in PAIRS:
        assert join(a, b) == join(b, a)


def test_join_is_monotone():
    for a, ap in PAIRS:
        if leq(a, ap):
            for b in ALL:
                assert leq(join(a, b), join(ap, b))


def test_star_is_monotone():
    for a, b in PAIRS:
        if leq(a, b):
            assert leq(star(a), star(b))


def test_star_is_extensive_and_idempotent_shape():
    # a <= a*  (a loop can do one iteration), and (a*)* == a*
    for a in ALL:
        assert leq(a, star(a))
        assert star(star(a)) == star(a)


def test_bottom_and_top():
    for a in ALL:
        assert leq(Effect.Y, a)        # Y is bottom
        assert leq(a, Effect.E)        # E is top
        assert join(Effect.Y, a) == a
        assert join(Effect.E, a) == Effect.E
