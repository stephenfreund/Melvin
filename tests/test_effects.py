"""Unit tests for melvin.effects -- the mover-effect lattice."""

import itertools

import pytest

from melvin.effects import Effect, Y, B, R, L, N, E, seq, star, join, join_all, \
    leq, seq_all, is_reducible

ALL = [Y, B, R, L, N, E]

# The sequential-composition table transcribed directly from the paper.
SEQ_TABLE = {
    Y: {Y: Y, B: Y, R: Y, L: L, N: L, E: E},
    B: {Y: Y, B: B, R: R, L: L, N: N, E: E},
    R: {Y: R, B: R, R: R, L: N, N: N, E: E},
    L: {Y: Y, B: L, R: E, L: L, N: E, E: E},
    N: {Y: R, B: N, R: E, L: N, N: E, E: E},
    E: {Y: E, B: E, R: E, L: E, N: E, E: E},
}
STAR_TABLE = {Y: Y, B: B, R: R, L: L, N: E, E: E}


def test_effect_enum_names_and_pretty():
    assert [e.value for e in ALL] == ["Y", "B", "R", "L", "N", "E"]
    assert str(R) == "R"
    assert B.pretty == "both-mover"
    assert N.pretty == "non-mover"
    assert Y.pretty == "yield"
    assert E.pretty == "error"


@pytest.mark.parametrize("a,b", list(itertools.product(ALL, ALL)))
def test_seq_matches_paper_table(a, b):
    assert seq(a, b) == SEQ_TABLE[a][b]


@pytest.mark.parametrize("a", ALL)
def test_star_matches_paper_table(a):
    assert star(a) == STAR_TABLE[a]


def test_leq_chain_and_incomparability():
    # Y <= B <= R,L <= N <= E
    for x in ALL:
        assert leq(x, x)                 # reflexive
        assert leq(x, E)                 # E is top
        assert leq(Y, x)                 # Y is bottom
    assert leq(B, R) and leq(B, L)
    assert leq(R, N) and leq(L, N)
    # R and L are incomparable
    assert not leq(R, L) and not leq(L, R)
    assert not leq(N, B) and not leq(R, B)


def test_leq_is_partial_order():
    for a, b in itertools.product(ALL, ALL):
        if leq(a, b) and leq(b, a):
            assert a == b               # antisymmetry
    for a, b, c in itertools.product(ALL, ALL, ALL):
        if leq(a, b) and leq(b, c):
            assert leq(a, c)            # transitivity


def test_join_properties():
    for a, b in itertools.product(ALL, ALL):
        j = join(a, b)
        assert leq(a, j) and leq(b, j)          # upper bound
        assert join(a, b) == join(b, a)         # commutative
        assert join(a, a) == a                  # idempotent
    assert join(R, L) == N
    assert join(Y, E) == E
    assert join(B, R) == R


def test_join_is_least_upper_bound():
    for a, b in itertools.product(ALL, ALL):
        j = join(a, b)
        for c in ALL:
            if leq(a, c) and leq(b, c):
                assert leq(j, c)


def test_join_all():
    assert join_all([]) == Y            # empty join is bottom
    assert join_all([B]) == B
    assert join_all([R, L]) == N
    assert join_all([Y, B, R]) == R


def test_seq_all():
    assert seq_all([]) == B             # identity of ;
    assert seq_all([R]) == R
    # acquire; read; write; release  =  R;B;B;L  =  N
    assert seq_all([R, B, B, L]) == N
    # two non-movers with no yield between = error
    assert seq_all([N, N]) == E


def test_reducibility_examples_from_paper():
    assert seq(R, L) == N
    assert seq(N, N) == E
    assert seq(Y, N) == L
    assert star(N) == E
    # spin loop (both-mover body)* then a right-mover commit
    assert seq(star(seq(B, B)), R) == R


def test_is_reducible():
    for x in ALL:
        assert is_reducible(x) == (x is not E)
