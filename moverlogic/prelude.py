"""The fixed Boogie prelude shared by every generated program.

It defines:
  * integer codes for the six effects and the `seqEff`/`leqEff` operations,
    transcribed from `effects.py` so the Boogie side computes the *same*
    effect algebra as the Python side;
  * the `even` predicate used by the counter examples;
  * uninterpreted immutable lists (Nil/cons/head/tail) and optionals
    (None/Some/isNone/theVal) with their defining axioms, used by the
    lock-free queue and stack examples.
"""

from __future__ import annotations

from .effects import Effect, seq, leq

_CODE = {Effect.Y: 0, Effect.B: 1, Effect.R: 2, Effect.L: 3, Effect.N: 4, Effect.E: 5}
ALL = [Effect.Y, Effect.B, Effect.R, Effect.L, Effect.N, Effect.E]

# Public integer codes for use by the generator.
EFF_CODE = {e.name: c for e, c in _CODE.items()}
E_CODE = _CODE[Effect.E]
R_CODE = _CODE[Effect.R]
L_CODE = _CODE[Effect.L]
Y_CODE = _CODE[Effect.Y]
B_CODE = _CODE[Effect.B]
N_CODE = _CODE[Effect.N]


def _seq_function() -> str:
    """Emit `function seqEff(int,int) returns(int)` as a nested if/else."""
    def rec(i: int) -> str:
        if i == len(ALL):
            return str(E_CODE)  # unreachable default
        a = ALL[i]

        def rec_b(j: int) -> str:
            if j == len(ALL):
                return str(E_CODE)
            b = ALL[j]
            val = _CODE[seq(a, b)]
            return f"(if b == {_CODE[b]} then {val} else {rec_b(j + 1)})"

        return f"(if a == {_CODE[a]} then {rec_b(0)} else {rec(i + 1)})"

    body = rec(0)
    return f"function {{:inline}} seqEff(a: int, b: int) returns (int) {{ {body} }}"


def _leq_function() -> str:
    def rec(i: int) -> str:
        if i == len(ALL):
            return "false"
        a = ALL[i]

        def rec_b(j: int) -> str:
            if j == len(ALL):
                return "false"
            b = ALL[j]
            val = "true" if leq(a, b) else "false"
            return f"(if b == {_CODE[b]} then {val} else {rec_b(j + 1)})"

        return f"(if a == {_CODE[a]} then {rec_b(0)} else {rec(i + 1)})"

    return f"function {{:inline}} leqEff(a: int, b: int) returns (bool) {{ {rec(0)} }}"


def prelude() -> str:
    parts = [
        "// ==== Mover Logic Boogie prelude ====",
        "// Effect codes: Y=0 B=1 R=2 L=3 N=4 E=5",
        _seq_function(),
        _leq_function(),
        "",
        "// even() used by the counter example",
        "function {:inline} even(n: int) returns (bool) { n mod 2 == 0 }",
        "",
        "// Immutable lists (lock-free stack example)",
        "type List;",
        "const unique Nil: List;",
        "function cons(int, List) returns (List);",
        "function head(List) returns (int);",
        "function tail(List) returns (List);",
        "axiom (forall v: int, s: List :: head(cons(v, s)) == v);",
        "axiom (forall v: int, s: List :: tail(cons(v, s)) == s);",
        "axiom (forall v: int, s: List :: cons(v, s) != Nil);",
        "",
        "// Optionals (lock-free queue example): None or Some(v)",
        "type Optional;",
        "const unique None: Optional;",
        "function Some(int) returns (Optional);",
        "function isNone(Optional) returns (bool);",
        "function theVal(Optional) returns (int);",
        "axiom (forall v: int :: Some(v) != None);",
        "axiom (forall v: int :: isNone(Some(v)) == false);",
        "axiom isNone(None);",
        "axiom (forall v: int :: theVal(Some(v)) == v);",
        "// ==== end prelude ====",
        "",
    ]
    return "\n".join(parts)
