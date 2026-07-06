# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Python implementation of **Mover Logic** — a reduction-based rely-guarantee
program logic (from the `../reduction-rg-logic` manuscript, `main.pdf`/`main.tex`)
— that verifies concurrent programs by lowering proof obligations to **Boogie**.
Architecturally inspired by the Anchor / Synchronicity verifiers in
`../Synchronicity`.

## Commands

```bash
pip install -e ".[test]"                         # install (adds `moverlogic`, `moverlogic-run`)
export MOVERLOGIC_BOOGIE=/path/to/boogie          # if boogie isn't on PATH
moverlogic examples/counter.mml                   # verify a program
moverlogic examples/counter.mml --show-bpl        # print generated Boogie
moverlogic examples/counter.mml --emit-bpl out.bpl   # save generated Boogie
moverlogic-run examples/oracle_safe.mml           # execute under all interleavings
pytest tests/ -q                                  # run tests (prover tests self-skip)
pytest tests/test_effects.py::test_seq_matches_paper_table   # a single test
```

Boogie discovery order: `MOVERLOGIC_BOOGIE` env var → `boogie`/`Boogie` on PATH
→ a fallback path in `boogie_backend.py`. There is **no** real Boogie Python
binding (the PyPI `boogie` package is an unrelated Django library); the tool
shells out to the executable.

## Pipeline / architecture

`.mll source → lexer → parser → AST → type checker → VC generator → Boogie → mapped diagnostics`

| Module | Role |
|--------|------|
| `lexer.py` / `parser.py` / `ast_nodes.py` | front end; AST nodes carry `Span`s |
| `types.py`   | type inference + **action classification** (write / read / local) |
| `effects.py` | the six-element effect lattice `Y⊑B⊑{R,L}⊑N⊑E` with `;`, `*`, `⊔` (tables copied verbatim from the paper) |
| `prelude.py` | fixed Boogie prelude: the effect algebra as Boogie functions, `even`, immutable `List`, `Optional` |
| `vcgen.py`   | the core — lowers each Mover Logic obligation to a Boogie procedure |
| `boogie_backend.py` | runs Boogie; `Emitter` records an obligation per emitted `assert`, keyed by line, so failures map back to source |
| `checker.py` / `cli.py` | driver and `moverlogic` verify CLI |
| `interp.py`  | reference small-step interpreter + `moverlogic-run`; independent differential oracle for the verifier (explores all interleavings, detects reachable `wrong`) |

### Key design points (read before editing `vcgen.py`)

* One Boogie procedure per obligation: each function def, each validity check,
  each state-rule check. Boogie verifies them independently.
* Store model inside a procedure: `v_<g>` current value; snapshots `o_` (reducible-
  sequence start / `\old` in P,Q,G), `pre_` (`\old` in a mover clause), `py_`
  (`\old` in R at a yield), `ce_` (`\old` in a callee's Q). Ghost int `eff` tracks
  the running effect; `assert eff != E` after each action enforces reducibility.
* Actions compose the **exact, state-sensitive** mover (an `if/else` over spec
  clauses) into `eff`. Loops use a havoc-cut with an exact per-iteration `eff ⊑ R`
  check plus a static approximation for the surrounding effect / termination side
  condition (`_loop_iter_static`).
* Error messages are attached at `Emitter.assert_`; keep them source-accurate.

### Adding to the language

Grammar keyword? update `lexer.KEYWORDS` + `parser`. New statement/expr? add an
`ast_nodes` dataclass (with a `Span`), parse it, type-check + classify in
`types.py`, lower it in `vcgen.py`, and translate any new expression form in
`vcgen.Translator.tr`.

## Examples & tests

`examples/*.mml` are the paper's examples plus corner cases (write-guarded,
nested control, non-atomic chains, atomic-calls-atomic) and rejected programs
(`racy_bad`, `assert_fail`, `double_release`, `both_mover_loop`). There is one
unit-test module per source file (`tests/test_<module>.py`) plus end-to-end
`tests/test_examples.py`; `tests/_util.py` holds the `needs_boogie` skip marker.
Boogie-dependent tests self-skip when the prover is absent. Run `pytest tests/`;
mutation tests guard against the checker becoming vacuous (a program that should
fail must still fail). Coverage is ~96% (`pytest --cov=moverlogic`).

Boogie runs under a wall-clock timeout (`boogie_backend.DEFAULT_TIMEOUT`, 5 min;
`--timeout` on the CLI). A timeout yields `CheckResult.timed_out=True` and CLI
exit code 2 (vs 1 for a refutation), never an exception.

Mover-spec validity checks all four paper conditions (`gen_validity` →
`_validity3` for (3), `_validity_commute` for (1),(2),(4)). Writes are modelled
as `<X := v>` (arbitrary store-independent value), so the commuting witness for
(1),(2),(4) is constructed explicitly and each condition is a plain assertion.
