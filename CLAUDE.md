# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

**Melvin**, a Python implementation of **Mover Logic** — a reduction-based
rely-guarantee program logic (from the `../reduction-rg-logic` manuscript,
`main.pdf`/`main.tex`) — that verifies concurrent programs by lowering proof
obligations to **Boogie**.
Architecturally inspired by the Anchor / Synchronicity verifiers in
`../Synchronicity`.

## Commands

```bash
pip install -e .                                 # install (adds `melvin`, `melvin-run`, `melvin-server`)
export MELVIN_BOOGIE=/path/to/boogie          # if boogie isn't on PATH
melvin examples/counter.mml                   # verify a program
melvin examples/counter.mml --show-bpl        # print generated Boogie
melvin examples/counter.mml --emit-bpl out.bpl   # save generated Boogie
melvin-run examples/oracle_safe.mml           # execute under all interleavings
pytest tests/ -q                                  # run tests (prover tests self-skip)
pytest tests/test_effects.py::test_seq_matches_paper_table   # a single test
```

Boogie discovery order: `MELVIN_BOOGIE` env var → `boogie`/`Boogie` on PATH
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
| `checker.py` / `cli.py` | driver and `melvin` verify CLI |
| `annotate.py` | per-statement mover letters (`--show-movers`, demo gutter); static clause join sharpened by a 3-valued evaluator for acquire/release/cas/known-value writes — display only, never used for verification |
| `interp.py`  | reference small-step interpreter + `melvin-run`; independent differential oracle for the verifier (explores all interleavings, detects reachable `wrong`); enumerates final stores with a representative trace each, and trace-step stores show per-thread call-frame stacks |

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

### Objects and the heap (the `objects` extension)

The language has Anchor-style classes: fields with mover clauses whose guards
may mention `this`, `this`'s fields, and `tid` (nothing else — this is what
keeps validity checking tractable), per-object `lock` fields, methods with an
implicit immutable `this` and immutable parameters, `new C`, `null`, and heap
arrays. Key encoding decisions (all in `vcgen.py`):

* Each class C contributes **shared store items**: one map per field
  (`f_C_fld: [C]T`) and an allocation set (`alloc_C: [C]bool`). A whole map is
  just another store item, so all `v_/o_/pre_/py_/ce_` snapshot machinery,
  yield havoc, and `\old` translation apply unchanged (whole-map assignment).
* Field accesses capture the receiver in a per-class temp (`recv_C`), assert
  it non-null, and evaluate the field's clauses with `this` bound to it.
  `new` picks a fresh unallocated reference and resets fields to defaults;
  allocation sets grow monotonically under interference (`_builtin_rely`).
* Method calls substitute call-entry temps (`cs<k>_this`, `cs<k>_a<i>`) for
  `this`/parameters in the callee spec. Callee havoc is field-granular and
  transitive through nested calls (`_shared_writes`); when the callee writes
  the heap only through `this` (`_writes_only_this`), only the *receiver's*
  map entries are havocked, so quantified guarantees survive calls.
* Field validity: same-class pairs only, two possibly-aliasing receivers
  (`_field_validity3`, `_field_validity_commute`); cross-class and
  field/global pairs commute structurally by the guard restriction.
* An array field `var int[] a ...` introduces a **named array type**
  `Arr_C_a` (`elems_C_a`, `len_C_a`, alloc set). Its plain clauses govern the
  reference; its `[i]` clauses are the element spec, and element guards are
  state-independent (`tid` + index only), which makes element validity(3)
  trivial. Element accesses carry null + bounds obligations.
* Spec-side quantifiers: `forall o : C . p`, `forall j : int . p`,
  `forall a in C.f . p` (over field C.f's arrays).
* Sugar: `lock m;` (no clauses) expands to the standard mutex discipline;
  `guarded_by m` on a field/global expands to `both-mover if <lock> == tid`.
* Not yet done (see PLAN.md): Anchor's FRESH/LOCAL/SHARED object-state ghost
  (`isLocal`-style specs), class invariants, owner-relative element guards
  (`holds(this)` on array elements), `modifies` clauses.

`interp.py` mirrors all of this with a heap inside its flat store dict
(`("ref", T, addr)` values, `("fld"/"elem"/"len"/"next", ...)` keys); run-time
faults (null deref, bounds, negative size) are reachable-`wrong`s.

### Adding to the language

Grammar keyword? update `lexer.KEYWORDS` + `parser`. New statement/expr? add an
`ast_nodes` dataclass (with a `Span`), parse it, type-check + classify in
`types.py`, lower it in `vcgen.py`, and translate any new expression form in
`vcgen.Translator.tr`.

## Examples & tests

`examples/*.mml` are the paper's examples plus corner cases (write-guarded,
nested control, non-atomic chains, atomic-calls-atomic) and rejected programs
(`racy_bad`, `assert_fail`, `double_release`, `both_mover_loop`,
`rely_not_transitive`, `rely_not_reflexive`). The object extension adds
`obj_counter`, `obj_counter_client` (quantified R/G), `obj_array`
(per-element movers), `obj_oracle_safe`/`obj_oracle_unsafe` (differential
oracle over a published object), and the rejected `obj_racy_bad`; their tests
live in `tests/test_objects.py`. There is one
unit-test module per source file (`tests/test_<module>.py`) plus end-to-end
`tests/test_examples.py`; `tests/_util.py` holds the `needs_boogie` skip marker.
Boogie-dependent tests self-skip when the prover is absent. Run `pytest tests/`;
mutation tests guard against the checker becoming vacuous (a program that should
fail must still fail). Coverage is ~96% (`pytest --cov=melvin`).

Boogie runs under a wall-clock timeout (`boogie_backend.DEFAULT_TIMEOUT`, 5 min;
`--timeout` on the CLI). A timeout yields `CheckResult.timed_out=True` and CLI
exit code 2 (vs 1 for a refutation), never an exception.

Mover-spec validity checks all four paper conditions (`gen_validity` →
`_validity3` for (3), `_validity_commute` for (1),(2),(4)). Writes are modelled
as `<X := v>` (arbitrary store-independent value), so the commuting witness for
(1),(2),(4) is constructed explicitly and each condition is a plain assertion.

Rely well-formedness (`gen_rely_checks`): each non-atomic function's rely must
be reflexive and transitive (`R = R*`), because `emit_yield` assumes R once to
model any number of interference steps. Guarantees need no closure check —
they are asserted one reducible sequence at a time.

## Usability features (both branches)

* Spec clauses that are literally `true` may be elided; `func f() { ... }`
  declares a non-atomic all-true-spec function.
* `melvin-run`: traces show `t<tid> file:line source` per step; distinct
  final stores are enumerated by default (`--no-finals`), deduplicated up to
  reachable-heap isomorphism on the objects branch; `--json` emits the
  structured result (trace steps carry store-JSON) that the demo server
  relays.
* `melvin --counterexample`: failed obligations carry a source-level store
  table decoded from the Boogie model (`/printModel:1`; models are partial —
  SSA-pruned values may be missing). On the objects branch, field maps are
  decoded through the model's Select_ graphs into `C#k.f` rows.
* `annotate.line_details()` powers the demo's hover popups: per line, the
  mover letter, WHY (clauses quoted from source with matched/ruled-out
  status), and a schematic abstract store (3-valued forward flow;
  display-only, approximate).
* Demo UI: gutter-chip hover popups, a clickable trace scrubber with
  per-step store snapshots, final-state panels, and counterexample tables;
  heap objects render as box-and-arrow SVG diagrams (`snapshot.js` +
  vendored dagre).

## Web demo

`melvin_server/` holds a FastAPI server (`melvin_server/app.py`: verify in-process via
`check_source`, interpreter in a killable subprocess; rate limit, job queue,
LRU cache, `MELVIN_DEMO_*` env config) and a no-build frontend
(`melvin_server/static/`, vendored CodeMirror 5). Run with `melvin-server [--reload]`
(or `uvicorn melvin_server.app:app --reload`); the demo deps (fastapi, uvicorn,
httpx) are part of the main pyproject dependencies.
`melvin_server/Dockerfile` bundles Boogie+Z3 and smoke-tests at build time;
`melvin_server/deploy/deploy-lightsail.sh` deploys to Lightsail Containers (`-n` = dry
run). The Examples menu manifest (`melvin_server/examples_manifest.py`) is also
the served-file allowlist — add new examples there.
