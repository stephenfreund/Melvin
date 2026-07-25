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
pip install -e ".[dev]"                          # install (adds `melvin`, `melvin-run`, `melvin-server`, `melvin-install-boogie`)
melvin-install-boogie                            # `dotnet tool install` Boogie into ~/.melvin/tools
melvin --doctor                                  # report the Boogie/Z3/examples Melvin can see
export MELVIN_BOOGIE=/path/to/boogie          # or point at an existing boogie
melvin examples/counter.mml                   # verify a program
melvin examples/counter.mml --show-bpl        # print generated Boogie
melvin examples/counter.mml --emit-bpl out.bpl   # save generated Boogie
melvin-run examples/oracle_safe.mml           # execute under all interleavings
pytest tests/ -q                                  # run tests (prover tests self-skip)
pytest tests/test_effects.py::test_seq_matches_paper_table   # a single test
```

Toolchain discovery lives in `melvin/tools.py` (the only module that knows how
to find or install the external tools): Boogie from `MELVIN_BOOGIE` → PATH →
`~/.melvin/tools` (where `melvin-install-boogie` puts it) → `~/.dotnet/tools` →
a legacy Synchronicity-checkout path; Z3 from `MELVIN_Z3` → PATH → the Python
environment's script dir (where the `melvin-verifier[z3]` extra's `z3-solver` wheel lands
it), in which case `BoogieBackend._prover_args` passes Boogie
`/proverOpt:PROVER_PATH=`. There is **no** real Boogie Python binding (the PyPI
`boogie` package is an unrelated Django library); the tool shells out to the
executable.

## Packaging and release

`melvin` is published to PyPI. Single source of version: `__version__` in
`melvin/__init__.py` (`pyproject.toml` reads it via `dynamic`/`attr`). The wheel
ships `examples/` *inside* the package as `melvin/examples/` (a `package-dir`
mapping in `pyproject.toml`); `tools.examples_dir()` resolves either layout and
the demo server uses it. Base dependencies deliberately include the demo server
(fastapi/uvicorn) so `pip install melvin` can run `melvin-server`; extras are
`[z3]` (prover binary from PyPI), `[test]`, `[dev]`.

`.github/workflows/ci.yml` runs the suite on 3.9/3.11/3.13 (installing Boogie
with the shipped `melvin-install-boogie`), builds + smoke-tests the wheel, and
builds the Docker image. `.github/workflows/release.yml` fires on a published
GitHub Release: it checks the tag against `__version__`, publishes to PyPI
(trusted publishing, or `PYPI_API_TOKEN`), then redeploys the demo image to
Lightsail via `melvin_server/deploy/deploy-lightsail.sh` (skipped when no AWS
credentials are configured).

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
| `checker.py` / `cli.py` | driver and `melvin` verify CLI (`--doctor`, `--version`) |
| `tools.py`   | finds/installs Boogie + Z3, locates bundled examples (`melvin-install-boogie`) |
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
  clauses) into `eff`. The paper's rules state their effect antecedents as
  *upper bounds* (`M(A,P) ⊑ e`), so the exact minimal effect is a valid — and
  optimal — ascription. Loops use a havoc-cut with an exact per-iteration
  `eff ⊑ R` check (M-while's `M(A₁,P);e₁ ⊑ R` antecedent), an unconditional
  `assert eff ⊑ R` at the loop head (M-while's `e ⋢ L` premise applied at the
  placement: any legal ascription is `⊒ R`, so a loop may never follow the
  commit point — checked before any exit-path assumes, so it also rejects
  loops whose exit can never succeed), plus a static approximation for the
  surrounding effect (`_loop_iter_static`).
* Two places compose a **larger-than-exact** ascription (`effects.bump_not_left`,
  Boogie `bumpEff`): a loop's effect is bumped out of the left-mover region
  (M-while's `e ⋢ L` — zero iterations perform no action, so e.g. a yield-only
  closure `Y` must not reset the surrounding phase; keeps loops out of the
  post-commit region, where termination would be required), and a blocking
  `acquire`'s mover is bumped likewise (M-action's totality side condition:
  `e ⊑ L` requires the action total). Post-commit placement of an acquire is
  then caught by the ordinary `eff != E` assert; for loops the head assert is
  the authoritative placement check (the bump only keeps the downstream effect
  faithful to the least legal ascription).
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
nested control, non-atomic chains, atomic-calls-atomic, `both_mover_loop` — a
both-mover loop ascribed a right-mover effect) and rejected programs
(`racy_bad`, `assert_fail`, `double_release`, `post_commit_loop`,
`post_commit_acquire`, `rely_not_transitive`, `rely_not_reflexive`). The object extension adds
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
* Demo guided tour (`js/tour.js`, vendored driver.js): 14 steps that drive
  the app itself (load examples, press Verify/Run) through the
  `window.MelvinApp` API exported at the bottom of `app.js`. Entry points:
  navbar Tour button, `#tour` URL hash, one-time first-visit toast
  (`localStorage` key `melvin-tour-seen`). Gotcha: driver.js puts
  `overflow:hidden` on the active element's *parent*; melvin.css un-clips
  `.menu` so the spotlighted Examples dropdown isn't clipped away.

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
