# Plan: Traces, Elided Specs, Explanations/Snapshots, Final States, Counterexamples

> **Status (2026-07-08): implemented.** All five features are on `main` in
> scalar form and on `objects` with the heap extensions (reachable-heap
> isomorphism for final states, object diagrams in traces/finals,
> receiver-field tracking in the hover flow, and heap counterexamples decoded
> from the Boogie model's Select_ graphs into `C#k.f` rows).
>
> **Still to do:**
> * Array **element** values in counterexamples are not decoded (the model's
>   nested `[at][int]T` select graphs are skipped); element rows would need a
>   two-level Select_ lookup in `boogie_backend.model_table`.
> * The hover schematic renders as a table, not an object diagram: the
>   `this.f` facts are receiver-relative with no object identity to draw.
>   Drawing a one-box "this" diagram would be a small `snapshot.js` addition.
> * The demo UI changes are tested at the API level and syntax-checked only;
>   a manual browser pass (hover popups, trace scrubber, finals diagrams,
>   counterexample checkbox) has not been done.
> * Counterexample values are inherently partial (Boogie prunes SSA
>   incarnations); no further mitigation is planned, but the UI could label
>   missing values explicitly.

Five features, each landing on `main` first (suite green), with `main` merged
into `objects` after each phase so the ancestor property is preserved; the
heap-specific extensions (isomorphism, object diagrams) then land as
`objects`-only follow-ons.

Design decisions settled by interview (2026-07-08):

* **F1**: fully spec-less non-atomic functions use the `func` keyword
  (`func f() { ... }`); any subset of clauses may also simply be elided.
* **F2**: memory snapshots appear in *all four* contexts — interpreter trace
  steps, Boogie counterexample stores, final-state displays, and a
  hover-on-any-line schematic (locks held + definitely-known values from a
  static 3-valued pass, unknowns drawn as `?`).
* **F3**: a "final state" is the globals plus the heap reachable from them
  (dead thread-locals collapse); enumeration is ON by default in both
  `melvin-run` and the UI, capped with a count.
* **F4**: counterexamples are shown as a mapped source-level store table
  (raw Boogie model not exposed).
* **UI diagrams**: vendor a small graph-layout library (dagre) and render
  Anchor-style box-and-arrow object diagrams over it in hand-written SVG.
* **Trace snapshots**: one per step (traces are shortest paths, so short).

## Shared infrastructure

* **`melvin-run --json`**: a machine-readable result — safe/unsafe/bounded,
  states explored, the failing trace as
  `[{tid, line, source, store_after}, ...]`, and the canonical final stores.
  The demo server relays this to the frontend instead of scraping text.
  Store JSON schema (shared by traces, finals, counterexamples, hover):
  `{"globals": {x: v, ...}, "objects": [{"id": "#1", "class": "C",
  "fields": {...}}, ...]}` — `objects` empty on `main`, populated on
  `objects`; reference values are `"#n"` / `"null"`; unknown values `"?"`.
* **`demo/static/vendor/dagre.min.js`** (one-time vendored download) plus a
  new `demo/static/snapshot.js`: takes the store JSON, lays out object boxes
  with dagre, draws SVG rects/rows/arrows. Used by the trace scrubber, the
  finals panel, the counterexample table, and the hover schematic. On `main`
  it degrades to a plain variable table (no boxes).

## F0 — traces with line numbers and source (small)

`Interpreter` accepts the source text; `_descr` becomes
`t1  counter.mml:23  x = t;`, one step per line in `--trace` output, and the
JSON trace carries `{line, source}` per step. Tests assert line numbers
appear. No open questions.

## F1 — elidable `true` spec clauses + `func`

* Parser: in `parse_fn_decl`, each of `relies/guarantees/requires/ensures`
  becomes optional (fixed order kept), defaulting to `BoolLit(true)`;
  `atomic` may elide either clause. New form `func name(params) block` =
  non-atomic with all-true spec. `parse_decl` dispatches on any of the six
  keywords. (`func` is already a lexer keyword, currently unused.)
* Trivially-true relies/guarantees remain reflexive/transitive and G⇒R
  holds, so no vcgen changes.
* Update the grammar comment, CLAUDE.md, and simplify a couple of examples
  to demonstrate (e.g. drop `requires true` from counter.mml's add).

## F2 — mover-hover explanations + snapshots in the UI

* **Explanations** (`annotate.py`): alongside the letter, emit a per-line
  record: action kind, the transition when statically known
  (`acquire: m 0 → tid`), each candidate clause with its status
  (matched / ruled out / undetermined, quoting the clause source via its
  span), and the resulting join. Serialized in the demo `/verify` response;
  the gutter chip gets a hover popup rendering it.
* **Hover schematic store** (`annotate.py`): a new forward 3-valued abstract
  interpretation over each body: per-line map of global (and on `objects`,
  receiver-field) abstract values — `tid`/literal/`?` — with locks tracked
  through acquire/release/cas; `yield` drops value facts but keeps locks
  held by `tid` (only the holder can release under the lock discipline;
  the popup labels the whole schematic "approximate"). Branch join = equal
  values kept, else `?`; loop bodies analyzed with modified names dropped
  to `?`. Rendered with `snapshot.js` next to the explanation.
* Display-only throughout — verification is untouched.

## F3 — final-state enumeration (default on)

* `interp.explore` collects terminal states (every thread's continuation
  empty). Canonicalization: project to globals; walk the heap from globals
  in deterministic order (sorted names, then field order / index order),
  renumbering addresses per type in first-visit order — isomorphic heaps
  produce identical canonical forms; basic values compare by equality.
  Collected into `ExploreResult.finals` (deduped set, insertion-capped at
  e.g. 100 with an overflow flag).
* CLI: after the SAFE/UNSAFE line, `N distinct final store(s):` with
  `x = 4, m = 0` per line; objects printed as `#1: Counter{x: 2, m: 0}`
  with `#n` references. `--no-finals` to suppress; bounded searches say
  "(search bounded — final states may be incomplete)".
* UI: "Final states" section in the Run panel, one diagram per state.
* On `main` the canonical form is just the global vector; the heap walk
  arrives with the `objects` merge.

## F4 — Boogie counterexamples (mapped store table)

* `boogie_backend`: when requested, add Boogie's model-printing flag, split
  `*** MODEL ... *** END_MODEL` blocks out of the output, and associate each
  with the preceding error line. **First step is a probe**: run the local
  Boogie on a failing program and build the parser against its actual model
  syntax (formats differ across versions; unparseable models degrade to
  "counterexample unavailable", never a crash).
* Mapping: through the existing obligation table — `v_x → x`,
  `o_x → \old(x)` (sequence start), `pre_x → pre-action x`, `tid`, and
  `eff`/`mv` decoded to mover letters. Only variables relevant to the failing
  procedure are shown. On `objects`, field-map entries for allocated
  references become a store JSON and render as a snapshot diagram.
* CLI: `melvin --counterexample` prints the table under each diagnostic.
  UI: a checkbox on Verify; table + diagram under each error.

## Sequencing

1. **F1 + F0** on `main` (parser sugar, trace lines, `--json` skeleton);
   merge → `objects`.
2. **F3** scalar version on `main` (terminal collection, canonical globals,
   CLI, JSON); merge → `objects`; then heap reachability + isomorphism +
   object rendering on `objects`.
3. **F4** on `main` (model probe, parser, mapping, CLI flag, server plumb);
   merge → `objects`; then heap-map → snapshot rendering.
4. **F2** on `main` (explanations, abstract-store pass, `/verify` payload,
   hover popup, vendored dagre + `snapshot.js`, trace scrubber + finals
   panel + counterexample display in the frontend); merge → `objects`; then
   receiver-field tracking and object-diagram hovers.
5. Docs (CLAUDE.md, PLAN-features.md status header) and demo manifest as
   needed.

## Risks

* Boogie model syntax varies by version → probe first, degrade gracefully.
* Terminal-state explosion → dedupe during search, cap stored finals.
* Hover schematic is an approximation (esp. locks-held across yields);
  it is labeled as such and never feeds verification.
* dagre must be vendored once (no runtime network in the demo).
