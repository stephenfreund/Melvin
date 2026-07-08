# Plan: Objects, Fields, and Arrays for Melvin (`objects` branch)

> **Status (2026-07-07).** Phases 1–5 and 7 are implemented on this branch
> (front end, heap vcgen, field/array validity, quantified R/G, precise call
> framing, arrays, interpreter + annotator, docs/demo/sugar); see the commit
> history and `tests/test_objects.py`. Notable deltas from the plan below:
>
> * Call framing improved on §2.5: when a callee (transitively) writes the
>   heap only through `this`, the call site havocs just the receiver's map
>   entries (a point update) instead of whole maps — no `modifies` clauses
>   needed for the common case.
> * Array element guards are restricted to `tid` + the index variable
>   (state-independent); owner-relative guards (`holds(this)`, `this.read`)
>   from the full FastTrack example need the phase-6 machinery and are
>   future work, as are `forall a : C.f`-style guards on the reference
>   itself. Spec-side `forall a in C.f . p` and `forall j : int . p` were
>   added instead to make per-slot relies/guarantees expressible.
> * `x = f(args)` / `x = e.m(args)` result binding was added (desugared to
>   call statements in the checker).
> * Phase 6 (FRESH/LOCAL/SHARED object-state ghost, `isLocal`, class
>   invariants) is NOT implemented — it remains the stretch phase below.

Goal: extend Melvin's language from flat globals to (roughly) the Anchor/Sink
language — classes with mutable fields carrying state-dependent mover specs,
per-object locks, arrays with per-element specs, allocation — while keeping
Melvin's existing Mover Logic pipeline (`lexer → parser → types → vcgen →
Boogie`, plus the `interp.py` differential oracle) intact.

Reference points:

* Anchor implementation: `../Synchronicity/workspace/Synchronicity/src/anchor/`
  — `sink/Ast.scala`, `sink/Parser.scala` (surface language),
  `tool/SinkPrinter.scala` (Boogie heap encoding),
  `tool/SinkYieldPrinter.scala` (yield/interference `Y` predicate).
* Melvin core to generalize: the store/snapshot model in `vcgen.py`
  (`v_/o_/pre_/py_/ce_` snapshots, `_mover_expr`, `_emit_mover`,
  `emit_yield`, `gen_validity`, callee framing in `_callee_global_writes`).

Non-goals (matching Anchor): no inheritance, no dynamic dispatch, no GC
reasoning. Deliberately deferred from Anchor for later phases: object
lifecycle states (`FRESH/LOCAL/SHARED`, `isLocal`), class invariants, `noABA`.

---

## 1. Surface language

Stay Melvin-flavored: keep Melvin's *clause list* mover syntax
(`read/write MOVER if guard`) rather than Anchor's conditional-mover
expression language (`c ? B : E`, `m1 # m2`). The two are equally expressive
(Anchor's `#` is Melvin's `read`/`write` split; Anchor's `? :` chains are
Melvin's ordered clause lists), and reusing `MoverClause` keeps
`vcgen._mover_ite` and `annotate.py` unchanged in shape.

### 1.1 Class declarations

```mml
class Counter {
  var int x   both-mover if this.m == tid;
  lock m;                       // built-in lock discipline, per object

  atomic
  requires true
  ensures  this.x == \old(this.x) + n && this.m == \old(this.m)
  add() {
    acquire(this.m);
    t = this.x;
    t = t + n;
    this.x = t;
    release(this.m);
  }
}
```

* Fields are declared like today's globals but inside `class`; guards may
  mention `this`, `tid`, and fields of `this` (post-state bare, pre-state via
  `\old(this.f)`), plus `newValue` for the value being written. Restriction
  (for tractable validity checks, see §4.4): a field guard may dereference
  only `this` — no `this.f.g`.
* `lock f;` inside a class = per-object lock field with the standard
  acquire-right-mover / release-left-mover clauses instantiated at `this`.
* Methods are today's `fn_decl` with an implicit `this` parameter; both
  `atomic` and `relies/guarantees` specs allowed. Method call syntax
  `e.m(args)`; while we're in here, add real parameters and arguments to
  functions/methods (currently Melvin functions are nullary and communicate
  through thread-locals — parameters become a prerequisite for `this` anyway).
* Reference types: `Counter c;` locals, `null` literal per class
  (`Counter.null` in Boogie, surface literal `null`).
* Allocation: `c = new Counter;` — fields start at type defaults
  (0 / false / null / Nil / None); an optional `init` method can be called
  explicitly. Allocation itself is a both-mover action (it touches no shared
  state; the fresh reference is unreachable by other threads).
* Top-level `var`/`lock` globals stay; internally they become fields of a
  synthetic singleton class so vcgen has one uniform heap story.

### 1.2 Field access as actions

Preserve the paper's one-shared-access-per-action discipline, extended to
the heap. `types.py` classifies:

* **field read**: `l = e.f;` where `e` is a local-only expression;
* **field write**: `e.f = rhs;` where `e`, `rhs` are local-only;
* **array read/write**: `l = e[i];`, `e[i] = rhs;` likewise;
* `acquire(e.f)` / `release(e.f)` / `cas(e.f, a, b)` with `e` local-only;
* unstable read `l = *e.f;`.

Compound accesses (`x.f.g = e.h`) are rejected with a "split into multiple
statements" diagnostic, exactly like today's multiple-globals-per-action rule.

### 1.3 Arrays

Anchor-style: array *element* specs with a named index variable. Reuse
`MoverClause.index` (already parsed and reserved for this):

```mml
class VarState {
  var int read   write right-mover if ... ;
  var int[] vc   [i] both-mover if this.m == tid || tid == i;

  ...
  ensureCapacity(n) {
    a = this.vc;
    len = length(a);
    ...
    t = a[i];        // element access, mover from the [i] clause
  }
}
```

* Array type `T[]`; `a = new int[n];`, `length(a)` builtin.
* Element clauses bind the declared index var (`[i] ... if ... i ...`), plus
  `this` = the owning object, `athis`-style array self-reference deferred
  (phase 3 keeps Anchor's simpler common case: arrays reached from a field).
* Note today's `int[]` surface type maps to a Boogie value `[int]int` (a
  math map, copied by value on assignment). Object-language arrays need
  reference semantics — `T[]` becomes a heap reference (see §2), which is a
  behavior change for any existing example using `[]` (none in `examples/`
  use mutation through two aliases, so the migration is mechanical).

---

## 2. Boogie heap encoding (vcgen)

Follow Anchor's encoding, adapted to Melvin's snapshot discipline.

### 2.1 Types and maps

Per class `C` (emitted into the per-program section of the prelude):

```boogie
type C;
const unique C.null: C;
var alloc_C: [C]bool;          // allocation set
// one map per field f: T
var f_C_f: [C]T;
```

Per array field of element type `T`:

```boogie
type Arr_T;                    // one ref type per element type
const unique Arr_T.null: Arr_T;
var elems_T: [Arr_T][int]T;
const length_T: [Arr_T]int;    // immutable length
axiom (forall a: Arr_T :: length_T[a] >= 0);
```

### 2.2 Store items = scalars + whole maps

The crucial simplification that makes Melvin's existing machinery carry over:
**a field map is just another store item**. `store_items(scope)` returns
locals (scalars, incl. ref-typed locals) *plus one entry per field map and
alloc set*. Then, unchanged in structure:

* `declare_vars` declares `v_/o_/pre_/py_/ce_` copies of each map
  (Boogie allows map-typed local variables and whole-map assignment, which is
  exactly what `snapshot()`'s `pre_x := v_x;` already emits);
* `\old(this.f)` translates to `pre_f_C_f[pre_this]` via the existing
  `Translator.tr` `Old` case — the `old` map for `f` points at the snapshot
  map, no new mechanism;
* `emit_yield` havocs all field maps + alloc sets (instead of all globals)
  and assumes R once, as today;
* `restore_seq_start` copies maps, as today.

`Translator.tr` gains a `FieldAccess(base, name)` case →
`f_C_f[tr(base)]`, an `Index` case over heap arrays →
`elems_T[tr(base)][tr(i)]`, and `null`/`length`.

### 2.3 Mover evaluation for a field access

`_mover_expr` generalizes from `(gname, access)` to a *location*:
`(class, field, access, receiver-expr)` (plus index for arrays). The emitted
`if/else` chain is the same `_mover_ite`, but the clause guards are translated
with `this ↦ tr(receiver)` (and `i ↦ tr(index)`) added to both `cur` and
`old` maps, and `newValue ↦ tr(rhs)` for writes. Emission order per action
stays: snapshot `pre_`, perform the map update
(`f_C_f := f_C_f[r := val]`), evaluate `mv`, `assert mv != E`,
`eff := seqEff(eff, mv)`, `assert eff != E`.

Add `assert r != C.null` (and array bounds `0 <= i < length_T[a]`) before
each access — new obligation class with its own diagnostic.

### 2.4 Allocation

```boogie
havoc tmp_C;
assume tmp_C != C.null && !v_alloc_C[tmp_C];
v_alloc_C := v_alloc_C[tmp_C := true];
v_f_C_f := v_f_C_f[tmp_C := <default>];   // each field
v_c := tmp_C;
```

Effect: compose B. Subtlety: at a yield, other threads may allocate — the
yield havoc of `alloc_C` already models this; the rely must be able to say
"allocated stays allocated", so bake
`forall o: C :: \old(alloc(o)) ==> alloc(o)` into the assumed interference
(part of the built-in rely conjunct, like `tid > 0` today).

### 2.5 Calls and framing

`_callee_global_writes` becomes field-granular: scan the callee for writes to
`(C, f)` pairs and havoc those *whole maps* at call sites before assuming the
callee's ensures. This is coarse (a callee writing `o.f` havocs `f` for all
objects) but sound; the callee's ensures should therefore be encouraged to
frame (`forall o: C :: o != this ==> o.f == \old(o.f)`). Later refinement:
auto-generate that frame conjunct from a `modifies this.f` clause
(Anchor's per-transaction `modifies` lists — worth adopting once quantified
ensures get annoying to write).

### 2.6 Rely/guarantee over the heap

R and G become heap relations. Two additions:

* **Ref-typed quantifiers**: extend `Quant` beyond int ranges to
  `forall C o :: body` / `exists C o :: body` (surface:
  `forall Counter o . even(\old(o.x)) ==> even(o.x)`). Translation is a plain
  Boogie `forall o: C :: ...`; consider `{:trigger}`s only if Z3 chokes.
* **Rely well-formedness** (`gen_rely_checks`, R = R*): unchanged in logic;
  the reflexivity/transitivity procedures now range over map-typed stores.
  Havoc maps instead of scalars; assertions become quantified. Watch prover
  time here — this is the first place quantifier blowup will show up.

### 2.7 Mover-spec validity (`gen_validity`)

The four paper conditions now quantify over *two* accesses that may or may
not alias. For each field spec, each condition becomes: two arbitrary
receivers `r1, r2` (and indices for arrays), two thread ids, case split
`r1 == r2` vs `r1 != r2`:

* `r1 != r2`: the accesses touch disjoint map indices; because guards may
  only dereference `this` (§1.1 restriction), the *values* commute trivially,
  but the *guards* of one access can still observe the other's write only if
  they read the same field of a different object — ruled out by the same
  restriction. So the distinct case reduces to checking guard stability under
  updates at other indices, which the encoding gets for free
  (`f[r1 := v]` at `r2` is `f[r2]`).
* `r1 == r2`: exactly today's `_validity_commute`/`_validity3` obligations,
  with `v_g` replaced by `f[r]`.

Concretely: generalize the existing witness construction to operate on
`(map, index)` locations instead of variable names. This is the trickiest
vcgen change; do it after the straight-line encoding works.

### 2.8 Prelude

Static parts unchanged (effect algebra, List, Optional). The per-program
emitted section grows the class/array type declarations of §2.1. Keep the
existing `[int]T` math-map encoding *only* for spec-level values if we keep
`value`-typed sequences; otherwise arrays uniformly move to the heap.

---

## 3. Interpreter, annotator, CLI

* **interp.py**: store gains a heap: `store[("heap", addr)] = {field: val}`;
  ref values are ints tagged with the class (`("ref", "Counter", 3)`),
  `null = ("ref", C, 0)`. Allocation uses a per-state counter (kept in the
  store so DFS hashing stays consistent). Field/array access and `new` in
  `_step`/`_eval`; `\old` snapshots already freeze the whole store, so heap
  snapshotting is free. Optional (only if state counts explode): canonicalize
  addresses by traversal order when hashing.
* **annotate.py**: 3-valued evaluator learns `this`/field access. Abstract
  values: references are `UNKNOWN` except `this` (a distinguished symbol,
  analogous to `TID`); `this.f` guards evaluate against per-`this.f` abstract
  facts (acquire/release/cas on `this.f` establish known values exactly as
  they do for globals today). Aliased receivers (`o.f`) simply evaluate to
  `UNKNOWN` → static join. Display-only, so being coarse is fine.
* **cli/checker/diagnostics**: nothing structural; new obligation kinds
  (null deref, bounds, field race) need message strings and tests mapping
  them back to source spans via `Emitter.assert_`.
* **Demo**: new examples must be added to
  `demo/server/examples_manifest.py` (it is the allowlist).

---

## 4. Phases

Each phase lands green (`pytest tests/ -q`, all existing examples still
verify/refute as before) before the next starts.

**Phase 1 — front end + parameters.**
`lexer.KEYWORDS` += `class`, `new`, `null`, `this`, `length`, `newValue`;
parser: `class_decl`, field decls (reuse `var_decl`/`lock_decl` bodies),
methods, `this`, `e.f` in exprs and lvalues, `new`, method params/args and
plain function params; AST: `ClassDecl`, `FieldAccess`, `New`,
`MethodCall`, param lists on `FnDecl`; `types.py`: class types, `this`
typing, action classification per §1.2, guard well-formedness
(only-`this` dereference rule). Tests: `test_lexer/parser/types` additions;
everything downstream still rejects classes with a clear "not yet lowered"
error.

**Phase 2 — heap vcgen, straight-line core.**
§2.1–§2.5 for scalar fields: maps as store items, snapshots, field
read/write/cas/acquire/release lowering, allocation, null checks, calls with
field-granular framing, yields havocking maps. Migrate globals onto the
singleton-class path so there is one code path. First end-to-end example:
`examples/obj_counter.mml` (the §1.1 class) verifying, plus a racy variant
refuted. Mutation tests: break the spec, must fail.

**Phase 3 — R/G, validity, rely checks over the heap.**
Ref quantifiers (§2.6), quantified relies/guarantees, generalized
`gen_validity` with alias case split (§2.7), `gen_rely_checks` over maps.
Examples: an object-based version of `counter_client2.mml`;
`rely_not_transitive` analogue with a quantified rely.

**Phase 4 — arrays.**
§1.3 + array encoding, bounds obligations, element-indexed mover clauses
(`[i]`). Example: port the FastTrack `VarState.ensureCapacity` fragment from
Anchor (`fasttrack-4.sink`) — it exercises index-dependent movers, which is
the whole point of element specs.

**Phase 5 — oracle + annotator.**
interp.py heap (§3), `melvin-run` on object examples, differential tests
(`oracle_safe`/`oracle_unsafe` object variants); annotate.py `this`-aware
evaluation; `--show-movers` gutter for methods.

**Phase 6 — thread-locality (Anchor's `_state`), stretch.**
`isLocal(e)` / `isShared(e)` guard primitives backed by a
`state_C: [C]State` ghost map (`FRESH/LOCAL(t)/SHARED`), publication on
writing a ref into a shared object, Anchor's state invariant
(`SinkPrinter.scala:714` `StateInvariant`) as an assumed/checked invariant,
and yield havoc that *preserves* fields of objects local to `tid` (the heap
analogue of Anchor's `Y` predicate — in Melvin terms, a built-in rely
conjunct `forall o: C :: isLocal(o, tid) ==> o.f == \old(o.f) && state
unchanged`). This is what makes `threadlocal`-style specs
(`isLocal(this) ? B : E`) provable and unlocks the idiomatic Anchor examples
(`ok1.sink`). Class invariants (`invariant e;` in a class, checked at
sequence boundaries) ride along here.

**Phase 7 — polish.**
Docs (`CLAUDE.md`, README grammar), demo examples + manifest, sugar:
`guarded_by e` / `write_guarded_by e` expanding to the standard clause
pairs (straight port of Anchor's `Parser.scala:181` desugarings), coverage
back to ~96%.

---

## 5. Risks / open questions

1. **Quantifier performance.** Heap relies/guarantees and validity checks
   introduce `forall o: C` everywhere. Mitigations: keep guards
   `this`-only (§1.1), inline mover functions like Anchor does
   (`{:inline}`), add triggers only when needed, and keep the per-obligation
   procedure split so failures stay local.
2. **Validity with aliasing** (§2.7) is the subtlest port — Anchor sidesteps
   parts of this with its `Y`-predicate formulation; if the two-access
   witness construction gets hairy, an alternative is to adopt Anchor's
   per-field `ReadEval/WriteEval` function style and its commutativity
   checks wholesale. Decide during phase 3, after reading
   `SinkYieldPrinter.scala` closely.
3. **`\old(e.f)` receiver semantics**: Melvin resolves the whole inner
   expression in the old store (`pre_f[pre_this]`); Boogie's `old()` does the
   same, and receivers are locals (unchanged by interference), so pre/post
   receiver values coincide except across local reassignment — document
   this and keep Melvin's rule.
4. **Existing `int[]` examples** change meaning (§1.3). Audit `examples/`
   and `tests/` during phase 4; keep `value`/`List` for immutable
   spec-level sequences.
5. **interp.py state-space growth** with heaps; keep `max_states` and add
   address canonicalization only if the oracle examples time out.
