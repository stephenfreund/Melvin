# Formal Development

### How Melvin implements Mover Logic by reduction to Boogie

*This document is a companion to the Mover Logic paper (Flanagan and Freund,
“Mover Logic: A Concurrent Program Logic for Reduction and Rely–Guarantee
Reasoning,” ECOOP 2024, [PDF](https://www.cs.williams.edu/~freund/papers/24-ecoop.pdf)).
It assumes familiarity with reduction, rely–guarantee reasoning, and the effect
system of that paper, and describes how **Melvin** — a Python implementation of
Mover Logic — discharges the logic’s proof obligations by lowering each of them
to an independent [Boogie](https://github.com/boogie-org/boogie) procedure.
It describes the system as it stands on the `main` branch, whose store is a flat
map from scalar global and thread-local names to values; the extension to a
mutable object heap (the `objects` branch) is deferred to a later companion.*

Throughout, we use the paper’s running example — a lock-protected shared counter
`x` with an `atomic add()` and a client thread that maintains the data invariant
`even(x)` — and we quote the **actual** Boogie that Melvin generates for it
(`melvin examples/counter.mml --show-bpl`), lightly trimmed for length. The
example source is [`examples/counter.mml`](examples/counter.mml).

---

## 1. Overview

Melvin realises the judgements of Mover Logic as verification conditions in the
Boogie intermediate verification language. The pipeline is

```
.mml source → lexer → parser → AST → type checker → VC generator → Boogie → mapped diagnostics
```

and its semantic core is the **verification-condition generator**,
[`melvin/vcgen.py`](melvin/vcgen.py). The organising principle of the whole
development is stated once and adhered to everywhere:

> **One obligation, one procedure.** Every proof obligation of Mover Logic — the
> body of each function definition, each of the four mover-specification
> *validity* conditions, each run-time *state* side condition, and each
> rely-well-formedness check — becomes a *separate*, self-contained Boogie
> procedure. Boogie verifies the procedures independently; the program is
> accepted iff every procedure verifies.

This one-to-one structure is what lets Melvin map a Boogie failure back to the
exact source construct and paper obligation that failed (§11), and it keeps each
generated procedure small enough to read against the corresponding rule.

The correspondence between the paper and the implementation is summarised in a
table in §13. The reader who wants the shortest path to the encoding can read
§4 (the effect lattice), §6 (the per-procedure store model), and §7 (the
definition rules), which together contain the essential ideas.

---

## 2. The source language

Melvin’s surface language is the Mover Logic Language (MLL) of the paper. A
program is a sequence of declarations:

* **Shared variables and locks** carry a **mover specification** — a list of
  clauses assigning a mover to each access under a state condition (§5). A
  `lock` is a distinguished integer global holding `0` (free) or the id of the
  holding thread.
* **Functions** are either `atomic`, specified by a precondition, a
  postcondition, and a declared atomic mover, or **non-atomic**, specified by a
  rely `R`, a guarantee `G`, a precondition, and a postcondition.
* An **`init`** predicate constrains the initial store, and each **`thread`**
  block forks a thread (in the paper’s non-preemptive formalisation, each thread
  begins at a `yield`).

The statement forms are exactly those of the operational semantics: `skip`,
`yield`, assignment, `acquire`/`release`, `if`, `while`, function `call`,
`assert`, `wrong`, and the atomic conditional actions used by lock-free code
(`cas` and the “unstable read” of a racy location). The AST dataclasses are in
[`melvin/ast_nodes.py`](melvin/ast_nodes.py); each node carries a source `Span`
so that diagnostics point at the originating token. The front end (lexer,
parser) is otherwise unremarkable and is not discussed further here; the
load-bearing static analysis is the **action classification** of §3.

---

## 3. Action classification

Before any verification condition is emitted, the type checker
([`melvin/types.py`](melvin/types.py)) infers the type of every thread-local
(any identifier that is not a declared global is a thread-local, per the paper’s
`r_tid` convention) and — crucially — **classifies every assignment** as exactly
one of:

* a **global write** `X = e`, where the checker requires the right-hand side `e`
  to mention only thread-locals (a global on the right is rejected: “read it
  into a local first”);
* a **global read** `l = X`, required to have exactly this shape (one global,
  read directly into a local); or
* a **purely local computation**, which touches no shared state.

This classification, recorded in `TypeInfo.assign_kind`, is what determines the
*mover* of each action and hence which obligations are emitted for it (a local
computation is a both-mover and changes no effect; a global access consults the
variable’s mover specification). The restriction to single-global,
locals-only actions is precisely the paper’s condition that each atomic action
touch the shared store at most once, and it is what makes the state-sensitive
mover of an action well defined. The checker also rejects the statically
detectable errors the logic forbids up front: assigning through a lock,
recursion in an atomic function (`M-def-atomic` requires atomic functions to be
non-recursive), and calls to unknown functions.

---

## 4. The mover-effect lattice

The heart of the logic is a six-element lattice of **effects**, implemented in
[`melvin/effects.py`](melvin/effects.py) as a faithful, checkable transcription
of the paper’s figure:

```
    e  ::=  Y | B | R | L | N | E

    Y   yield                      B   both-mover
    R   right-mover                L   left-mover
    N   non-mover                  E   error
```

ordered along a single chain except that `R` and `L` are incomparable:

$$
Y \;\sqsubseteq\; B \;\sqsubseteq\; \{R, L\} \;\sqsubseteq\; N \;\sqsubseteq\; E.
$$

A run of actions is **reducible** iff its overall effect is not `E`; the DFA
that the effect algebra encodes accepts exactly the reducible sequences of the
form `R*[N]L*` separated by yields. The lattice carries three operations, all
transcribed verbatim from the paper’s tables so that the implementation is a
mechanically checkable copy of the formal definitions:

* **join** `⊔` (least upper bound): the only incomparable pair is `{R, L}`,
  whose join is `N`;
* **sequential composition** `;` (`seq`), the table below;
* **iterative closure** `*` (`star`): `Y* = Y`, `B* = B`, `R* = R`, `L* = L`,
  `N* = E`, `E* = E`.

```
  ;   Y   B   R   L   N   E          The identity of ; is B (it is the effect
  Y   Y   Y   Y   L   L   E          of skip). The empty run joins to Y. A
  B   Y   B   R   L   N   E          non-mover after a non-mover, or a
  R   R   R   R   N   N   E          right-mover after a left-mover, yields E,
  L   Y   L   E   L   E   E          which is how the R*[N]L* discipline is
  N   R   N   E   N   E   E          enforced purely arithmetically.
  E   E   E   E   E   E   E
```

**Encoding into Boogie.** So that the Boogie side computes the *same* algebra as
the Python side, the fixed prelude ([`melvin/prelude.py`](melvin/prelude.py))
emits the six effects as integer codes

```
Y = 0   B = 1   R = 2   L = 3   N = 4   E = 5
```

and generates two total `{:inline}` Boogie functions, `seqEff(a,b)` and
`leqEff(a,b)`, whose bodies are nested `if`/`else` expressions produced *by
enumerating the Python tables* — the prelude literally walks `effects.seq` and
`effects.leq` over all `6×6` inputs and prints the resulting constant for each.
For instance the composition table becomes:

```boogie
function {:inline} seqEff(a: int, b: int) returns (int) {
  (if a == 0 then (if b == 0 then 0 else (if b == 1 then 0 else (if b == 2 then 0
   else (if b == 3 then 3 else (if b == 4 then 3 else (if b == 5 then 5 else 5))))))
   else (if a == 1 then ... ) ...) }
```

Because the tables are generated from the single source of truth in
`effects.py`, the Python effect algebra and its Boogie image cannot drift apart;
the `tests/test_effects*.py` suite additionally checks the algebraic laws (e.g.
associativity of `;`, `star` as a fixpoint of `;`) the paper relies on.

---

## 5. Mover specifications and state-sensitive movers

A shared variable’s mover specification is a list of **clauses**, each of the
form `access mover if condition`, where `access ∈ {read, write}` (a lock uses
`write` for both acquire and release) and `condition` is a two-store predicate
over the globals, `tid`, and `\old`. For the counter:

```
var  int x   both-mover if m == tid;
lock m       write right-mover if \old(m) == 0 && m == tid
             write left-mover  if \old(m) == tid && m == 0;
```

The mover of a *concrete* access is therefore **state-sensitive**: acquiring `m`
(`0 → tid`) is a right-mover, releasing it (`tid → 0`) is a left-mover, and every
access to `x` is a both-mover precisely while the accessing thread holds `m`.

Melvin never approximates this mover when checking an actual access. For each
access it emits the *exact* mover as a Boogie `if`/`else` cascade over the
clauses — `\old` in a clause binding to the pre-action snapshot `pre_` and bare
names to the post-action store `v_` — falling through to the error code `5` if
no clause applies (`Lowerer._mover_expr` / `_mover_ite`). It stores the result
in the ghost `mv`, asserts the access is permitted, and folds the mover into the
running effect, asserting reducibility:

```boogie
mv := (if (v_m == tid) then 1 else 5);   // the exact mover of the write x = t
assert mv != 5;                          // access legality: some clause applies
eff := seqEff(eff, mv);                  // fold into the running effect
assert eff != 5;                         // reducibility: still R*[N]L*
```

The two assertions carry source-accurate messages: `mv != 5` fails as “write of
`'x'` is not permitted here by its mover specification (possible data race)”,
and `eff != 5` as “…breaks reducibility here: this reducible sequence is not of
the form `R*[N]L*` (insert a yield to split it)”.

The `acquire`/`release`/`cas` actions reuse this machinery. An `acquire(m)` is
lowered as a guarded write of `tid` into `m` (`assume pre_m == 0; v_m := tid`)
followed by the write-mover selection; a `release(m)` writes `0`; a successful
`cas` writes its new value and takes the target’s write-mover, while a failing
`cas` is the store identity and a both-mover.

---

## 6. The proof state inside a procedure

Every function-body procedure verifies **one arbitrary thread** `tid` (`assume
tid > 0`), and models the store and the proof state with a fixed family of
Boogie variables, one group per store item `g`:

| Boogie var | denotes |
|------------|---------|
| `v_g`   | the **current** value of `g` |
| `o_g`   | snapshot at the **start of the current reducible sequence** — what `\old` denotes in `P`, `Q`, and the guarantee `G` |
| `pre_g` | snapshot **just before an action** — what `\old` denotes in a mover clause |
| `py_g`  | snapshot **just before a yield** — what `\old` denotes in the rely `R` |
| `ce_g`  | snapshot at a **call site** — what `\old` denotes in a callee’s postcondition |
| `eff`   | ghost `int`, the **running effect** of the current reducible sequence |
| `mv`, `le_save` | scratch: the last action’s mover; the effect saved across a loop |

The four distinct `\old` snapshots are the subtle part of the encoding: Mover
Logic uses `\old` with four different binding sites depending on the assertion
context, and Melvin keeps them in separate arrays rather than trying to reuse
one. `restore_seq_start` (`o_g := v_g` for all items) marks the boundary of a
new reducible sequence, and is invoked exactly where the logic starts one: at a
yield and after a non-atomic call.

The running effect `eff` is initialised to `B` (code `1`), the identity of `;`
and the effect of `skip`. Each action composes its exact mover into `eff` (§5),
and the invariant `eff != E` after every action is what mechanises the
reducibility premise of the definition rules.

---

## 7. Verification-condition generation for definitions

### 7.1 Atomic functions — `M-def-atomic`

For an atomic function Melvin snapshots the entry store into `o_` (so `\old`
throughout the body denotes the entry state), assumes the precondition, runs the
body with `eff` tracking the effect, and finally asserts the postcondition and
that the body’s effect is **at most the declared atomic mover** (`M-conseq`).
The default atomic mover is `N`. Here is the generated procedure for `add()`,
trimmed to the interesting lines:

```boogie
procedure {:entrypoint} Def_add()
{
  // ... var declarations for v_/o_/pre_/py_/ce_ of x, m, n, t, result ...
  assume tid > 0;
  o_x := v_x;  o_m := v_m;  o_n := v_n;  o_t := v_t;  o_result := v_result;  // \old = entry
  assume true;                       // requires
  eff := 1;                          // eff := B (skip)

  // acquire(m):  guarded write 0 -> tid, a right-mover
  pre_x := v_x;  pre_m := v_m;
  assume pre_m == 0;
  v_m := tid;
  mv := (if ((pre_m == 0) && (v_m == tid)) then 2 else (if ((pre_m == tid) && (v_m == 0)) then 3 else 5));
  assert mv != 5;  eff := seqEff(eff, mv);  assert eff != 5;

  // t = x:  a read of x, a both-mover because m == tid
  pre_x := v_x;  pre_m := v_m;
  mv := (if (v_m == tid) then 1 else 5);
  assert mv != 5;  eff := seqEff(eff, mv);  assert eff != 5;
  havoc v_t;  assume v_t == v_x;

  // t = t + n:  local computation (both-mover, no effect change)
  pre_t := v_t;  havoc v_t;  assume v_t == (pre_t + v_n);

  // x = t:  a write of x, a both-mover because m == tid
  pre_x := v_x;  pre_m := v_m;
  v_x := v_t;
  mv := (if (v_m == tid) then 1 else 5);
  assert mv != 5;  eff := seqEff(eff, mv);  assert eff != 5;

  // result = t:  local
  pre_result := v_result;  havoc v_result;  assume v_result == v_t;

  // release(m):  write tid -> 0, a left-mover
  pre_x := v_x;  pre_m := v_m;
  v_m := 0;
  mv := (if ((pre_m == 0) && (v_m == tid)) then 2 else (if ((pre_m == tid) && (v_m == 0)) then 3 else 5));
  assert mv != 5;  eff := seqEff(eff, mv);  assert eff != 5;

  assert (((v_x == (o_x + v_n)) && (v_result == v_x)) && (v_m == o_m));  // postcondition Q
  assert leqEff(eff, 4);                                                 // eff <= declared mover (N)
}
```

Two encoding choices in this procedure are worth calling out. First, **local
assignments are lowered as `havoc l; assume l == e`** rather than a direct `:=`.
This is logically identical (havoc, then pin to the exact value) but keeps the
local a named model constant, so it appears in a Boogie counterexample; a
self-referential right-hand side such as `t = t + n` is handled by snapshotting
the pre-value first. Second, the *composed* effect of `add()` is exactly
`B;R;B;B;B;L = R;L`, which the reducibility asserts accept and the final
`leqEff(eff, 4)` confirms is `⊑ N` — `add()` is a single reducible sequence, so
it earns the precise, client-independent postcondition `x == \old(x)+n && result
== x`.

### 7.2 Non-atomic functions — `M-def-non-atomic`

A non-atomic function is verified the same way, but its body must consist of
**reducible sequences separated by yields and must end in a yield**: the closing
obligation is `leqEff(eff, R)` rather than `leqEff(eff, mover)`. Its
postcondition is interpreted as a one-store (stable) predicate. The generated
`client()` procedure shows the yield encoding (§8) and a call encoding (§9); its
frame is:

```boogie
procedure {:entrypoint} Def_client()
{
  ...
  assume tid > 0;
  o_x := v_x; o_m := v_m; ...;         // \old = entry
  assume even(v_x);                    // requires
  eff := 1;                            // eff := B
  //  yield ; n = 2 ; add() ; yield ; n = 2 ; add() ; yield   (bodies in §8–§9)
  assert even(v_x);                    // postcondition Q (stable)
  assert leqEff(eff, 2);               // body is reducible & ends in a yield: eff <= R
}
```

---

## 8. Yields, guarantees, and interference

A `yield` is where a non-atomic function both **discharges its guarantee** for
the reducible sequence just completed and **admits environment interference**
before the next sequence. `emit_yield` encodes it in three moves (compare the
`client()` body):

```boogie
// P => G:  the guarantee must hold over (\old = sequence start = o_)
assert (even(o_x) ==> even(v_x));

// interference:  snapshot the pre-yield store, havoc the globals, assume the rely once
py_x := v_x;  py_m := v_m;
havoc v_x;  havoc v_m;
assume (even(py_x) ==> even(v_x));

// start a new reducible sequence and record the yield in the effect
o_x := v_x;  o_m := v_m;  o_n := v_n;  o_result := v_result;
eff := seqEff(eff, 0);               // ; Y
```

The single assumed rely step models the paper’s *arbitrary* interference `R*`.
This is sound only because the rely is proved to be its own reflexive–transitive
closure (`R = R*`), discharged separately in §10. A yield inside an atomic
function is unreachable by construction and is lowered to `assert false` (“atomic
functions may not contain a yield”), since atomic functions take `G = false`.

Conditionals (`if`) are lowered to a Boogie nondeterministic `if (*) { … } else
{ … }` in which each arm first *commits to the test* — `assume c` on the true
arm, `assume !c` on the false arm, and for a `cas` the success arm performs the
guarded write while the failure arm is the identity — and then runs its body, so
that the exact effect of the test is composed on each path.

---

## 9. Function calls — `M-call`

A call is verified against the callee’s specification, not its body. Melvin
snapshots the call site into `ce_` (the callee’s `\old`), asserts the callee’s
precondition, **havocs exactly the store locations the callee may write**
(transitively through nested calls — since Mover Logic omits frame conditions,
the callee’s postcondition must pin what matters), assumes the callee’s
postcondition, and folds the callee’s effect into `eff`. For the `add()` call
inside `client()`:

```boogie
ce_x := v_x; ce_m := v_m; ce_n := v_n; ce_result := v_result;  // \old for callee Q
assert true;                                                    // add()'s precondition
havoc v_x; havoc v_m; havoc v_result;                           // add() writes x, m, result
assume (((v_x == (ce_x + v_n)) && (v_result == v_x)) && (v_m == ce_m));  // add()'s Q
eff := seqEff(eff, 4);                                          // ; (add's atomic mover N)
assert eff != 5;
```

A call to an **atomic** callee composes the callee’s declared atomic mover (here
`N = 4`) into `eff`. A call to a **non-atomic** callee is different: it may only
appear where the current reducible sequence is trivial, so after assuming the
callee’s postcondition Melvin restarts the sequence (`restore_seq_start`) and
composes `R`, matching the paper’s `M-call` rule for non-atomic callees.

---

## 10. Loops — `M-while`

Loops are the one place the encoding blends an exact check with a static
approximation, and the split is deliberate. `emit_while`:

1. asserts the loop invariant on entry, then performs a **havoc cut**: it havocs
   every global *and thread-local the body may modify* and assumes the
   invariant, so the body is verified from an arbitrary invariant-satisfying
   state. (Havocking the modified locals is essential: otherwise the exit test
   would be evaluated against their pre-loop values and could render the whole
   continuation vacuously unreachable.)
2. In a nondeterministic `if (*)` it verifies **one arbitrary iteration** with a
   fresh `eff := B`, composing the *exact* successful test and the body, then
   asserts the invariant is preserved and — the key premise — that the
   iteration is a **right-mover or less**, `leqEff(eff, R)`. A reducible loop
   may not commit inside the loop.
3. On exit it composes a *static, state-insensitive* over-approximation of the
   iteration’s effect closure (`star(iter_static)`) with the **exact** failing
   test `A2`, and asserts the loop does not break reducibility in its
   surrounding sequence.

The static per-iteration effect (`_loop_iter_static`, `_stmt_static`) is also
used for a **termination side condition**: a loop whose overall effect is `⊑ L`
(entirely in the post-commit, left-mover region) is rejected at generation time,
because such a loop could fail to terminate after committing. The exactness that
matters for soundness — that each iteration is `⊑ R` — is checked precisely; the
approximation is confined to the surrounding-effect and termination bookkeeping,
which is a sound over-approximation.

---

## 11. Mover-specification validity

A mover specification is only meaningful if it is **valid**: the movers it
assigns must actually justify the commuting reorderings that reduction relies
on. Melvin checks all four of the paper’s validity conditions, for the relevant
pairs of variables `X` (accessed by thread `t`) and `Y` (accessed by thread
`u`, with `t ≠ u`):

1. a right-mover of `t` commutes to the right of a following non-mover of `u`;
2. a left-mover of `u` commutes to the left of a preceding non-mover of `t`;
3. an action of `t` does not change the mover `u` computes; and
4. a non-mover of `t` cannot cause a left-mover of `u` to block.

**Condition (3)** is a direct assertion that a write to `X` by `t` leaves `Y`’s
read- and write-mover for `u` unchanged (guarding that `t`’s own write is
well-defined). Melvin emits one `Valid3_X_Y` procedure per ordered pair; e.g.
that a write to `m` cannot change `x`’s (both-)mover for another thread:

```boogie
procedure {:entrypoint} Valid3_m_x()
{
  var s_x: int; var s_m: int; var s2_m: int; var t: int; var u: int;
  assume t > 0 && u > 0 && t != u;
  assume (if ((s_m == 0) && (s2_m == t)) then 2 else (if ((s_m == t) && (s2_m == 0)) then 3 else 5)) != 5;
  assert ((if (s_m == u) then 1 else 5)) == ((if (s2_m == u) then 1 else 5));   // read-mover of x unchanged
  assert ((if (s_m == u) then 1 else 5)) == ((if (s2_m == u) then 1 else 5));   // write-mover of x unchanged
}
```

**Conditions (1), (2), (4)** are commuting conditions on pairs of writes. The
paper states them with an existentially quantified witness store; Melvin
discharges them without quantifier alternation by **constructing the witness
explicitly**. Because a write is modelled exactly as in the paper — `⟨X := v⟩`
for an arbitrary, store-independent, local-determined value `v` — the two write
actions `A1 = ⟨X := v1⟩` (thread `t`) and `A2 = ⟨Y := v2⟩` (thread `u`) are
deterministic, so applying them in the opposite order gives a concrete witness
and each condition becomes an ordinary assertion: *under the condition’s mover
hypotheses, the two orders produce the same store.* For distinct `X ≠ Y` this
holds structurally; for `X = Y` it forces the two writes to agree, so a spec that
would let two threads make conflicting non-both-mover writes to the same location
is rejected. Reads and other store-identity actions commute trivially and are
omitted. Condition (1) for the two writes of `x`:

```boogie
procedure {:entrypoint} Valid1_x_x()
{
  var s_x: int; var s_m: int; var v1: int; var v2: int; var t: int; var u: int;
  assume t > 0 && u > 0 && t != u;
  assume leqEff((if (s_m == t) then 1 else 5), 2);   // M(A1,t,σ)  <= R
  assume leqEff((if (s_m == u) then 1 else 5), 4);   // M(A2,u,σ') <= N
  assert (v2 == v1) && (s_m == s_m);                 // the two orders agree
}
```

---

## 12. The run-time state rule and rely well-formedness

Two families of obligations are independent of any single function body and
close the gap between per-thread reasoning and a whole concurrent program.

**`M-state`** (`gen_state_checks`) discharges, over the set of functions actually
run by `thread` blocks:

* **`I ⇒ G`** — each guarantee is reflexive (`Reflexive_client`);
* **`G_t ⇒ R_u`** — each thread role’s guarantee is contained in every *other*
  role’s rely, and in its own rely when at least two threads run that role
  (`GR_client_client`); and
* **`init ⇒ pre`** — the initial store satisfies every thread’s precondition
  (`Init_establishes`).

```boogie
procedure {:entrypoint} GR_client_client() {          // G[client] => R[client]
  var v_x, o_x, v_m, o_m: int; var t, u: int; assume t > 0 && u > 0 && t != u;
  assume (even(o_x) ==> even(v_x));                    // assume the guarantee
  assert (even(o_x) ==> even(v_x));                    // prove the rely
}
```

**Rely well-formedness** (`gen_rely_checks`) discharges, for every non-atomic
function, that its rely equals its own reflexive–transitive closure — both
**reflexive** (`R(s,s)`) and **transitive** (`R;R ⇒ R`):

```boogie
procedure {:entrypoint} RelyTrans_client() {
  var a_x, b_x, c_x, a_m, b_m, c_m: int; var tid: int; assume tid > 0;
  assume (even(a_x) ==> even(b_x));
  assume (even(b_x) ==> even(c_x));
  assert (even(a_x) ==> even(c_x));
}
```

This is exactly the property that licenses §8’s use of a **single** assumed rely
step to summarise the arbitrarily-many interference steps `R*` the paper
quantifies over. Guarantees need no such closure check: they are asserted one
reducible sequence at a time, and all multi-step composition is absorbed on the
rely side.

---

## 13. Fidelity and approximations

Melvin is designed so that every obligation whose *soundness* depends on
precision is discharged **exactly**, and approximation is confined to places
where an over-approximation can only reject more programs, never accept a wrong
one. It is worth being explicit about where each falls.

**Exact.**

* *State-sensitive movers.* Every actual access composes the precise mover
  selected by the full clause cascade over the live store (§5); Melvin never
  substitutes a variable’s join-of-clauses static mover for a real access.
* *Validity conditions (1)–(4).* Checked exactly, with the commuting witness
  *constructed* from the deterministic write model rather than left as a
  quantifier alternation (§11).
* *Effect algebra.* The Boogie `seqEff`/`leqEff` are generated from the same
  `effects.py` tables the Python side uses, so the two cannot disagree (§4).
* *Reducibility.* The `eff != E` assertion after every action, and the closing
  `leqEff(eff, mover)` / `leqEff(eff, R)`, mechanise `R*[N]L*` exactly on every
  path through a body.

**Over-approximate (sound; may reject).**

* *Loops.* Each iteration’s `⊑ R` check is exact, but the loop’s
  *surrounding-effect* composition and the *termination* side condition use a
  static, state-insensitive per-iteration effect (§10). A loop whose exact
  behaviour is fine but whose static effect looks non-reducing would be rejected.
* *Frames at calls.* Mover Logic omits frame conditions; Melvin havocs the
  (transitively) written locations and relies on the callee’s postcondition to
  re-establish facts (§9). A callee that changes a location without mentioning it
  in its postcondition loses that fact at the call site — sound, but the caller
  must be told what it needs.

**Justified assumption.**

* *Single rely step for `R*`.* Sound precisely because rely well-formedness
  (`R = R*`) is proved for every non-atomic function (§8, §12).

These boundaries are exercised directly by the test suite: mutation tests
confirm that programs which *should* fail still fail (the checker is not
vacuous), and the corner-case examples in `examples/` (write-guarded access,
nested control, atomic-calls-atomic, and the rejected programs `racy_bad`,
`double_release`, `both_mover_loop`, `rely_not_transitive`,
`rely_not_reflexive`, …) pin each obligation.

---

## 14. The interpreter as a differential oracle

Independently of the Boogie encoding, Melvin ships a reference **small-step
interpreter** ([`melvin/interp.py`](melvin/interp.py), `melvin-run`) that
implements MLL’s operational semantics directly and an explicit-state scheduler
that explores *all* thread interleavings up to a state bound. It answers exactly
one question: **is a state in which some thread is about to execute `wrong`
reachable?** (An `assert B` desugars to `if B then skip else wrong`, so a failed
assertion is a reachable `wrong`.)

This gives a cheap, trustworthy check on the verifier’s soundness theorem — *if
the tool verifies a program, the program does not go wrong.* For every program
the verifier accepts, the interpreter must find **no** reachable `wrong`; if it
ever did, that would be a soundness bug in the logic’s encoding. Conversely, a
program the interpreter shows *can* go wrong must be rejected by the verifier.
Because the interpreter is a direct, sequential implementation of the semantics,
it is far simpler than the VC generator and shares none of its machinery, which
is what makes it a meaningful differential oracle (`tests/test_semantics_oracle.py`).

---

## 15. Correspondence to the paper

| Paper | Melvin |
|-------|--------|
| Effect domain `Y⊑B⊑{R,L}⊑N⊑E`, tables for `;`, `*`, `⊔` | [`effects.py`](melvin/effects.py); Boogie image in [`prelude.py`](melvin/prelude.py) (`seqEff`, `leqEff`) |
| Reducible sequence `R*[N]L*` | `eff` ghost + `assert eff != E` after each action ([`vcgen.py`](melvin/vcgen.py) `_emit_mover`) |
| Mover specifications; state-sensitive movers | clause cascade `_mover_expr` / `_mover_ite`; classification in [`types.py`](melvin/types.py) |
| `M-def-atomic` | `gen_atomic_fn` |
| `M-def-non-atomic` | `gen_nonatomic_fn` |
| `M-conseq` | closing `leqEff(eff, mover)` / `leqEff(eff, R)` |
| yield: `P ⇒ G`, interference `R*`, sequence restart | `emit_yield` |
| `M-call` (atomic / non-atomic) | `emit_call` |
| `M-while` | `emit_while` + `_loop_iter_static` |
| Validity (1)–(4) | `gen_validity`, `_validity_commute`, `_validity3` |
| `M-state` (`I⇒G`, `G_t⇒R_u`, init) | `gen_state_checks` |
| `R = R*` well-formedness | `gen_rely_checks` |
| Soundness (“verified ⇒ does not go wrong”) | differential oracle [`interp.py`](melvin/interp.py) |
| `\old` binding sites (`P/Q/G`, mover clause, rely, callee `Q`) | snapshots `o_`, `pre_`, `py_`, `ce_` |

Diagnostics are attached at the point each `assert` is emitted
(`Emitter.assert_` records `line → (span, message)` in
[`boogie_backend.py`](melvin/boogie_backend.py)), so that a Boogie refutation of
any one procedure is reported against the precise source construct and the exact
Mover Logic obligation that failed.

---

*The extension of this development to a mutable object heap — reachable-heap
isomorphism for final states, receiver-field mover tracking, and heap
counterexamples decoded from Boogie models — lives on the `objects` branch and
will be described in a follow-on companion.*
