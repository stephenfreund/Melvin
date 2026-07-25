<img width="200" height="200" alt="melvin-small" src="https://github.com/user-attachments/assets/f969a50d-8e68-427b-878f-12a4677cd2ee" />

# Melvin

**Melvin** is a verifier for **Mover Logic** — the reduction-based
rely-guarantee program logic of
[Flanagan & Freund (ECOOP 2024)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2024.16)
— implemented in Python with **Boogie** as the theorem prover.

Mover Logic extends rely-guarantee (RG) logic with Lipton's theory of
*reduction*.  By proving that a function is **atomic** (its body is a single
*reducible* sequence of movers), the logic gives that function a precise,
*client-independent* postcondition, instead of the weak, stabilized
postconditions that plain RG logic forces on shared-memory code.  This
"disentangles" a library's specification from any particular client's data
invariant and synchronization discipline.

Try our Melvin system on the [web](https://melvin-demo.gss8b1ryfh8jc.us-east-1.cs.amazonlightsail.com/)!

---

## Installation

**Requirements:** Python 3.9+ and the **Boogie** verifier (with a Z3 backend).

```bash
pip install "melvin-verifier[z3]"     # the verifier, the demo server, and Z3
melvin-install-boogie        # installs Boogie (needs the .NET SDK)
melvin --doctor              # report what Melvin can see
```

That gives you four commands: `melvin` (verify), `melvin-run` (the reference
interpreter), `melvin-server` (the web demo), and `melvin-install-boogie`.

**Why two steps?**  Z3 has a PyPI wheel, so the `[z3]` extra installs it like
any Python dependency.  Boogie does not: it is a .NET tool, so it has to come
from NuGet.  `melvin-install-boogie` runs

```bash
dotnet tool install --tool-path ~/.melvin/tools Boogie
```

which needs the .NET SDK (`brew install dotnet-sdk`,
`apt-get install dotnet-sdk-8.0`, `winget install Microsoft.DotNet.SDK.8`, or
<https://dotnet.microsoft.com/download>).  Installing into `~/.melvin/tools`
rather than globally keeps it out of your `PATH`; Melvin looks there itself.
Already have Boogie?  `melvin-install-boogie` leaves it alone (`--force`
overrides), or you can just point Melvin at it:

```bash
export MELVIN_BOOGIE=/path/to/boogie
```

Boogie is located, in order, from `MELVIN_BOOGIE`, then `boogie`/`Boogie` on
`PATH`, then `~/.melvin/tools`, then `~/.dotnet/tools`.  Z3 is found from
`MELVIN_Z3`, then `PATH`, then the Python environment's script directory —
that last case (a `pip install melvin-verifier[z3]` under pipx/uv, where the script
directory is not on `PATH`) is handled by passing Boogie an explicit
`/proverOpt:PROVER_PATH`.  `melvin --doctor` prints exactly what was found.

### From a checkout

```bash
git clone https://github.com/stephenfreund/Melvin.git
cd Melvin
pip install -e ".[dev]"      # verifier + demo server + Z3 + test/build tools
melvin-install-boogie
pytest tests/ -q
```

The `.mml` examples ship with the package, so pip users have them too —
`melvin --doctor` prints the directory.

> The distribution is named **`melvin-verifier`** on PyPI (plain `melvin` is
> taken by an unrelated project); the import package and the commands are
> `melvin`.

## Running it

```bash
melvin examples/counter.mml                 # verify one program
melvin examples/*.mml                        # verify several
python -m melvin examples/counter.mml        # equivalent, no console script
melvin examples/counter.mml --show-bpl       # also print the generated Boogie
melvin examples/counter.mml --show-movers    # print the program with mover letters
melvin examples/counter.mml --emit-bpl out.bpl   # save the generated Boogie
melvin --timeout 60 examples/counter.mml     # cap Boogie at 60s for this file
```

### Mover annotations (`--show-movers`)

`--show-movers` prints each file with a margin letter classifying every
statement — `R`/`B`/`L`/`N` for its mover, `Y` at yields — like the annotated
figures in the paper:

```console
$ melvin examples/counter.mml --show-movers
== examples/counter.mml (movers) ==
   | add() {
 R |   acquire(m);
 B |   t = x;          // read of x     (both-mover: lock held)
 B |   t = t + n;      // local compute (both-mover)
 B |   x = t;          // write of x    (both-mover: lock held)
 B |   result = t;     // local
 L |   release(m);
   | }
...
```

The letters come from the static clause classification, sharpened for actions
whose transition is known (an `acquire` is the `0 → tid` write, so it shows
the right-mover clause rather than the join of all clauses); verification
itself always uses the exact state-sensitive movers in Boogie. Calls to
atomic functions show the declared atomic mover; calls to non-atomic
functions get no letter. The web demo displays the same letters as colored
gutter chips after verification.

### Running a program (the reference interpreter)

Besides *verifying* a program, you can *run* it under the reference operational
semantics with `melvin-run`.  It explores **all thread interleavings** and
reports whether any of them can go wrong (fail an assertion or reach `wrong`):

```console
$ melvin-run examples/oracle_safe.mml
SAFE: no interleaving reaches `wrong` (explored 837 states, exhaustive).

$ melvin-run examples/oracle_unsafe.mml --trace
UNSAFE: some interleaving reaches `wrong` (explored 11 states).
  interleaving (thread:next-step):
    t2:Call_ -> t2:Yield -> t2:Assert -> t2:Call_ -> t2:Acquire -> ...
```

`--max-states N` bounds the search (reported as `UNKNOWN` if hit); `--trace`
prints an interleaving that reaches `wrong`. Only complete, thread-bearing
programs can be run (functions alone are not executed). Exit codes: `0` safe,
`1` a `wrong` is reachable, `2` a front-end error / no threads, `3` bound hit.
This interpreter is also the verifier's differential oracle (see *How the
implementation is validated*).

**Timeouts.** Each file gets a wall-clock verification budget (default **300 s =
5 minutes**), adjustable with `--timeout SECONDS`.  If Boogie does not finish in
time it is killed and the file is reported as timed out (not crashed):

```console
$ melvin --timeout 5 hard.mml ; echo "exit=$?"
== hard.mml ==
verification timed out:
error: verification timed out after 5s (raise the limit with --timeout)
exit=2
```

**Exit status:** `0` if every file verifies, `1` if some file is refuted, and
`2` if some file timed out — so scripts can tell a genuine refutation from an
exhausted budget.

## Quick start — examples to try and their expected output

Verify the running example (an atomic, lock-protected counter with an `even(x)`
client):

```console
$ melvin examples/counter.mml
== examples/counter.mml ==
verified (23 Boogie proof obligation(s) discharged)
```

The whole example suite — every file below should verify except the
intentionally broken one:

```console
$ melvin examples/counter.mml examples/counter_client2.mml \
             examples/spinlock.mml examples/queue.mml examples/stack.mml
== examples/counter.mml ==
verified (23 Boogie proof obligation(s) discharged)

== examples/counter_client2.mml ==
verified (23 Boogie proof obligation(s) discharged)

== examples/spinlock.mml ==
verified (19 Boogie proof obligation(s) discharged)

== examples/queue.mml ==
verified (6 Boogie proof obligation(s) discharged)

== examples/stack.mml ==
verified (6 Boogie proof obligation(s) discharged)
```

The broken example is **rejected**, with the error mapped to the exact racy
line (a write/read of `x` performed without holding the lock):

```console
$ melvin examples/racy_bad.mml ; echo "exit=$?"
== examples/racy_bad.mml ==
racy_bad.mml:18:3: error: read of 'x' is not permitted here by its mover specification (possible data race)
      t = x;          // <-- race: reads x without holding m
      ^
exit=1
```

Try breaking a *good* program to see other diagnostics — e.g. delete a `yield;`
from `client()` in `counter.mml` and you get a reducibility error
(`call to add() breaks reducibility here`: two non-movers with no yield between
them); change `add`'s postcondition to `x == \old(x) + 1` and you get
`postcondition of atomic add() may not hold`.

## Web demo

There is a browser front end (examples menu, editor with error squiggles,
generated-Boogie view, and a Run-all-interleavings button) backed by a small
verification server that runs locally or on Amazon Lightsail:

The server ships with the package, so no extra install is needed:

```bash
melvin-server                               # then open http://127.0.0.1:8000
melvin-server --reload                      # or: uvicorn melvin_server.app:app --reload
```

See [`melvin_server/README.md`](melvin_server/README.md) for the Docker image and the Lightsail
deployment script.

## Releasing

Version lives in exactly one place: `__version__` in
[`melvin/__init__.py`](melvin/__init__.py) (`pyproject.toml` reads it).  To cut
a release:

1. bump `__version__`, commit, push;
2. publish a GitHub Release whose tag is `v<that version>`.

[`.github/workflows/release.yml`](.github/workflows/release.yml) then checks
that the tag and `__version__` agree, builds the sdist + wheel, smoke-tests the
wheel in a clean environment, publishes to PyPI, and redeploys the demo image
to Lightsail.  [`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs the
test suite (Python 3.9/3.11/3.13, with Boogie installed the same way users
install it), the packaging smoke test, and the Docker build on every push.

One-time repository setup for the release workflow:

| Setting | Purpose |
|---|---|
| PyPI [trusted publisher](https://docs.pypi.org/trusted-publishers/) for `release.yml`, or secret `PYPI_API_TOKEN` | publishing to PyPI (trusted publishing is used when the secret is absent) |
| secret `AWS_ROLE_ARN` (OIDC) or `AWS_ACCESS_KEY_ID` + `AWS_SECRET_ACCESS_KEY` | Lightsail deploy — skipped, not failed, when unset |
| variables `AWS_REGION`, `LIGHTSAIL_SERVICE` | region and service name (default `us-east-1`, `melvin-demo`) |

## Running the tests

```bash
pip install -e ".[test]"
pytest tests/ -q
```

There is a unit-test module per source file (`tests/test_<module>.py`) plus an
end-to-end suite (`tests/test_examples.py`) that verifies every example and
checks that the broken ones are rejected with the right diagnostic. Boogie-
dependent tests self-skip if Boogie cannot be located, so the effect-algebra,
lexer, parser, type-checker, and code-generation tests still run without a
prover installed. There are ~270 tests at ~96% line coverage.

## How the implementation is validated

Unit tests mostly check the code against itself. Real correctness assurance
needs **independent ground truth** and **laws the analysis must obey**. Five
kinds of checks go beyond self-consistency:

### 1. Differential oracle against the operational semantics — the biggest win

`melvin/interp.py` is a from-scratch small-step interpreter of MLL with an
explicit-state scheduler that explores *all* thread interleavings and detects
any reachable `wrong`. It is a much simpler, independent implementation of the
semantics, so it is a trustworthy cross-check of the whole verifier pipeline.

The soundness theorem says *verified ⟹ cannot go wrong*, so
`tests/test_semantics_oracle.py` asserts:

* every program the verifier **accepts** → the interpreter finds **no** reachable
  `wrong` (checked on `counter`, `counter_client2`, `nonatomic_two_yields`,
  `oracle_safe`); and
* a matched **unsafe** variant → the verifier **rejects** *and* the interpreter
  finds a `wrong`.

`examples/oracle_safe.mml` / `oracle_unsafe.mml` demonstrate the pairing: `add2`
(even-preserving) verifies and is proven safe, while `add1` (breaks evenness) is
rejected and the interpreter finds the failing `assert even(x)`. If the verifier
ever had a soundness bug — accepting something unsafe — this catches it.

### 2. Algebraic laws of the effect domain

`tests/test_effects_laws.py` exhaustively proves, over the six-element lattice,
that `;` is associative with `B` as identity and `E` absorbing, and that `;`,
`*`, and `⊔` are monotone — exactly the properties the compositional analysis
and the rule of consequence (M-conseq) depend on. A transcription error in the
paper's `;`/`*`/`⊔` tables would surface here.

### 3. Boogie ⟷ Python algebra agreement

`tests/test_prelude.py` generates a Boogie program asserting `seqEff`/`leqEff`
equal the Python `effects` result on all 36 pairs, so the two implementations of
the effect algebra (Python-side for the static analysis, Boogie-side inside the
generated VCs) cannot drift apart.

### 4. Systematic mutation testing

`tests/test_mutation.py` breaks verified programs in semantics-changing ways
(drop a lock op, drop an interior yield, swap the acquire/release movers, weaken
a postcondition) and asserts each mutant is **rejected** — guarding against the
checker silently becoming vacuous (i.e. against false negatives).

### 5. Generated-Boogie well-formedness

`tests/test_wellformed.py` confirms Boogie can parse, resolve, and type-check
**every** generated program (no `tool_failure`, no resolution errors) across all
language constructs, so code generation never emits malformed Boogie.

---

## The Mover Logic Language (MLL)

MLL is an idealized concurrent language: any number of threads share a store
(a mapping from variables to values) and interleave at the granularity of
individual *actions*.  The surface syntax adds types, curly braces, and named
locals for readability, exactly as the paper's examples do.

### Lexical structure

* **Comments:** `// line` and `/* block */`.
* **Identifiers:** `[A-Za-z_][A-Za-z0-9_]*`.
* **Integers:** decimal literals.
* **Specification escapes:** `\old(e)` and `\result`.
* **Keywords:** `var lock thread init  atomic relies guarantees requires
  ensures  read write  both-mover right-mover left-mover non-mover  if else
  while invariant skip yield wrong assert acquire release cas  true false tid
  result  int bool lock_t value List Optional  forall exists in  head tail Nil
  None Some even`.
* **Operators (by increasing precedence):**
  `<==>` · `==>` · `||` · `&&` · `== != < <= > >=` · `+ -` · `* / %` · `::`
  (list cons, right-assoc.) · unary `! -` · postfix `[ ]` (array index).
  `==>` and `::` are right-associative; the rest are left-associative.

### Program structure

```
program      ::= decl*
decl         ::= var_decl | lock_decl | fn_decl | thread_decl | init_decl

var_decl     ::= 'var' type IDENT mover_clause* ';'
lock_decl    ::= 'lock' IDENT mover_clause* ';'
init_decl    ::= 'init' pred ';'
thread_decl  ::= 'thread' block
fn_decl      ::= fn_spec IDENT '(' ')' block
```

### Types

| Type           | Meaning                                            |
|----------------|----------------------------------------------------|
| `int`          | mathematical integer                               |
| `bool`         | boolean                                            |
| `lock_t`       | a lock (an `int`; `0` = free, otherwise the holder's `tid`) |
| `value`        | an opaque value                                    |
| `List`         | immutable list: `Nil`, `v :: s`, `head(s)`, `tail(s)` |
| `Optional`     | `None` or `Some(v)`                                |
| `T[]`          | array of `T`, indexed with `a[i]`                  |

Thread-local (per-thread) variables are **not declared**: any identifier that is
not a global `var`/`lock` is a thread-local, following the paper's `r_tid`
convention (each thread `t` gets its own copy).  Their types are inferred.
`result` is the distinguished thread-local holding a function's return value
(function parameters and results are likewise passed in thread-locals, since the
core calculus elides them).

### Mover specifications

Each shared variable carries a **mover specification**: an ordered list of
clauses stating the *effect* (mover) of each access under a state predicate.

```
mover_clause ::= ('[' IDENT ']')? ('read' | 'write')? MOVER ('if' pred)?
MOVER        ::= 'both-mover' | 'right-mover' | 'left-mover' | 'non-mover'
```

* An access's effect is the mover of the **first** clause whose guard holds; if
  no clause applies, the access is an **error** (a data race).
* Omitting `read`/`write` makes a clause apply to both.
* A guard `pred` is a two-store predicate over the globals and `tid`, where
  `\old(g)` is the value of `g` *before* the access and `g` its value *after*.
* The optional `[i]` prefix introduces clauses for element accesses `a[i]`.

```mll
var int x  both-mover if m == tid;           // lock-protected: race-free iff m held

lock m  write right-mover if \old(m) == 0 && m == tid   // acquire (0 -> tid): R
        write left-mover  if \old(m) == tid && m == 0;  // release (tid -> 0): L
```

The lattice of effects is `Y ⊑ B ⊑ {R, L} ⊑ N ⊑ E` (yield, both, right/left,
non, error), with sequential composition `;`, iterative closure `*`, and join
`⊔` exactly as in the paper.  A code sequence between two yields is *reducible*
iff its composed effect is not `E`; the accepted shape is `R*[N]L*` (right-movers,
an optional single non-mover "commit", then left-movers).

### Statements

```
stmt ::= 'skip' ';'
       | 'yield' ';'                       -- a point where interference is visible
       | 'wrong' ';'                       -- must be unreachable
       | 'assert' pred ';'                 -- sugar for  if (pred) skip else wrong
       | IDENT '=' expr ';'                -- assignment / write / local compute
       | IDENT '=' '*' IDENT ';'           -- r = *x : unstable read (a right-mover)
       | 'acquire' '(' IDENT ')' ';'       -- lock acquire (blocks if held)
       | 'release' '(' IDENT ')' ';'       -- lock release
       | 'if' '(' cond ')' block ('else' block)?
       | 'while' '(' cond ')' ('invariant' pred)? block
       | IDENT '(' ')' ';'                 -- function call

cond ::= '!' cond                          -- negates a conditional action
       | 'cas' '(' IDENT ',' expr ',' expr ')'   -- compare-and-set
       | expr                              -- a boolean predicate test
```

**Actions and their classification.** Every store operation is an *action*
`A ⊆ Tid × Store × Store`.  Assignments are classified during type-checking:

* `g = e` where `g` is **global** and `e` mentions only locals — a **write** of
  `g`; its mover comes from `g`'s `write` clauses.
* `r = g` where `r` is **local** and `g` is a single **global** — a **read** of
  `g`; its mover comes from `g`'s `read` clauses.
* `r = e` over locals only — a **local computation** (always a both-mover).

Reading a global inside a larger expression, or writing a global from an
expression that mentions another global, is rejected: decompose it into simple
reads first (this keeps every action's mover well-defined, per the paper).

**Conditional actions.** `if`/`while` branch on a *conditional action*
`b = A₁ ⋄ A₂` (a success action and a failure action):

* a boolean predicate `e` — success `assume e`, failure `assume !e`;
* `cas(x, a, b)` — success writes `x` from `a` to `b` (its mover is `x`'s write
  mover); failure is the identity and a both-mover, so a *failing* cas commutes
  freely — the key to lock-free atomicity;
* `!c` swaps the success/failure actions.

`acquire(m)` is the right-moving action `⟨\old(m)=0 ∧ m=tid⟩` (it blocks while the
lock is held); `release(m)` is `⟨m=0⟩`.  `r = *x` is an **unstable read**: it may
load any value into `r` and is treated as a right-mover (a proof technique that
trades knowledge of the value for commutativity; the final `cas` recovers the
value).

### Function specifications

```
fn_spec ::= 'atomic' MOVER? 'requires' pred 'ensures' pred
          | 'relies' pred 'guarantees' pred 'requires' pred 'ensures' pred
```

* **Atomic functions** have a reducible, yield-free body.  `MOVER` is the
  function's overall effect (default `non-mover`); `requires S` is a one-store
  precondition; `ensures Q` is a two-store postcondition where `\old(x)` denotes
  the value on entry.  Atomic functions must be non-recursive.  A call
  `{P} f() {P;Q}` checks `P ⟹ S` and gives the caller the precise `Q`.

* **Non-atomic functions** may contain yields.  `relies R` / `guarantees G` are
  two-store predicates (`\old` = the store before an interference / reducible
  step); `requires S` / `ensures T` are one-store.  The body must consist of
  reducible sequences separated by yields and end in a yield.

### Rely / guarantee and yields

At each `yield`, Mover Logic checks `P ⟹ G` (the just-finished reducible
sequence is summarized by the thread guarantee `G`) and then models arbitrary
interference by other threads with the reflexive-transitive rely `R*`.  Because
`G` summarizes an *entire atomic effect* rather than each intermediate step,
temporarily broken invariants inside an atomic callee are never exposed to the
client.  (Relies and guarantees are written as two-store predicates and are
assumed reflexive and transitive, as RG logic requires.)

### The initial state

`init P;` gives the predicate satisfied by the program's initial store.
`thread { ... }` declares an initial thread; each thread body begins with a
`yield`, matching the paper's non-preemptive formalization.

---

## What gets verified

For each program the tool discharges (as separate Boogie procedures):

1. **Function definitions** (`M-def-atomic`, `M-def-non-atomic`): the body meets
   its pre/postcondition, is reducible, and has an effect within its declared
   mover; atomic bodies are yield-free (enforced via `G = false`).
2. **Statement obligations**: every access is permitted by its mover
   specification (no data races), every reducible sequence has shape `R*[N]L*`,
   `assert`/`wrong` are safe, loop invariants hold, and — for `M-while` — each
   iteration is a right-mover-or-less and the loop's ascribed effect is never
   below a left-mover (bumped up if needed).  Since any legal loop ascription is
   therefore `⊒ R`, a loop may never be placed after the commit point, where
   termination would be required; this is checked by an unconditional
   `assert eff ⊑ R` at every loop head (so it fires even when the loop's exit
   can never succeed and the loop would spin forever).  Likewise a blocking
   `acquire` is never ascribed an effect below a left-mover (`M-action`'s
   totality side condition), so it cannot follow the commit point either.
3. **Call obligations** (`M-call-*`): callee preconditions hold and callee
   postconditions/effects are composed into the caller.
4. **Mover-spec validity** (paper's Validity, all four conditions): the declared
   movers really do commute — right-movers commute right of following
   non-movers (1), left-movers commute left of preceding non-movers (2), an
   action cannot change the mover another thread computes (3), and a non-mover
   cannot make a left-mover block (4). See *How validity is checked* below.
5. **Run-time state rule** (`M-state`): the guarantee is reflexive (`I ⟹ G`),
   each thread's guarantee is contained in every other thread's rely
   (`G_t ⟹ R_u`), and the initial store establishes each thread's precondition.
6. **Rely well-formedness** (`RelyRefl_*`, `RelyTrans_*`): every non-atomic
   function's rely is reflexive and transitive, i.e. `R = R*`, so the single
   interference step assumed at each `yield` soundly summarises any finite
   number of environment steps (including zero).

A program that discharges all obligations **does not go wrong** (Soundness
theorem): it never fails an assertion or races.

### How validity is checked

Mover-spec validity is a property of the specification `M` alone: it must make
truthful commuting claims about how one thread's actions reorder against
another's.  The paper's Validity definition has four conditions, quantified over
all actions `A₁`, `A₂`, distinct threads `t ≠ u`, and stores.  We check all
four, one Boogie procedure per ordered pair of variables `(X, Y)`.

**Action model.**  Following the paper, an access is modelled abstractly:

* a **write** to variable `X` is `⟨X := v⟩` — it sets `X` to a value `v` and
  leaves every other variable unchanged.  Since the source guarantees the
  right-hand side of a write mentions only thread-local state, `v` is
  *independent of the shared store*; we model it as an arbitrary Boogie value.
  This one form subsumes `acquire` (`⟨m := tid⟩` when `m = 0`), `release`
  (`⟨m := 0⟩`), and a successful `cas` (`⟨X := new⟩` when `X = expected`):
  transitions that fall outside `X`'s declared discipline simply get the mover
  `E` (error) and are excluded by each condition's mover hypotheses.
* a **read** (and a failing `cas`, and an unstable read) is the **identity** on
  the shared store.  Identity actions commute with everything, so they cannot
  break conditions (1), (2), (4) and are not enumerated there.

The mover of an action is the exact clause selection
`M(A, t, σ) = if c₁ then e₁ else … else E`, evaluated with `\old` bound to the
pre-store and bare names to the post-store, and `tid` bound to the acting thread.

**Conditions (1), (2), (4) — commuting, by explicit witness.**  Each condition
asks: given `A₁` by `t` then `A₂` by `u` (with certain mover bounds), does there
*exist* a store `σ‴` witnessing that the two actions can run in the opposite
order to the same effect?  A raw `∀…∃σ‴…` is hard for SMT — but because our
writes are deterministic and their values are store-independent, the witness is
simply "run `A₂` first, then `A₁`", which we **construct explicitly**.  With
`A₁ = ⟨X := v₁⟩` (thread `t`) and `A₂ = ⟨Y := v₂⟩` (thread `u`), and
`σ′ = σ[X := v₁]`, the whole condition collapses to: *assume the mover
hypotheses, then assert the two orders agree.*

| Cond. | Assumed (mover hypotheses)                                   | Asserted (commuting witness)                     |
|-------|--------------------------------------------------------------|--------------------------------------------------|
| (1)   | `M(A₁,t,σ) ⊑ R`  and  `M(A₂,u,σ′) ⊑ N`                        | `σ[X:=v₁][Y:=v₂] == σ[Y:=v₂][X:=v₁]`             |
| (2)   | `M(A₁,t,σ) ⊑ N`  and  `M(A₂,u,σ′) ⊑ L`                        | `σ[X:=v₁][Y:=v₂] == σ[Y:=v₂][X:=v₁]`             |
| (4)   | `M(A₁,t,σ) ⊑ N`  and  `M(A₂,u,σ)  ⊑ L`  (both evaluated at σ) | `σ[X:=v₁][Y:=v₂] == σ[Y:=v₂][X:=v₁]`             |

The asserted equality is a Boogie tautology when `X ≠ Y` (independent updates),
and reduces to `v₁ == v₂` when `X = Y`.  So for the same variable the check says
"two threads may not make *conflicting* (different-valued) writes with these
mover bounds" — which is exactly what forbids, e.g., two concurrent both-mover
writes to one location.  The mover hypotheses do the real filtering: for a
lock-protected `x` (`both-mover if m == tid`) the two would need `m == t` and
`m == u` at once (`t ≠ u`), so the hypotheses are unsatisfiable and the
condition holds vacuously; for a lock-free `buf` (`non-mover`) a right-mover
hypothesis `⊑ R` is already false, so (1) is vacuous and the lone non-mover
commit never has to commute.

**Condition (3) — mover stability.**  This one has no existential: *an action of
`t` must not change the mover `u` computes.*  For each pair `(X, Y)` and
`t ≠ u`, we take a well-defined write of `X` by `t` (assume its own mover is not
`E`) moving `X` to an arbitrary `v`, and assert that the mover `u` would assign
to an access of `Y` is the same before and after — for both a read and a write
of `Y`:

```
assume  M(⟨X:=v⟩, t, σ) != E            // t's action is a real, well-defined step
assert  M(read  Y, u, σ) == M(read  Y, u, σ[X:=v])
assert  M(write Y, u, σ) == M(write Y, u, σ[X:=v])
```

This rejects any specification whose movers depend on data another thread can
legally mutate (e.g. `both-mover if x == 0`, where writing `x` silently changes
`x`'s own mover), which is the property our per-thread, static mover selection
relies on for soundness.  It holds for the lock disciplines because their movers
depend only on lock variables, and the acquire/release protocol keeps those
consistent across the threads that may touch them.

---

## Examples

| File                       | Illustrates                                             |
|----------------------------|---------------------------------------------------------|
| `counter.mml`              | atomic lock-protected `add()`; `even(x)` client         |
| `counter_client2.mml`      | the *same* `add()` reused with an `x >= 0` client (disentanglement) |
| `spinlock.mml`             | user-defined spin lock; `spin_lock` = atomic right-mover |
| `queue.mml`                | lock-free single-element queue (cas + unstable read)    |
| `stack.mml`                | lock-free stack over immutable lists                    |
| `write_guarded.mml`        | write-guarded discipline (locked writes, lock-free reads) |
| `nested_control.mml`       | nested `if` inside a critical section (branch join)     |
| `nonatomic_two_yields.mml` | a non-atomic worker with three reducible sequences      |
| `atomic_calls_atomic.mml`  | an atomic function calling other atomic functions       |
| `assert_pass.mml`          | an assertion that holds                                  |
| `both_mover_loop.mml`      | a both-mover loop ascribed a right-mover effect (`M-while`'s upper bound) |
| **Rejected examples**      | *(verified to fail, with a source-mapped diagnostic)*   |
| `racy_bad.mml`             | writing `x` without holding its lock (data race)        |
| `assert_fail.mml`          | an assertion that need not hold                          |
| `double_release.mml`       | releasing a lock the thread does not hold               |
| `post_commit_loop.mml`     | a loop placed after the commit point (`e ⋢ L` in `M-while`) |
| `post_commit_cas_loop.mml` | a post-commit CAS spin loop whose exit can never succeed (head-phase check) |
| `post_commit_acquire.mml`  | a blocking acquire after the commit point (`M-action` totality) |
| `rely_not_transitive.mml`  | a per-step-bounded rely (`x <= \old(x) + 1`) that is not transitively closed |
| `rely_not_reflexive.mml`   | a strictly-increasing rely (`\old(x) < x`) that excludes the no-interference step |

---

## Source layout

| Module                       | Responsibility                                    |
|------------------------------|---------------------------------------------------|
| `melvin/lexer.py`        | tokenizer                                         |
| `melvin/parser.py`       | recursive-descent parser → AST                    |
| `melvin/ast_nodes.py`    | AST with source spans                             |
| `melvin/types.py`        | type inference + action classification            |
| `melvin/effects.py`      | the six-element effect lattice (`;`, `*`, `⊔`)    |
| `melvin/prelude.py`      | fixed Boogie prelude (effect algebra, lists, ...) |
| `melvin/vcgen.py`        | lowering Mover Logic obligations to Boogie        |
| `melvin/boogie_backend.py` | run Boogie, map failures back to source         |
| `melvin/checker.py`      | top-level driver                                  |
| `melvin/cli.py`          | `melvin` command-line interface (verify)      |
| `melvin/interp.py`       | reference interpreter + `melvin-run` (execute + oracle) |
| `melvin/tools.py`        | find/install Boogie + Z3 (`melvin-install-boogie`, `--doctor`) |

---

## Scope and limitations

* Mover-spec **validity** checks all four conditions (1)–(4) of the paper's
  Validity definition. Actions are modelled as in the paper — a write is
  `<X := v>` for an arbitrary local-determined value, a read is a store
  identity — which subsumes the concrete `acquire`/`release`/`cas` actions
  (transitions outside a variable's declared discipline get the error effect and
  are excluded by the conditions' mover hypotheses). Store-identity actions
  (reads, failing cas, unstable reads) commute trivially and are not enumerated.
* The paper's calculus omits **frame conditions**; consequently a callee's
  `ensures` must state what it leaves unchanged (e.g. `m == \old(m)`).
* The `M-while` **left-mover-termination** side condition is enforced with a
  sound reducibility check per iteration plus an unconditional head-phase check
  (`assert eff ⊑ R` at every loop head: any legal loop ascription is `⊒ R`, so
  a loop may never follow the commit point); a static (state-insensitive)
  approximation is used only to summarize the loop's downstream effect, which
  is sound because it only ever enlarges the composed effect.
* The yield rule assumes the rely **once** to model `R*` (any finite number of
  interference steps), so each rely must be reflexive and transitive.  Melvin
  discharges both properties as Boogie obligations (`RelyRefl_*`,
  `RelyTrans_*`) and rejects the program otherwise — see
  `examples/rely_not_transitive.mml` and `examples/rely_not_reflexive.mml`;
  the closed form of a per-step bound like `x <= \old(x) + 1` is
  `x >= \old(x)`.  Guarantees need no closure check: a guarantee is *asserted*
  one reducible sequence at a time (never composed by the verifier), and
  multi-step interference is absorbed entirely on the rely side via
  `G_t ⟹ R_u` plus the rely's transitivity.  The only residual caveat is
  prover incompleteness: a genuinely transitive rely could in principle fail
  to prove (e.g. nonlinear arithmetic), yielding a false rejection — never a
  false verification.
* Verification is procedure-modular and unbounded-thread; the model is
  sequentially consistent (no weak-memory reasoning).

## Reference

Melvin implements the logic of:

> Cormac Flanagan and Stephen N. Freund.
> *Mover Logic: A Concurrent Program Logic for Reduction and Rely-Guarantee
> Reasoning.* In 38th European Conference on Object-Oriented Programming
> (ECOOP 2024). Leibniz International Proceedings in Informatics (LIPIcs),
> Volume 313, pp. 16:1–16:29, Schloss Dagstuhl – Leibniz-Zentrum für
> Informatik (2024).

It is inspired architecturally by the Anchor and Synchronicity verifiers.
