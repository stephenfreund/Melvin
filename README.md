# Mover Logic

A verifier for **Mover Logic** — the reduction-based rely-guarantee program
logic of Flanagan & Freund — implemented in Python with **Boogie** as the
theorem prover.

Mover Logic extends rely-guarantee (RG) logic with Lipton's theory of
*reduction*.  By proving that a function is **atomic** (its body is a single
*reducible* sequence of movers), the logic gives that function a precise,
*client-independent* postcondition, instead of the weak, stabilized
postconditions that plain RG logic forces on shared-memory code.  This
"disentangles" a library's specification from any particular client's data
invariant and synchronization discipline.

This tool follows the architecture of the **Anchor**/**Synchronicity**
verifiers: it parses a small concurrent language, builds an AST, type-checks it,
lowers the Mover Logic proof obligations to Boogie verification conditions, runs
Boogie, and maps prover failures back to the original source location.

```
  .mll source ──▶ lexer ──▶ parser ──▶ AST ──▶ type checker ──▶ VC generator
                                                                     │
                                                              Boogie (.bpl)
                                                                     │
                          diagnostics  ◀── map errors back ──── prover result
```

---

## Installation

**Requirements:** Python 3.8+ and the **Boogie** verifier (with a Z3 backend).

1. Install Boogie and Z3.  Any of these works:
   * `dotnet tool install --global Boogie` (needs the .NET SDK; then `boogie` is
     on your `PATH`), or
   * download a Boogie release, or use the copy bundled with the Anchor /
     Synchronicity distributions.
2. Install this package (adds a `moverlogic` command):

   ```bash
   cd MoverLogic
   pip install -e .            # or: pip install -e ".[test]" for the test deps
   ```

3. Point the tool at your Boogie executable (only needed if `boogie` is not on
   your `PATH`):

   ```bash
   export MOVERLOGIC_BOOGIE=/path/to/boogie
   ```

   Boogie is located, in order, from `MOVERLOGIC_BOOGIE`, then `boogie`/`Boogie`
   on `PATH`, then a bundled fallback path.

## Running it

```bash
moverlogic examples/counter.mml                 # verify one program
moverlogic examples/*.mml                        # verify several
python -m moverlogic examples/counter.mml        # equivalent, no console script
moverlogic examples/counter.mml --show-bpl       # also print the generated Boogie
moverlogic examples/counter.mml --emit-bpl out.bpl   # save the generated Boogie
```

Exit status is `0` if every file verifies, `1` otherwise.

## Quick start — examples to try and their expected output

Verify the running example (an atomic, lock-protected counter with an `even(x)`
client):

```console
$ moverlogic examples/counter.mml
== examples/counter.mml ==
verified (9 Boogie proof obligation(s) discharged)
```

The whole example suite — every file below should verify except the
intentionally broken one:

```console
$ moverlogic examples/counter.mml examples/counter_client2.mml \
             examples/spinlock.mml examples/queue.mml examples/stack.mml
== examples/counter.mml ==
verified (9 Boogie proof obligation(s) discharged)

== examples/counter_client2.mml ==
verified (9 Boogie proof obligation(s) discharged)

== examples/spinlock.mml ==
verified (7 Boogie proof obligation(s) discharged)

== examples/queue.mml ==
verified (3 Boogie proof obligation(s) discharged)

== examples/stack.mml ==
verified (3 Boogie proof obligation(s) discharged)
```

The broken example is **rejected**, with the error mapped to the exact racy
line (a write/read of `x` performed without holding the lock):

```console
$ moverlogic examples/racy_bad.mml ; echo "exit=$?"
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

## Running the tests

```bash
pip install -e ".[test]"
pytest tests/ -q
```

Boogie-dependent tests self-skip if Boogie cannot be located, so the effect-
algebra and front-end tests still run without a prover installed.

> **On "Boogie Python bindings":** there is no official Python binding for the
> Boogie verifier — the `boogie` package on PyPI is an unrelated Django helper.
> This tool therefore invokes the Boogie executable through a small, isolated
> backend (`moverlogic/boogie_backend.py`); a real binding could replace it
> without touching the rest of the pipeline.

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
   iteration is a right-mover-or-less and the loop does not lie entirely in the
   post-commit (left-mover) region (left-mover termination).
3. **Call obligations** (`M-call-*`): callee preconditions hold and callee
   postconditions/effects are composed into the caller.
4. **Mover-spec validity** (paper's Validity, condition 3): one thread's action
   cannot change the mover another thread computes — the property that makes
   per-thread mover selection sound.
5. **Run-time state rule** (`M-state`): the guarantee is reflexive (`I ⟹ G`),
   each thread's guarantee is contained in every other thread's rely
   (`G_t ⟹ R_u`), and the initial store establishes each thread's precondition.

A program that discharges all obligations **does not go wrong** (Soundness
theorem): it never fails an assertion or races.

---

## Examples

| File                       | Illustrates                                             |
|----------------------------|---------------------------------------------------------|
| `counter.mml`              | atomic lock-protected `add()`; `even(x)` client         |
| `counter_client2.mml`      | the *same* `add()` reused with an `x >= 0` client (disentanglement) |
| `spinlock.mml`             | user-defined spin lock; `spin_lock` = atomic right-mover |
| `queue.mml`                | lock-free single-element queue (cas + unstable read)    |
| `stack.mml`                | lock-free stack over immutable lists                    |
| `racy_bad.mml`             | a racy program that is correctly **rejected**           |

---

## Source layout

| Module                       | Responsibility                                    |
|------------------------------|---------------------------------------------------|
| `moverlogic/lexer.py`        | tokenizer                                         |
| `moverlogic/parser.py`       | recursive-descent parser → AST                    |
| `moverlogic/ast_nodes.py`    | AST with source spans                             |
| `moverlogic/types.py`        | type inference + action classification            |
| `moverlogic/effects.py`      | the six-element effect lattice (`;`, `*`, `⊔`)    |
| `moverlogic/prelude.py`      | fixed Boogie prelude (effect algebra, lists, ...) |
| `moverlogic/vcgen.py`        | lowering Mover Logic obligations to Boogie        |
| `moverlogic/boogie_backend.py` | run Boogie, map failures back to source         |
| `moverlogic/checker.py`      | top-level driver                                  |
| `moverlogic/cli.py`          | command-line interface                            |

---

## Scope and limitations

* Mover-spec **validity** currently checks condition (3) of the paper's Validity
  definition (mover stability), which is the condition per-thread mover
  selection depends on.  The commuting/non-blocking diagrams (1), (2), (4) hold
  for the standard lock, write-guarded, and barrier disciplines expressed here;
  a full existential-witness encoding of them is future work.
* The paper's calculus omits **frame conditions**; consequently a callee's
  `ensures` must state what it leaves unchanged (e.g. `m == \old(m)`).
* The `M-while` **left-mover-termination** side condition is enforced with a
  sound reducibility check per iteration plus a static (state-insensitive)
  approximation for the "not entirely left-moving" requirement.
* Rely/guarantee predicates are assumed reflexive and transitive, so a single
  rely step models `R*`.
* Verification is procedure-modular and unbounded-thread; the model is
  sequentially consistent (no weak-memory reasoning).

## Reference

Based on *Mover Logic: A Concurrent Program Logic based on Reduction* (the
`reduction-rg-logic` manuscript), and inspired architecturally by the Anchor and
Synchronicity verifiers.
