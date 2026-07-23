# A Weakest-Precondition Calculus for Mover Logic

**Status.** Companion technical note to *Mover Logic: A Concurrent Program Logic for
Reduction and Rely-Guarantee Reasoning* (Flanagan & Freund, ECOOP 2024; henceforth
**[ML]**, `../reduction-rg-logic/main.tex`). This document gives a
weakest-precondition (WP) presentation of mover logic: a compositional predicate
transformer `wp` such that checking a fixed set of entailments over `wp` verifies a
program, together with the metatheory relating the transformer to the declarative
proof rules of [ML] and to the operational semantics. The transformer is the
declarative counterpart of the verification-condition generation implemented in
Melvin (`vcgen.py`); see §8.

The key design decision is that `wp` acts on predicates over *phase-extended
configurations* $(t,\sigma_0,\sigma,p)$: thread id, store at the start of the
current reducible sequence, current store, and a *phase* $p\in\{\mathsf{R},\mathsf{N}\}$
recording whether the current reducible sequence has committed. The phase plays the
role of the ghost effect variable in the instrumented semantics of [ML, §A.2], and
reducibility, left-mover totality, and guarantee obligations all become ordinary
conjuncts of `wp`. No stability side conditions are needed except at `yield`, which
is a single clause of the transformer.

---

## 1. Setting

We work with the Mover Logic Language (MML) exactly as in [ML, §5–§7]; this section
fixes notation and records the ingredients the transformer needs. Proofs of facts
stated here without proof are in [ML].

### 1.1 Syntax and operational semantics

$$
\begin{array}{rcl}
s &::=& \mathtt{skip} \mid \mathtt{wrong} \mid A \mid s;s
        \mid \mathtt{if}\;(A_1\diamond A_2)\;s\;s
        \mid \mathtt{while}\;(A_1\diamond A_2)\;s \mid f() \mid \mathtt{yield}\\
A &\subseteq& \mathit{Tid}\times\mathit{Store}\times\mathit{Store}
\qquad \sigma\in\mathit{Store}=\mathit{Var}\to\mathit{Value}
\qquad t,u\in\mathit{Tid}
\end{array}
$$

Actions $A$ are arbitrary tid-indexed store relations (assignments, lock
operations, `cas`, unstable reads, …). Write
$\mathsf{en}(A,t,\sigma) \iff \exists\sigma'.\ (t,\sigma,\sigma')\in A$
(*$A$ is enabled*), and call $A$ *total* if $\mathsf{en}(A,t,\sigma)$ for all
$t,\sigma$. A conditional action $A_1\diamond A_2$ must satisfy the language
well-formedness condition that $A_1\cup A_2$ is total. A state
$\Sigma=\langle s_1\ldots s_n,\sigma\rangle$ steps under the preemptive relation
$\Sigma\to\Sigma'$ of [ML, §5]; $\Sigma$ is *wrong* if some $s_i=E[\mathtt{wrong}]$,
with evaluation contexts $E ::= \bullet \mid E;s$. A statement is *yielding* if it is
$E[\mathtt{yield}]$ or $\mathtt{skip}$. Function bodies are drawn from a declaration
table $D$; calls execute by inlining the body (rule E-call).

### 1.2 Effects and phases

$$
m \in \mathbb{E} ::= \mathsf{Y}\mid\mathsf{B}\mid\mathsf{R}\mid\mathsf{L}\mid\mathsf{N}\mid\mathsf{E}
\qquad\qquad
\mathsf{Y}\sqsubseteq\mathsf{B}\sqsubseteq\mathsf{R},\mathsf{L}\sqsubseteq\mathsf{N}\sqsubseteq\mathsf{E}
$$

with join $\sqcup$, sequential composition $;$ and iterative closure $^*$ from
[ML, §6.1]:

| $m_1;m_2$ | $\mathsf{Y}$ | $\mathsf{B}$ | $\mathsf{R}$ | $\mathsf{L}$ | $\mathsf{N}$ | $\mathsf{E}$ |
|---|---|---|---|---|---|---|
| $\mathsf{Y}$ | $\mathsf{Y}$ | $\mathsf{Y}$ | $\mathsf{Y}$ | $\mathsf{L}$ | $\mathsf{L}$ | $\mathsf{E}$ |
| $\mathsf{B}$ | $\mathsf{Y}$ | $\mathsf{B}$ | $\mathsf{R}$ | $\mathsf{L}$ | $\mathsf{N}$ | $\mathsf{E}$ |
| $\mathsf{R}$ | $\mathsf{R}$ | $\mathsf{R}$ | $\mathsf{R}$ | $\mathsf{N}$ | $\mathsf{N}$ | $\mathsf{E}$ |
| $\mathsf{L}$ | $\mathsf{Y}$ | $\mathsf{L}$ | $\mathsf{E}$ | $\mathsf{L}$ | $\mathsf{E}$ | $\mathsf{E}$ |
| $\mathsf{N}$ | $\mathsf{R}$ | $\mathsf{N}$ | $\mathsf{E}$ | $\mathsf{N}$ | $\mathsf{E}$ | $\mathsf{E}$ |
| $\mathsf{E}$ | $\mathsf{E}$ | $\mathsf{E}$ | $\mathsf{E}$ | $\mathsf{E}$ | $\mathsf{E}$ | $\mathsf{E}$ |

and $\mathsf{Y}^*=\mathsf{Y}$, $\mathsf{B}^*=\mathsf{B}$, $\mathsf{R}^*=\mathsf{R}$,
$\mathsf{L}^*=\mathsf{L}$, $\mathsf{N}^*=\mathsf{E}$, $\mathsf{E}^*=\mathsf{E}$.

A **phase** is $p\in\mathbb{P}=\{\mathsf{R},\mathsf{N}\}$: $\mathsf{R}$ means the
current reducible sequence is in its pre-commit part (only right-movers so far since
the last yield); $\mathsf{N}$ means it has committed. The *phase update* $p;m$ is
composition restricted to $\mathbb{P}\times\mathbb{E}$; explicitly:

$$
\begin{array}{c|cccccc}
p;m & \mathsf{Y} & \mathsf{B} & \mathsf{R} & \mathsf{L} & \mathsf{N} & \mathsf{E}\\\hline
\mathsf{R} & \mathsf{R} & \mathsf{R} & \mathsf{R} & \mathsf{N} & \mathsf{N} & \mathsf{E}\\
\mathsf{N} & \mathsf{R} & \mathsf{N} & \mathsf{E} & \mathsf{N} & \mathsf{E} & \mathsf{E}
\end{array}
$$

Note $p;m\in\mathbb{P}\cup\{\mathsf{E}\}$, and $p;\mathsf{Y}=\mathsf{R}$ (yield opens
a new sequence).

**Lemma 1 (effect algebra).** By inspection of the tables:
(a) $;$ is associative and monotone in both arguments;
(b) $m\sqsubseteq m^{*};m$ for $m^{*}\in\{\mathsf{B},\mathsf{R}\}$;
(c) if $p;m\neq\mathsf{E}$ and $p'\sqsubseteq p$ then $p';m\sqsubseteq p;m$ and
$p';m\neq\mathsf{E}$;
(d) $\mathsf{N};m\neq\mathsf{E} \iff m\sqsubseteq\mathsf{L}$ or $m = \mathsf{Y}$.

### 1.3 Mover specifications

A mover specification assigns each action a state- and thread-dependent effect

$$
M : \mathit{Action}\times\mathit{Tid}\times\mathit{Store} \to \mathbb{E}\setminus\{\mathsf{Y}\}.
$$

$M$ is compiled from source `read`/`write` clauses exactly as in [ML, §6.2]: for a
variable `x` with write clauses $\mathtt{write}\ m_i\ \mathtt{if}\ P_i$
($P_i\subseteq\mathit{Tid}\times\mathit{Store}\times\mathit{Store}$, evaluated in order),

$$
M(\mathtt{x}\!=\!expr,\,t,\sigma) \;=\;
\begin{cases}
m_1 & \text{if } P_1(t,\sigma,\sigma[\mathtt{x}:=\sigma(expr)])\\
\ \vdots\\
m_n & \text{if } P_n(t,\sigma,\sigma[\mathtt{x}:=\sigma(expr)])\\
\mathsf{E} & \text{otherwise}
\end{cases}
$$

and dually for reads with $P_i(t,\sigma,\sigma)$. Local computations have
$M=\mathsf{B}$. Because the clauses are boolean combinations of assertions over
$(\mathit{tid},\sigma,\sigma')$, the function $\lambda\sigma.\,M(A,t,\sigma)$ is
*definable* as a nested conditional in the assertion language — the fact that makes
the transformer below syntactically computable (§3.3).

**Definition 1 (Validity, [ML, Def. 1]).** $M$ is *valid* if for all $t\neq u$,
actions $A_1,A_2$, and stores:

- **(V1)** if $M(A_1,t,\sigma)\sqsubseteq\mathsf{R}$, $(t,\sigma,\sigma')\in A_1$,
  $M(A_2,u,\sigma')\sqsubseteq\mathsf{N}$, $(u,\sigma',\sigma'')\in A_2$, then
  $\exists\sigma'''$ with $(u,\sigma,\sigma''')\in A_2$ and $(t,\sigma''',\sigma'')\in A_1$.
- **(V2)** if $M(A_1,t,\sigma)\sqsubseteq\mathsf{N}$, $(t,\sigma,\sigma')\in A_1$,
  $M(A_2,u,\sigma')\sqsubseteq\mathsf{L}$, $(u,\sigma',\sigma'')\in A_2$, then
  $\exists\sigma'''$ with $(u,\sigma,\sigma''')\in A_2$ and $(t,\sigma''',\sigma'')\in A_1$.
- **(V3)** if $M(A_1,t,\sigma)\sqsubseteq\mathsf{N}$ and $(t,\sigma,\sigma')\in A_1$
  then $M(A_2,u,\sigma) = M(A_2,u,\sigma')$.
- **(V4)** if $M(A_1,t,\sigma)\sqsubseteq\mathsf{N}$, $(t,\sigma,\sigma')\in A_1$,
  $M(A_2,u,\sigma)\sqsubseteq\mathsf{L}$, $(u,\sigma,\sigma'')\in A_2$, then
  $\exists\sigma'''$ with $(u,\sigma',\sigma''')\in A_2$ and $(t,\sigma'',\sigma''')\in A_1$.

### 1.4 Relies, guarantees, specifications, predicate notation

$R,G,P,Q,A \subseteq \mathit{Tid}\times\mathit{Store}\times\mathit{Store}$ (two-store);
$S,T\subseteq\mathit{Tid}\times\mathit{Store}$ (one-store). Standard operators
([ML, §7]):

$$
\begin{array}{rcl@{\qquad}rcl}
\langle S\rangle &=& \{(t,\sigma,\sigma)\mid (t,\sigma)\in S\} &
I &=& \{(t,\sigma,\sigma)\}\\
\mathit{post}(P) &=& \{(t,\sigma)\mid (t,\_,\sigma)\in P\} &
P;A &=& \{(t,\sigma,\sigma'')\mid \exists\sigma'.\,P(t,\sigma,\sigma')\wedge A(t,\sigma',\sigma'')\}
\end{array}
$$

$R^*$ is the reflexive-transitive closure of $R$ at fixed $t$. Function
specifications:

$$
\begin{array}{ll}
\textbf{atomic } e_f\ \textbf{requires } S\ \textbf{ensures } Q_f\quad f()\ \{s\}
& (e_f\in\mathbb{E}\setminus\{\mathsf{Y},\mathsf{E}\},\ \text{$f$ non-recursive})\\[2pt]
\textbf{relies } R_f\ \textbf{guarantees } G_f\ \textbf{requires } S\ \textbf{ensures } T\quad f()\ \{s\}
& (G_f \neq \emptyset)
\end{array}
$$

The mover logic judgment of [ML, §7] is written
$R,G \vdash \{P\}\, s\, \{Q\}\cdot e$.

---

## 2. The WP domain

**Definition 2 (configurations and extended predicates).**

$$
\mathit{Cfg} \;=\; \mathit{Tid}\times\mathit{Store}\times\mathit{Store}\times\mathbb{P},
\qquad
\Phi,\Psi \in \mathit{XPred} \;=\; \mathcal{P}(\mathit{Cfg}).
$$

A configuration $(t,\sigma_0,\sigma,p)$ reads: thread $t$ runs in current store
$\sigma$; the current reducible sequence started at store $\sigma_0$ (all
$\mathtt{\backslash old}(x)$ references in assertions denote $\sigma_0(x)$); the
sequence is in phase $p$.

**Embeddings.** For a two-store $P$ and $q\in\mathbb{E}$:

$$
P@p = \{(t,\sigma_0,\sigma,p) \mid (t,\sigma_0,\sigma)\in P\},
\qquad
\lceil P\rceil_q = \{(t,\sigma_0,\sigma,p') \mid (t,\sigma_0,\sigma)\in P,\ p'\in\mathbb{P},\ p'\sqsubseteq q\},
$$

and $\mathit{pre}_p(\Phi) = \{(t,\sigma_0,\sigma)\mid(t,\sigma_0,\sigma,p)\in\Phi\}$.
$\Phi$ is **$\downarrow$-closed** if $(t,\sigma_0,\sigma,\mathsf{N})\in\Phi$ implies
$(t,\sigma_0,\sigma,\mathsf{R})\in\Phi$ (harder phases imply easier ones; note
$\mathsf{R}\sqsubseteq\mathsf{N}$). Every $\lceil P\rceil_q$ is $\downarrow$-closed.

---

## 3. The transformer

The transformer is parameterized by the declaration table $D$, the mover
specification $M$, and the ambient rely/guarantee $R,G$; we write
$\mathit{wp}_{R,G}(s,\Phi)$, eliding subscripts when clear.

### 3.1 Definition

The auxiliary *guarded step* transformer, for an action $A$:

$$
\mathit{st}(A,\Psi) \;=\;
\Bigl\{(t,\sigma_0,\sigma,p) \;\Bigm|\;
\forall\sigma'.\ (t,\sigma,\sigma')\in A \Rightarrow
p;M(A,t,\sigma)\neq\mathsf{E} \;\wedge\;
(t,\sigma_0,\sigma',\,p;M(A,t,\sigma))\in\Psi \Bigr\}
$$

**Definition 3 (wp).**

$$
\begin{array}{rcl}
\mathit{wp}(\mathtt{skip},\Phi) &=& \Phi\\[3pt]
\mathit{wp}(\mathtt{wrong},\Phi) &=& \emptyset\\[3pt]
\mathit{wp}(A,\Phi) &=&
\{(t,\sigma_0,\sigma,p) \mid p;M(A,t,\sigma)\neq\mathsf{E}\ \wedge\
(p=\mathsf{N}\Rightarrow \mathsf{en}(A,t,\sigma))\}\ \cap\ \mathit{st}(A,\Phi)\\[3pt]
\mathit{wp}(s_1;s_2,\Phi) &=& \mathit{wp}(s_1,\mathit{wp}(s_2,\Phi))\\[3pt]
\mathit{wp}(\mathtt{if}\,(A_1\diamond A_2)\,s_1\,s_2,\Phi) &=&
\mathit{st}(A_1,\mathit{wp}(s_1,\Phi))\ \cap\ \mathit{st}(A_2,\mathit{wp}(s_2,\Phi))\\[3pt]
\mathit{wp}(\mathtt{while}\,(A_1\diamond A_2)\,s,\Phi) &=&
\nu W.\ \bigl[\{(t,\sigma_0,\sigma,p)\mid p=\mathsf{R}\}\ \cap\
\mathit{st}(A_1,\mathit{wp}(s,W))\ \cap\ \mathit{st}(A_2,\Phi)\bigr]\\[3pt]
\mathit{wp}(\mathtt{yield},\Phi) &=&
\{(t,\sigma_0,\sigma,p) \mid (t,\sigma_0,\sigma)\in G\ \wedge\
\forall\sigma'.\ (t,\sigma,\sigma')\in R^* \Rightarrow (t,\sigma',\sigma',\mathsf{R})\in\Phi\}
\end{array}
$$

For a call $f()$ where $D$ declares
$\textbf{atomic } e_f\ \textbf{requires } S\ \textbf{ensures } Q_f$:

$$
\mathit{wp}(f(),\Phi) =
\{(t,\sigma_0,\sigma,p) \mid
p;e_f\neq\mathsf{E}\ \wedge\ (t,\sigma)\in S\ \wedge\
\forall\sigma'.\ (t,\sigma,\sigma')\in Q_f \Rightarrow (t,\sigma_0,\sigma',\,p;e_f)\in\Phi\}
$$

For a call $f()$ where $D$ declares
$\textbf{relies } R_f\ \textbf{guarantees } G_f\ \textbf{requires } S\ \textbf{ensures } T$:

$$
\mathit{wp}(f(),\Phi) =
\begin{cases}
\{(t,\sigma,\sigma,\mathsf{R}) \mid (t,\sigma)\in S\ \wedge\
\forall\sigma'.\ (t,\sigma')\in T \Rightarrow (t,\sigma',\sigma',\mathsf{R})\in\Phi\}
& \text{if } R\subseteq R_f \text{ and } G_f\subseteq G\\
\emptyset & \text{otherwise}
\end{cases}
$$

The while-clause is a greatest fixed point in the complete lattice
$(\mathit{XPred},\subseteq)$; the body functional is monotone (Lemma 2), so
$\nu W$ exists (Knaster–Tarski). Equivalently, membership can be established by
exhibiting any *invariant* $J\subseteq\mathit{Cfg}$ with

$$
J \subseteq \{p=\mathsf{R}\}\ \cap\ \mathit{st}(A_1,\mathit{wp}(s,J))\ \cap\ \mathit{st}(A_2,\Phi),
$$

since every such $J$ is contained in $\nu W$. This is the form a verifier uses
(loop invariant + inductiveness + exit checks).

### 3.2 Reading the clauses

- **Reducibility.** Each action conjoins $p;M(A,t,\sigma)\neq\mathsf{E}$: the DFA
  $\mathsf{R}^*[\mathsf{N}]\mathsf{L}^*$ of [ML, §6.1] must not die. For a *bare*
  action statement this obligation is unconditional (mirroring rule I-action of the
  instrumented semantics, which goes wrong even if $A$ is disabled); for the arms of
  `if`/`while` it is guarded by enabledness of that arm (mirroring I-if). This
  asymmetry is inherited deliberately from the instrumented semantics of [ML, §A.2].
- **Post-commit progress.** The conjunct $p=\mathsf{N}\Rightarrow\mathsf{en}(A,t,\sigma)$
  is the per-configuration form of the "left-movers must be total" premise of
  M-action: once a sequence commits, it must run to its yield without blocking
  (Lemma 8). Conditionals need no such conjunct because $A_1\cup A_2$ is total, and
  loops none because their head is confined to phase $\mathsf{R}$.
- **Loops.** The conjunct $p=\mathsf{R}$ at the loop head (initially *and* at every
  re-test, since the recursive occurrence $W$ carries it) is the transformer image
  of the M-while premises $M(A_1,P);e_1\sqsubseteq\mathsf{R}$ (an iteration may
  not commit and keep looping) and $e\not\sqsubseteq\mathsf{L}$ (every legal
  ascription is $\sqsupseteq\mathsf{R}$, so a loop may not follow the commit
  point): the post-commit part of a reducible sequence may
  not contain loop iterations, since it must terminate. A loop body may re-enter
  phase $\mathsf{R}$ only via `yield` ($\mathsf{N};\mathsf{Y}=\mathsf{R}$), so
  non-atomic loops such as `while (*) { add(); yield }` are accepted.
- **Yield.** Two obligations, replacing all stabilization requirements of RG logic:
  the pending sequence $\sigma_0\to\sigma$ must be published to the guarantee $G$,
  and the continuation must tolerate any finite amount of interference
  $R^*$, restarting with a fresh anchor $\sigma_0'=\sigma'$ and phase $\mathsf{R}$.
- **Atomic calls** use the callee's pre/post as a relational contract composed onto
  the caller's pending sequence ($\sigma_0$ is *not* reset — the callee's behavior
  is absorbed into the caller's reducible sequence) and advance the phase by the
  declared effect $e_f$.
- **Non-atomic calls** require an empty pending sequence ($\sigma_0=\sigma$, phase
  $\mathsf{R}$): the callee will yield internally, so the call must sit at a
  reducible-sequence boundary; on return the anchor is reset. The side condition
  $R\subseteq R_f,\ G_f\subseteq G$ is the contravariant rely / covariant guarantee
  containment of M-call-non-atomic + M-conseq.

### 3.3 Syntactic translation (derived forms)

Fix the assertion language of first-order formulas $\varphi$ over current variables
$\vec{x}$, anchored values $\mathtt{\backslash old}(\vec x)$ (denoting $\sigma_0$),
$\mathit{tid}$, and a phase symbol $\pi$ ranging over
$\{\mathsf{R},\mathsf{N}\}$, with $\llbracket\varphi\rrbracket\in\mathit{XPred}$.
Since $M$ is clause-defined (§1.3), for each global `x` there are effect-valued
*terms* $\widehat{M}^{w}_{x}(e)$ and $\widehat{M}^{r}_{x}$, obtained from the clause
list by substituting, in each $P_i$, current values for the pre-store and (for
writes) $x\mapsto e$ for the post-store. Then `wp` computes by substitution:

| statement | $\mathit{wp}(\cdot,\varphi)$ |
|---|---|
| `x := e` (global, total, deterministic) | $\pi;\widehat{M}^{w}_{x}(e)\neq\mathsf{E}\ \wedge\ \varphi[\pi := \pi;\widehat{M}^{w}_{x}(e)][x := e]$ |
| `r := e` (local; $M=\mathsf{B}$) | $\varphi[r := e]$ |
| `r := x` (read of global into local) | $\pi;\widehat{M}^{r}_{x}\neq\mathsf{E}\ \wedge\ \varphi[\pi := \pi;\widehat{M}^{r}_{x}][r := x]$ |
| unstable read $r \Leftarrow x$ | $\pi;\widehat{M}^{r}_{x}\neq\mathsf{E}\ \wedge\ \forall v.\ \varphi[\pi := \pi;\widehat{M}^{r}_{x}][r := v]$ |
| `acquire(m)` (guard $g \equiv m{=}0$) | $\bigl(g \Rightarrow \pi;\widehat{M}^{w}_{m}(\mathit{tid})\neq\mathsf{E} \wedge \varphi[\pi := \pi;\widehat{M}^{w}_{m}(\mathit{tid})][m := \mathit{tid}]\bigr)\ \wedge\ (\pi{=}\mathsf{N} \Rightarrow g)$ |
| `release(m)` | $\pi;\widehat{M}^{w}_{m}(0)\neq\mathsf{E}\ \wedge\ \varphi[\pi := \pi;\widehat{M}^{w}_{m}(0)][m := 0]$ |
| `assert B` ($B$ a local-state test) | $B\ \wedge\ \varphi$ |
| `yield` | $G(\mathtt{\backslash old}(\vec x),\vec x)\ \wedge\ \forall \vec{x}'.\ R^*(\vec x,\vec x') \Rightarrow \varphi[\mathtt{\backslash old}(\vec x),\vec x,\pi := \vec x',\vec x',\mathsf{R}]$ |

A `cas(x,v,v')` used as a test is the conditional action
$\langle \mathtt{\backslash old}(x)=v \wedge x=v'\rangle_x \diamond I$ and is handled
by the `if`/`while` clauses via $\mathit{st}$ on each arm. Tests that read shared
variables carry the read effect of those variables in their $M$. Expressiveness of
the target logic requires definability of $R^*$; in practice relies are declared
reflexive and transitive ($R = R^*$), as Melvin requires, making this trivial.

---

## 4. Program-level proof obligations

Fix a program: declarations $D$, mover specification $M$, top-level rely/guarantee
$R,G$, and an initial state $\Sigma_{0} = \langle s_1\ldots s_n,\ \sigma_{\mathit{init}}\rangle$
in which every $s_t$ begins with `yield`. Let the *terminal target* be

$$
\Phi_G \;=\; \{(t,\sigma_0,\sigma,p)\mid (t,\sigma_0,\sigma)\in G\}
$$

(a thread that terminates publishes its last pending sequence to $G$; $\Phi_G$ is
$\downarrow$-closed). The **WP obligations** are:

- **(O1)** $M$ is valid (Definition 1).
- **(O2)** $I \subseteq G$ (the guarantee is reflexive).
- **(O3)** for all $t\neq u$: $(t,\sigma,\sigma')\in G \Rightarrow (u,\sigma,\sigma')\in R$
  (each thread's guarantee is contained in every other thread's rely; this is the
  substituted containment $G[\mathit{tid}{:=}t]\Rightarrow R[\mathit{tid}{:=}u]$ of
  M-state).
- **(O4a)** for each atomic declaration
  $\textbf{atomic } e_f\ \textbf{requires } S\ \textbf{ensures } Q_f\ f()\{s\}$:
  $f$ is not (directly or indirectly) recursive, and for **each**
  $p_0\in\{\mathsf{R},\mathsf{N}\}$ with $p_0;e_f\neq\mathsf{E}$:

  $$\langle S\rangle@p_0 \;\subseteq\; \mathit{wp}_{\emptyset,\emptyset}\bigl(s,\ \lceil Q_f\rceil_{p_0;e_f}\bigr).$$

  (Verifying the body at symbolic initial phase, as Melvin's ghost `eff` does,
  discharges both instances at once. The empty rely/guarantee make any reachable
  `yield` in the body unverifiable, enforcing atomicity.)
- **(O4b)** for each non-atomic declaration
  $\textbf{relies } R_f\ \textbf{guarantees } G_f\ \textbf{requires } S\ \textbf{ensures } T\ f()\{s\}$:
  $G_f\neq\emptyset$ and

  $$\langle S\rangle@\mathsf{R} \;\subseteq\; \mathit{wp}_{R_f,G_f}\bigl(s,\ \{(t,\sigma,\sigma,\mathsf{R})\mid (t,\sigma)\in T\}\bigr).$$

  (The identity-shaped target forces the body to end at a reducible-sequence
  boundary — in practice, with a final `yield`.)
- **(O5)** for each thread $t$: $s_t$ is yielding and
  $(t,\sigma_{\mathit{init}},\sigma_{\mathit{init}},\mathsf{R}) \in \mathit{wp}_{R,G}(s_t,\Phi_G)$.
- **(O6)** for every conditional action $A_1\diamond A_2$ in the program,
  $A_1\cup A_2$ is total (language well-formedness, as in [ML, §5]).

We say the program is **wp-verified** when O1–O6 hold. The main results:
wp-verified programs do not go wrong (Theorem 3), and every program verifiable in
mover logic is wp-verified (Theorem 4).

---

## 5. Metatheory I: structural properties

**Lemma 2 (healthiness).** For every $s$: $\mathit{wp}_{R,G}(s,\cdot)$ is monotone
and universally conjunctive
($\mathit{wp}(s,\bigcap_{i}\Phi_i) = \bigcap_i \mathit{wp}(s,\Phi_i)$, $I \ne \emptyset$).

*Proof.* Structural induction. Every clause is built from intersections,
implications with fixed antecedents, and universally quantified consequents in
which $\Phi$ occurs positively and exactly once; $\mathit{st}$ is monotone and
universally conjunctive in $\Psi$. For `while`: the body functional
$F_\Phi(W)$ is monotone in both $W$ and $\Phi$ (by IH), so $\nu W.F_\Phi$ is
monotone in $\Phi$; conjunctivity follows since
$\nu W.F_{\bigcap\Phi_i}(W) = \nu W.\bigcap_i F_{\Phi_i}(W)$ and greatest fixed
points of pointwise intersections of monotone functionals with a common $W$
coincide with the intersection of the fixed points here because $W$ occurs only
through $\mathit{wp}(s,W)$, which is conjunctive by IH. $\square$

**Lemma 3 (phase $\downarrow$-closure).** If $\Phi$ is $\downarrow$-closed then so
is $\mathit{wp}_{R,G}(s,\Phi)$.

*Proof.* Structural induction; let $(t,\sigma_0,\sigma,\mathsf{N})\in\mathit{wp}(s,\Phi)$
and show membership at $\mathsf{R}$. For actions and $\mathit{st}$: by Lemma 1(c),
$\mathsf{R};m\sqsubseteq\mathsf{N};m$ and $\neq\mathsf{E}$ is preserved downward,
and successor configurations move to a phase $\sqsubseteq$ the original one, so IH
plus $\downarrow$-closure of $\Phi$ (respectively of $\mathit{wp}(s_i,\Phi)$, by IH)
applies. The progress conjunct is vacuous at $\mathsf{R}$. For `yield`, the clause
is phase-independent. For `while`, the clause contains no $\mathsf{N}$-tuples, so
closure is vacuous. Calls: the atomic clause is downward-closed by Lemma 1(c) and
$\downarrow$-closure of $\Phi$; the non-atomic clause contains only
$\mathsf{R}$-tuples. $\square$

**Lemma 4 (rely/guarantee weakening).** If $R\subseteq R'$ and $G'\subseteq G$ then
$\mathit{wp}_{R',G'}(s,\Phi) \subseteq \mathit{wp}_{R,G}(s,\Phi)$.

*Proof.* Induction on $s$. Only `yield` and non-atomic calls mention $R,G$. Yield:
$G'(t,\sigma_0,\sigma)\Rightarrow G(t,\sigma_0,\sigma)$, and quantifying over the
smaller set $R^*\subseteq R'^*$ weakens the antecedent. Non-atomic call: the side
condition $R\subseteq R'\subseteq R_f$, $G_f\subseteq G'\subseteq G$ persists by
transitivity. Loops: $\nu$ of a pointwise-larger monotone functional is larger. $\square$

**Lemma 5 (context decomposition).** Define $K_\bullet(\Phi)=\Phi$ and
$K_{E;s}(\Phi) = K_E(\mathit{wp}(s,\Phi))$. Then for all $E,s,\Phi$:
$\mathit{wp}(E[s],\Phi) = \mathit{wp}(s, K_E(\Phi))$, and $K_E$ is monotone and
preserves $\downarrow$-closure.

*Proof.* Induction on $E$, unfolding $\mathit{wp}(s_1;s_2,\Phi)$; the closure
claims follow from Lemmas 2–3. $\square$

**Lemma 6 (anchor shift / prefix).** For a two-store relation $P_0$ define
$P_0\triangleright\Phi = \{(t,\sigma_0,\sigma',p)\mid \exists\hat\sigma.\ (t,\sigma_0,\hat\sigma)\in P_0
\wedge (t,\hat\sigma,\sigma',p)\in\Phi\}$. Then for all $R,G$:

$$
P_0 \triangleright \mathit{wp}_{\emptyset,\emptyset}(s,\Phi)
\;\subseteq\;
\mathit{wp}_{R,G}(s,\ P_0\triangleright\Phi)
$$

where on the left $\Phi$ and $\mathit{wp}_{\emptyset,\emptyset}(s,\Phi)$ are read as
predicates whose anchor is the *callee-side* anchor $\hat\sigma$.

*Proof.* Structural induction. In every clause except `yield` and non-atomic calls,
the anchor component $\sigma_0$ is inert: it is copied unchanged into all
constraints and successor configurations, so pre-composition with $P_0$ commutes
with the clause. $\mathit{wp}_{\emptyset,\emptyset}(\mathtt{yield},\cdot)=\emptyset$
(the conjunct $(t,\sigma_0,\sigma)\in\emptyset$ fails), and
$\mathit{wp}_{\emptyset,\emptyset}(f_{\mathit{non\text{-}atomic}}(),\cdot)=\emptyset$
(the side condition $G_f\subseteq\emptyset$ contradicts $G_f\neq\emptyset$), so
those cases are vacuous. Loops: coinduction, taking
$P_0\triangleright(\nu W)$ as the candidate invariant for the shifted fixed
point. $\square$

Lemma 6 is the WP form of [ML, Lemma "Prefix"]: an atomic callee verified from the
identity anchor $\langle S\rangle$ may be spliced into the middle of a caller's
reducible sequence with pending prefix $P_0$.

---

## 6. Metatheory II: soundness

Soundness follows the architecture of [ML, §A]: (i) an instrumented semantics with
phases; (ii) preservation of a wp-based state judgment under the *non-preemptive*
instrumented semantics; (iii) post-commit termination; (iv) the Simulation and
Reduction theorems of [ML], which transfer safety from the non-preemptive
instrumented semantics back to the standard preemptive semantics. Steps (ii) and
(iii) are where the logic enters, and are re-proved here against `wp`; steps (i)
and (iv) are unchanged from [ML].

### 6.1 Instrumented states and the wp state judgment

Instrumented states $\Pi = \langle p_1\ldots p_n\rangle\cdot\langle s_1\ldots s_n,\sigma\rangle$
and the relations $\Pi\to_t\Pi'$ (preemptive) and $\Pi\mapsto_t\Pi'$
(non-preemptive: all $u\neq t$ yielding) are exactly those of [ML, §A.2]: each
action step composes $M(A,t,\sigma)$ into the phase and goes wrong on
$\mathsf{E}$; `yield` resets the phase to $\mathsf{R}$; calls inline bodies.

**Definition 4 (wp-verified instrumented states).** $\vdash_{\mathit{wp}} \Pi$ iff
O1–O4, O6 hold and there exist an *active thread* $\mathit{tid}$ and an *anchor*
$\sigma_0$ such that:

1. $(\mathit{tid},\sigma_0,\sigma,p_{\mathit{tid}}) \in \mathit{wp}_{R,G}(s_{\mathit{tid}},\Phi_G)$;
2. for every $u\neq\mathit{tid}$: $s_u$ is yielding and
   $(u,\sigma_0,\sigma_0,p_u) \in \mathit{wp}_{R,G}(s_u,\Phi_G)$.

Clause 2 records that a non-active thread last observed the store $\sigma_0$ at
the start of the active thread's current sequence, with an empty pending sequence
of its own — the stabilized form produced by Lemma 7 below.

**Lemma 7 (yield stabilization).** Assume O2. If $s$ is yielding,
$(t,\sigma_0,\sigma,p)\in \mathit{wp}_{R,G}(s,\Phi_G)$, and $(t,\sigma,\sigma')\in R^*$,
then $(t,\sigma',\sigma',p)\in\mathit{wp}_{R,G}(s,\Phi_G)$.

*Proof.* If $s=\mathtt{skip}$: $\mathit{wp}(s,\Phi_G)=\Phi_G$, membership gives
$(t,\sigma_0,\sigma)\in G$; and $(t,\sigma',\sigma')\in I\subseteq G$ gives the
claim. If $s=E[\mathtt{yield}]$: by Lemma 5,
$\mathit{wp}(s,\Phi_G)=\mathit{wp}(\mathtt{yield},K_E(\Phi_G))$, so membership gives
(a) $(t,\sigma_0,\sigma)\in G$ and (b)
$\forall\sigma''.\ R^*(t,\sigma,\sigma'')\Rightarrow(t,\sigma'',\sigma'',\mathsf{R})\in K_E(\Phi_G)$.
For the shifted configuration: $(t,\sigma',\sigma')\in I\subseteq G$ discharges (a),
and (b) restricted to $R^*$-successors of $\sigma'$ follows from (b) at $\sigma$ by
transitivity of $R^*$. The phase is unconstrained by the yield clause. $\square$

**Lemma 8 (context switch).** Assume O2, O3. If $\vdash_{\mathit{wp}}\Pi$ with
active thread $t$ and anchor $\sigma_0$, and all threads of $\Pi$ are yielding,
then for every thread $u$, $\vdash_{\mathit{wp}}\Pi$ holds with active thread $u$
and anchor $\sigma$ (the current store).

*Proof.* Thread $t$ is yielding, so as in the proof of Lemma 7 its membership
yields $(t,\sigma_0,\sigma)\in G$; by O3, $(v,\sigma_0,\sigma)\in R \subseteq R^*$
for every $v\neq t$. Applying Lemma 7 to each $v\neq t$ (which sits at
$(v,\sigma_0,\sigma_0,p_v)$, with $(v,\sigma_0,\sigma)\in R^*$) moves it to
$(v,\sigma,\sigma,p_v)\in\mathit{wp}(s_v,\Phi_G)$, and applying Lemma 7 to $t$
itself with the reflexive step moves it to $(t,\sigma,\sigma,p_t)$. All threads now
sit at anchor $\sigma$ with empty pending sequences, so Definition 4 holds for any
choice of active thread. $\square$

### 6.2 Preservation

**Theorem 1 (Preservation).** If $\vdash_{\mathit{wp}}\Pi$ and $\Pi\mapsto\Pi'$
then $\vdash_{\mathit{wp}}\Pi'$.

*Proof.* Let the step be by thread $w$. If $w$ is not the active thread of
Definition 4, then all threads are yielding (definition of $\mapsto$) and Lemma 8
re-establishes $\vdash_{\mathit{wp}}\Pi$ with active thread $w$; so assume $w =
\mathit{tid} = 1$ w.l.o.g., with anchor $\sigma_0$, store $\sigma$, phase
$p=p_1$, and $s_1 = E[x]$ for redex $x$. By Lemma 5,
$(1,\sigma_0,\sigma,p)\in\mathit{wp}(x,\Psi)$ where $\Psi = K_E(\Phi_G)$, and it
suffices to re-establish clause 1 of Definition 4 for the new configuration
(clause 2 is untouched except in the yield case). Case analysis on $x$:

- $x=\mathtt{wrong}$: impossible, $\mathit{wp}(\mathtt{wrong},\Psi)=\emptyset$.
- $x=\mathtt{skip};s'$: the step is I-seq; $\mathit{wp}(\mathtt{skip};s',\Psi)=\mathit{wp}(s',\Psi)$
  and nothing else changes.
- $x=A$: membership gives $p;M(A,1,\sigma)\neq\mathsf{E}$, so the I-action error
  transition is impossible; for the normal transition
  $(1,\sigma,\sigma')\in A$ with $p' = p;M(A,1,\sigma)$, the $\mathit{st}$ conjunct
  gives $(1,\sigma_0,\sigma',p')\in\Psi = \mathit{wp}(E[\mathtt{skip}],\Phi_G)$
  modulo Lemma 5 (note $\mathit{wp}(\mathtt{skip},\Psi)=\Psi$).
- $x=\mathtt{if}\,(A_1\diamond A_2)\,s_1's_2'$: for the arm $i$ taken,
  $(1,\sigma,\sigma')\in A_i$, so $\mathit{st}(A_i,\mathit{wp}(s_i',\Psi))$ yields
  both $p;M(A_i,1,\sigma)\neq\mathsf{E}$ (no error transition) and membership of the
  successor in $\mathit{wp}(s_i',\Psi) = \mathit{wp}(E[s_i'],\Phi_G)$.
- $x=\mathtt{while}\,(A_1\diamond A_2)\,s'$: the step is the unfolding I-while, so
  it suffices that
  $\mathit{wp}(\mathtt{while}\ldots,\Psi) \subseteq
   \mathit{wp}(\mathtt{if}\,(A_1\diamond A_2)\,(s';\mathtt{while}\ldots)\,\mathtt{skip},\Psi)$.
  Unfold $\nu W = F(\nu W)$: the right-hand side is
  $\mathit{st}(A_1,\mathit{wp}(s',\nu W))\cap\mathit{st}(A_2,\Psi)$, which is $F(\nu W)$
  minus the conjunct $p=\mathsf{R}$ — a superset.
- $x=\mathtt{yield}$: the step (I-yield) leaves $\sigma$ unchanged, sets
  $p_1'=\mathsf{R}$. Membership gives $(1,\sigma_0,\sigma)\in G$ and, taking the
  reflexive interference step,
  $(1,\sigma,\sigma,\mathsf{R})\in K_E(\Phi_G) = \mathit{wp}(E[\mathtt{skip}],\Phi_G)$.
  Re-anchor at $\sigma_0' = \sigma$: clause 1 holds for thread 1. For each
  $u\neq 1$: from $(1,\sigma_0,\sigma)\in G$ and O3, $(u,\sigma_0,\sigma)\in R^*$,
  so Lemma 7 moves $u$ from anchor $\sigma_0$ to anchor $\sigma$. Definition 4
  holds with active thread 1 and anchor $\sigma$.
- $x=f()$, atomic, body $s_f$: the step (I-call) replaces $f()$ by $s_f$, leaving
  $\sigma,p$ unchanged. Membership gives $(1,\sigma)\in S$, $p;e_f\neq\mathsf{E}$,
  and $\forall\sigma'.\ Q_f(1,\sigma,\sigma')\Rightarrow(1,\sigma_0,\sigma',p;e_f)\in\Psi$.
  Instantiate O4a at $p_0 = p$:
  $(1,\sigma,\sigma,p)\in\mathit{wp}_{\emptyset,\emptyset}(s_f,\lceil Q_f\rceil_{p;e_f})$.
  Apply Lemma 6 with $P_0=\{(1,\sigma_0,\sigma)\}$:
  $(1,\sigma_0,\sigma,p)\in\mathit{wp}_{R,G}(s_f,\ P_0\triangleright\lceil Q_f\rceil_{p;e_f})$.
  Every element of $P_0\triangleright\lceil Q_f\rceil_{p;e_f}$ has the form
  $(1,\sigma_0,\sigma',p')$ with $Q_f(1,\sigma,\sigma')$ and $p'\sqsubseteq p;e_f$,
  hence lies in $\Psi$ by the call conjunct and $\downarrow$-closure of $\Psi$
  (Lemmas 3, 5). By monotonicity (Lemma 2),
  $(1,\sigma_0,\sigma,p)\in\mathit{wp}(s_f,\Psi) = \mathit{wp}(E[s_f],\Phi_G)$.
- $x=f()$, non-atomic, body $s_f$: membership gives $p=\mathsf{R}$,
  $\sigma_0=\sigma$, $(1,\sigma)\in S$, the side conditions
  $R\subseteq R_f, G_f\subseteq G$, and
  $\forall\sigma'.\ T(1,\sigma')\Rightarrow(1,\sigma',\sigma',\mathsf{R})\in\Psi$.
  By O4b, $(1,\sigma,\sigma,\mathsf{R})\in\mathit{wp}_{R_f,G_f}(s_f,\Phi_{\mathit{ret}})$
  with $\Phi_{\mathit{ret}}=\{(1,\sigma',\sigma',\mathsf{R})\mid T(1,\sigma')\}$;
  by Lemma 4 the same holds for $\mathit{wp}_{R,G}$; and
  $\Phi_{\mathit{ret}}\subseteq\Psi$ by the call conjunct, so monotonicity gives
  $(1,\sigma,\sigma,\mathsf{R})\in\mathit{wp}(E[s_f],\Phi_G)$. $\square$

**Theorem 2 (verified states are not wrong).** If $\vdash_{\mathit{wp}}\Pi$ then
$\Pi$ is not wrong.

*Proof.* A wrong thread has $s_t = E[\mathtt{wrong}]$, which is not yielding, so
$t$ must be the active thread; but then
$(t,\sigma_0,\sigma,p)\in\mathit{wp}(\mathtt{wrong},K_E(\Phi_G))=\emptyset$,
a contradiction. $\square$

### 6.3 Post-commit termination

Recall the metric $|s|$ of [ML, Lemma "Post-Commit Termination"]:
$|\mathtt{skip}|=|\mathtt{wrong}|=0$; $|A|=|\mathtt{yield}|=|\mathtt{while}\ldots|=1$;
$|f()|=1$ for non-atomic $f$ and $|s_f|+1$ for atomic $f$ with body $s_f$;
$|s_1;s_2|=|\mathtt{if}\,C\,s_1\,s_2|=1+|s_1|+|s_2|$. It is well-defined because
atomic functions are non-recursive (O4a).

**Lemma 9 (post-commit termination).** Suppose $\vdash_{\mathit{wp}}\Pi$, thread
$t$ has $p_t=\mathsf{N}$, and $s_t$ is not yielding. Then $s_t$ can step
($\Pi\to_t$ is enabled), no such step is an error transition, every step strictly
decreases $|s_t|$, and the phase remains $\mathsf{N}$ until $s_t$ becomes yielding.
Consequently $\Pi\to_t^*\Pi'$ with $s'_t$ yielding, in at most $|s_t|$ steps.

*Proof.* Since $s_t$ is not yielding, $t$ is the active thread; let
$(t,\sigma_0,\sigma,\mathsf{N})\in\mathit{wp}(x,\Psi)$ for the redex $x$ (Lemma 5).
Case analysis:

- $x=A$: the progress conjunct at $\mathsf{N}$ gives $\mathsf{en}(A,t,\sigma)$;
  reducibility gives $\mathsf{N};M(A,t,\sigma)\neq\mathsf{E}$, so the step is a
  normal transition; by the phase table the new phase is $\mathsf{N}$
  ($M\neq\mathsf{Y}$); $|\mathtt{skip}|<|A|$.
- $x=\mathtt{if}\,(A_1\diamond A_2)\ldots$: some arm is enabled by O6; for that arm,
  $\mathit{st}$ gives non-error; metric decreases; phase stays $\mathsf{N}$.
- $x=\mathtt{while}\ldots$: impossible — the loop clause requires
  $p=\mathsf{R}$.
- $x=f()$ non-atomic: impossible — the call clause requires $p=\mathsf{R}$.
- $x=f()$ atomic: I-call inlines the body, is always enabled, keeps $\sigma,p$;
  the preservation argument (atomic-call case of Theorem 1, using O4a at
  $p_0=\mathsf{N}$) re-establishes membership; $|s_f|<|f()|$.
- $x=\mathtt{skip};s'$: enabled, metric decreases.
- $x=\mathtt{wrong}$: impossible ($\mathit{wp}=\emptyset$).
- $x=\mathtt{yield}$: excluded ($s_t$ would be yielding).

Each step is a $\mapsto_t$ step (all other threads yielding, by
$\vdash_{\mathit{wp}}\Pi$), so Theorem 1 maintains $\vdash_{\mathit{wp}}$ along the
sequence and the argument iterates; the metric bounds its length. $\square$

### 6.4 Reduction interface and the main theorem

The remaining machinery of [ML, §A] is independent of how states are verified:

**Theorem (Simulation, [ML, Thm 2]).** If $\Sigma\sim\Pi$ and $\Sigma\to\Sigma'$
then there is $\Pi'$ with $\Pi\to\Pi'$ and either $\Sigma'\sim\Pi'$ or $\Pi'$
wrong. (Here $\sim$ pairs $\Sigma$ with any phase-annotated $\Pi$ carrying the same
threads and store.)

**Theorem (Reduction, [ML, Thm 3]).** Suppose $\vdash_{\mathit{wp}}\Pi$, all
threads of $\Pi$ are yielding, and $\Pi$ goes wrong under $\to$. Then $\Pi$ goes
wrong under $\mapsto$.

The proof of Reduction in [ML, §B.1] uses only: the eight commuting/disjointness
properties of the instrumented semantics, which depend on validity of $M$
(O1, via the Right- and Left-Commutativity lemmas and the Diamond and Iterative
Diamond lemmas of [ML, §B.1] — these mention no proof system); Preservation; and
Post-Commit Termination. Substituting Theorem 1 for [ML]'s Preservation theorem
and Lemma 9 for [ML]'s Post-Commit Termination lemma yields the statement
verbatim.

**Theorem 3 (Soundness of the WP translation).** If a program is wp-verified
(O1–O6) then $\Sigma_0$ does not go wrong under the standard preemptive
semantics.

*Proof.* Let $\Pi_0$ annotate $\Sigma_0$ with all phases $\mathsf{R}$. O5 gives
Definition 4 for $\Pi_0$ (any thread active, anchor $\sigma_{\mathit{init}}$;
clause 2 holds because every $s_t$ is yielding and sits at the common anchor), so
$\vdash_{\mathit{wp}}\Pi_0$, and $\Sigma_0\sim\Pi_0$. Suppose
$\Sigma_0\to^*\Sigma'$ wrong. By Simulation (induction along the trace),
$\Pi_0\to^*\Pi'$ with $\Pi'$ wrong. All threads of $\Pi_0$ are yielding, so by
Reduction $\Pi_0\mapsto^*\Pi''$ with $\Pi''$ wrong. By Theorem 1 (induction),
$\vdash_{\mathit{wp}}\Pi''$ — contradicting Theorem 2. $\square$

---

## 7. Metatheory III: agreement with mover logic

### 7.1 The logic embeds into wp

**Theorem 4 (soundness of mover logic relative to wp).** If
$R,G\vdash\{P\}\,s\,\{Q\}\cdot e$ is derivable ([ML, §7]) then for every
$p\in\mathbb{P}$ with $p;e\neq\mathsf{E}$:

$$
P@p \;\subseteq\; \mathit{wp}_{R,G}\bigl(s,\ \lceil Q\rceil_{p;e}\bigr).
$$

Moreover, derivability of $\vdash \mathit{fn}$ for every declaration implies O4,
and $\vdash\Sigma_0$ (rule M-state) implies O1–O3, O5, O6. Hence every program
verifiable in mover logic is wp-verified, and Theorem 3 re-proves [ML, Thm 1].

*Proof.* Induction on the derivation. Throughout, write $m_\sigma =
M(A,t,\sigma)$ and recall $M(A,P) = \bigsqcup_{(t,\_,\sigma)\in P} M(A,t,\sigma)$,
so $m_\sigma \sqsubseteq M(A,P)$ for $(t,\_,\sigma)\in P$, and $;$ is monotone
(Lemma 1a).

- **M-action** ($M(A,P)\sqsubseteq e$; $e\sqsubseteq\mathsf{L}\Rightarrow A$ total). Fix
  $(t,\sigma_0,\sigma)\in P$ and $p$ with $p;e\neq\mathsf{E}$. Reducibility:
  $p;m_\sigma\sqsubseteq p;e\neq\mathsf{E}$. Progress: if $p=\mathsf{N}$ then
  $\mathsf{N};e\neq\mathsf{E}$ forces $e\sqsubseteq\mathsf{L}$ (Lemma 1d and
  $e \ne \mathsf{Y}$), so $A$ is total, hence enabled. Step: any successor
  $(t,\sigma_0,\sigma')$ lies in $P;A = Q$ at phase
  $p;m_\sigma\sqsubseteq p;e$, i.e. in $\lceil Q\rceil_{p;e}$.
- **M-seq** ($e = e_1;e_2$). $p;e_1;e_2\neq\mathsf{E}$ gives
  $p;e_1\neq\mathsf{E}$ ($\mathsf{E}$ is absorbing). IH on $s_1$:
  $P@p\subseteq\mathit{wp}(s_1,\lceil Q_1\rceil_{p;e_1})$. For every phase
  $p'\sqsubseteq p;e_1$ with a $Q_1$-tuple, $p';e_2\sqsubseteq p;e\neq\mathsf{E}$
  (Lemma 1c), so IH on $s_2$ at $p'$ gives
  $Q_1@p'\subseteq\mathit{wp}(s_2,\lceil Q_2\rceil_{p';e_2})
  \subseteq\mathit{wp}(s_2,\lceil Q_2\rceil_{p;e})$; hence
  $\lceil Q_1\rceil_{p;e_1}\subseteq\mathit{wp}(s_2,\lceil Q\rceil_{p;e})$ and
  monotonicity concludes.
- **M-if** ($(M(A_1,P);e_1)\sqcup(M(A_2,P);e_2)\sqsubseteq e$). For each arm $i$ and
  successor via $A_i$: $p;(M(A_i,P);e_i)\sqsubseteq p;e\neq\mathsf{E}$, so
  $p;M(A_i,P)\neq\mathsf{E}$, giving the $\mathit{st}$ reducibility conjunct;
  with $p''=p;m_\sigma\sqsubseteq p;M(A_i,P)$ and $p'';e_i \neq \mathsf{E}$, IH on
  $s_i$ from $P;A_i$ places the successor in
  $\mathit{wp}(s_i,\lceil Q\rceil_{p'';e_i})\subseteq\mathit{wp}(s_i,\lceil Q\rceil_{p;e})$.
- **M-while** ($e_{\mathit{it}} := M(A_1,P);e_1\sqsubseteq\mathsf{R}$,
  $e_{\mathit{it}}^*;M(A_2,P)\sqsubseteq e$, $e\not\sqsubseteq\mathsf{L}$,
  $Q = P;A_2$). From $e\not\sqsubseteq\mathsf{L}$ and $e\neq\mathsf{E}$ (else
  $p;e=\mathsf{E}$): $e\in\{\mathsf{R},\mathsf{N}\}$. Thus $p;e\neq\mathsf{E}$
  forces $p=\mathsf{R}$. From the iteration premise,
  $e_{\mathit{it}}^*\in\{\mathsf{Y},\mathsf{B},\mathsf{R}\}$, so
  $\mathsf{R};e_{\mathit{it}}^*=\mathsf{R}$.
  Take the invariant $W = P@\mathsf{R}$ and show
  $W\subseteq F(W)$: the head conjunct $p=\mathsf{R}$ holds by construction. For
  $\mathit{st}(A_1,\mathit{wp}(s,W))$: a successor of
  $(t,\sigma_0,\sigma,\mathsf{R})$ via $A_1$ sits in $P;A_1$ at
  $p''=\mathsf{R};m_\sigma \sqsubseteq \mathsf{R};M(A_1,P)$ with
  $p'';e_1\sqsubseteq\mathsf{R};e_{\mathit{it}}\sqsubseteq\mathsf{R}$, so IH on the
  body judgment $R,G\vdash\{P;A_1\}\,s\,\{P\}\cdot e_1$ gives membership in
  $\mathit{wp}(s,\lceil P\rceil_{\mathsf{R}}) = \mathit{wp}(s,W)$
  (phases $\sqsubseteq\mathsf{R}$ are exactly $\{\mathsf{R}\}$). For
  $\mathit{st}(A_2,\lceil Q\rceil_{p;e})$: a successor via $A_2$ sits in $P;A_2=Q$
  at $\mathsf{R};m_\sigma\sqsubseteq\mathsf{R};M(A_2,P) =
  \mathsf{R};e_{\mathit{it}}^*;M(A_2,P)\sqsubseteq\mathsf{R};e$. Hence
  $W\subseteq\nu W' F(W')$, i.e. $P@\mathsf{R}\subseteq\mathit{wp}(\mathtt{while}\ldots,\lceil Q\rceil_{\mathsf{R};e})$.
- **M-skip, M-wrong**: immediate ($Q=P$, $e=\mathsf{B}$, $p;\mathsf{B}=p$;
  respectively $P=\emptyset$).
- **M-yield** ($P\Rightarrow G$, $Q = \{(t,\sigma',\sigma')\mid(t,\_,\sigma)\in P,
  (t,\sigma,\sigma')\in R^*\}$, $e=\mathsf{Y}$; $p;\mathsf{Y}=\mathsf{R}$). The
  guarantee conjunct is the premise; each $R^*$-successor $(t,\sigma',\sigma',\mathsf{R})$
  lies in $Q@\mathsf{R}\subseteq\lceil Q\rceil_{\mathsf{R}}$.
- **M-conseq** ($P\Rightarrow P_1$, $Q_1\Rightarrow Q$, $R\Rightarrow R_1$,
  $G_1\Rightarrow G$, $e_1\sqsubseteq e$). $p;e_1\sqsubseteq p;e\neq\mathsf{E}$; IH,
  then Lemma 4 (weakening from $R_1,G_1$ to $R,G$), then monotonicity with
  $\lceil Q_1\rceil_{p;e_1}\subseteq\lceil Q\rceil_{p;e}$.
- **M-call-atomic** ($\mathit{post}(P)\Rightarrow S$, $Q = P;Q_f$, $e = e_f$):
  the three conjuncts of the atomic-call clause are exactly the premises plus
  $p;e_f\neq\mathsf{E}$ (assumed) and the definition of $P;Q_f$.
- **M-call-non-atomic** ($P=\langle S\rangle$, $Q=\langle T\rangle$,
  $e=\mathsf{R}$): $p;\mathsf{R}\neq\mathsf{E}$ forces $p=\mathsf{R}$; tuples of
  $\langle S\rangle@\mathsf{R}$ have $\sigma_0=\sigma$; the rule instantiates the
  judgment at the callee's own $R_f,G_f$ (subsumption to the caller's context goes
  through M-conseq, handled above), so the side condition holds with
  $R = R_f$, $G = G_f$.
- **M-def-atomic**: the premise
  $\emptyset,\emptyset\vdash\{\langle S\rangle\}\,s\,\{Q_f\}\cdot e_f$ under the
  main claim (at each $p_0$ with $p_0;e_f\neq\mathsf{E}$) is literally O4a.
  **M-def-non-atomic**: the premise
  $R_f,G_f\vdash\{\langle S\rangle\}\,s\,\{\langle T\rangle\}\cdot\mathsf{R}$ at
  $p_0=\mathsf{R}$ gives
  $\langle S\rangle@\mathsf{R}\subseteq\mathit{wp}_{R_f,G_f}(s,\lceil\langle T\rangle\rceil_{\mathsf{R}})$,
  and $\lceil\langle T\rangle\rceil_{\mathsf{R}}$ is exactly the target of O4b.
  **M-state**: its premises are O1–O3, O5, O6 (with $Q_t\Rightarrow G$ becoming the
  choice of terminal target $\Phi_G$, justified by
  $\lceil Q_t\rceil\subseteq\Phi_G$ and monotonicity). $\square$

**Remark 1 (the embedding is strict).** `wp` verifies programs mover logic
rejects, in two ways. *(i) Per-state effects*: `wp` composes
$M(A,t,\sigma)$ pointwise, while M-action joins over the whole precondition.
Example: with `x write non-mover if flag / both-mover if !flag` and
`y write both-mover if flag / non-mover if !flag`, the sequence `x := 1; y := 2`
from a precondition allowing both values of `flag` gets
$M(\cdot,P)=\mathsf{N}$ for both writes in the logic
($\mathsf{N};\mathsf{N}=\mathsf{E}$, rejected), yet every single store is fine
($\mathsf{N};\mathsf{B}$ or $\mathsf{B};\mathsf{N}$), and `wp` accepts. Melvin's
VC generator implements the per-state (`wp`) semantics — "the exact,
state-sensitive mover". *(ii) Partial left-movers post-commit*: when the ascribed
effect of an action is $\sqsubseteq\mathsf{L}$, M-action demands *totality* —
enabledness at every store — while `wp` demands enabledness only at the reachable
phase-$\mathsf{N}$ configurations, where it is semantically required. (The
upper-bound form of M-action lets a *pre-commit* partial action escape the
totality premise by ascribing the least effect $\not\sqsubseteq\mathsf{L}$, so
the gap concerns only genuinely post-commit placements.)

The upper-bound premises of M-while also closed a former third gap: a yielding
loop such as `while (*) { yield }` has least effect
$\mathsf{Y}\sqsubseteq\mathsf{L}$, which the earlier equality-form rule could not
ascribe ($e\not\sqsubseteq\mathsf{L}$ fails), but the upper-bound rule accepts
with $e=\mathsf{R}$.

### 7.2 Relative completeness

For the converse we must bridge the gaps of Remark 1. Let **ML⁺** be mover
logic extended with the (sound) indexed disjunction rule

$$
\textsf{M-disj}\quad
\frac{\forall i\in\mathcal{I}.\ \ R,G\vdash\{P_i\}\,s\,\{Q\}\cdot e_i}
     {R,G\vdash\{\textstyle\bigcup_i P_i\}\,s\,\{Q\}\cdot \bigsqcup_i e_i}
$$

whose soundness is immediate from Theorem 4 (each $P_i@p\subseteq
\mathit{wp}(s,\lceil Q\rceil_{p;e_i})\subseteq\mathit{wp}(s,\lceil Q\rceil_{p;\sqcup e_i})$).
Assume:

- **(E)** *Expressiveness*: all `wp`-sets and $R^*$ are definable in the assertion
  language (Cook-style; guaranteed, e.g., when relies are reflexive-transitive and
  the language contains arithmetic).
- **(T)** *Totality discipline*: every action $A$ occurring in the program with
  $M(A,t,\sigma)\sqsubseteq\mathsf{L}$ for some $t,\sigma$ is total. (All standard
  primitives satisfy this: assignments, reads, unstable reads, `release` are total;
  `acquire` is partial but is a right-mover; partial `cas` arms occur inside
  conditional actions, to which M-action's totality premise does not apply.)

**Theorem 5 (relative completeness).** Assume (E) and (T). For every statement
$s$, $\downarrow$-closed definable $\Phi$, and $p\in\mathbb{P}$ with
$W_p := \mathit{pre}_p(\mathit{wp}_{R,G}(s,\Phi)) \neq \emptyset$, there exist $Q$
and $e$ with $p;e\neq\mathsf{E}$ such that

$$
R,G\vdash_{\textsf{ML}^{+}}\{W_p\}\ s\ \{Q\}\cdot e
\qquad\text{and}\qquad
\lceil Q\rceil_{p;e}\subseteq\Phi .
$$

Consequently, a wp-verified program is verifiable in ML⁺: instantiating the claim
at the O4/O5 targets yields the premises of M-def-atomic, M-def-non-atomic, and
M-state (using M-conseq to fix the advertised specifications).

*Proof.* By M-disj over singletons it suffices to prove the claim for
$P = \{(t,\sigma_0,\sigma)\}$, a single configuration in $W_p$; the general $W_p$
is the union of its singletons, $Q$ the union of the constructed posts (contained
in $\mathit{pre}(\Phi)$-projections, so the final $\lceil\cdot\rceil$ containment
persists), and $e$ the join of the constructed effects, which satisfies
$p;e\neq\mathsf{E}$ because each disjunct does and $p;\cdot$ preserves joins on
this finite lattice. Structural induction on $s$ (for `while`, on the fixed point):

- $s=A$: membership in $\mathit{wp}(A,\Phi)$ gives $p;m_\sigma\neq\mathsf{E}$.
  For the singleton, $M(A,P) = m_\sigma$ exactly. If $m_\sigma\sqsubseteq\mathsf{L}$,
  (T) gives totality, discharging the M-action premise. Take
  $Q = P;A$, $e = m_\sigma$; the $\mathit{st}$ conjunct places
  $Q@(p;m_\sigma)\subseteq\Phi$, and $\downarrow$-closure lifts this to
  $\lceil Q\rceil_{p;e}\subseteq\Phi$. Apply M-action.
- $s=s_1;s_2$: by IH on $s_1$ with target $\mathit{wp}(s_2,\Phi)$
  ($\downarrow$-closed and definable by Lemma 3 and (E)), obtain
  $\{P\}s_1\{Q_1\}\cdot e_1$ with $\lceil Q_1\rceil_{p;e_1}\subseteq\mathit{wp}(s_2,\Phi)$.
  For each $p'\sqsubseteq p;e_1$, IH on $s_2$ from
  $\mathit{pre}_{p'}(\mathit{wp}(s_2,\Phi))\supseteq Q_1$ yields
  $\{Q_1\}s_2\{Q^{p'}_2\}\cdot e^{p'}_2$; combine the (at most two) instances with
  M-disj-style bookkeeping — formally, apply the singleton decomposition to $Q_1$
  so that each disjunct carries the phase $p'$ it actually reaches — and M-seq,
  taking $e = e_1;\bigsqcup e^{p'}_2$; associativity and Lemma 1c give
  $p;e\neq\mathsf{E}$ and the target containment.
- $s=\mathtt{if}\,(A_1\diamond A_2)\,s_1\,s_2$: from $\mathit{st}(A_i,\mathit{wp}(s_i,\Phi))$,
  IH on each arm from the (singleton-decomposed) $P;A_i$, then M-if with
  M-conseq to equalize the two posts to their union.
- $s=\mathtt{while}\,(A_1\diamond A_2)\,s'$: membership forces $p=\mathsf{R}$. Take
  the loop invariant $J = \mathit{pre}_{\mathsf{R}}(\nu W)$ (definable by (E)).
  The fixed-point equation gives, for each singleton of $J$:
  $\mathit{st}(A_1,\mathit{wp}(s',\nu W))$, so IH on $s'$ yields
  $\{J;A_1\}\,s'\,\{J\}\cdot e_1$ with $\mathsf{R};M(A_1,J);e_1\sqsubseteq\mathsf{R}$,
  i.e. $e_{\mathit{it}} := M(A_1,J);e_1\sqsubseteq\mathsf{R}$ — the iteration
  premise of M-while. Take $e$ to be the least effect with
  $e_{\mathit{it}}^*;M(A_2,J)\sqsubseteq e$ and $e\not\sqsubseteq\mathsf{L}$
  (bumping $\mathsf{Y},\mathsf{B}\mapsto\mathsf{R}$ and
  $\mathsf{L}\mapsto\mathsf{N}$ if needed); then
  $e\in\{\mathsf{R},\mathsf{N}\}$, so $p;e\neq\mathsf{E}$, and M-while applies
  with $Q = J;A_2$, whose $\lceil\cdot\rceil_{\mathsf{R};e}$-embedding lies in
  $\Phi$ by $\mathit{st}(A_2,\Phi)$.
- $s=\mathtt{yield}$: take $Q = \{(t,\sigma',\sigma')\mid R^*(t,\sigma,\sigma')\}$
  (definable by (E)), $e=\mathsf{Y}$; the `wp` conjuncts are the M-yield premises,
  and $Q@\mathsf{R}\subseteq\Phi$ is the interference conjunct.
- $s=f()$: read the corresponding call clause of Definition 3 as the premises of
  M-call-atomic (with $Q=P;Q_f$, $e=e_f$) or M-call-non-atomic (with M-conseq for
  the rely/guarantee side conditions), exactly inverting the M-call cases of
  Theorem 4.
- $s=\mathtt{skip},\mathtt{wrong}$: M-skip; for `wrong`, $W_p=\emptyset$ and there
  is nothing to prove (or apply M-wrong). $\square$

The proof isolates precisely where completeness genuinely needs more than [ML]'s
rules: arbitrary disjunction (gap (i)) and the totality discipline (gap (ii)).
Under (T), plain mover logic suffices.

---

## 8. Correspondence with the Melvin encoding

Melvin's `vcgen.py` is a forward (strongest-postcondition-style) Boogie encoding of
the same obligations; the dictionary between the two presentations:

| WP calculus | Melvin / Boogie |
|---|---|
| phase $\pi$, update $p;M(A,t,\sigma)$ | ghost `eff` variable, composed via the prelude's effect-algebra functions |
| reducibility conjunct $p;M\neq\mathsf{E}$ | `assert eff != E` after each action |
| per-state $M(A,t,\sigma)$ (Remark 1(i)) | the exact, state-sensitive mover: an `if/else` over spec clauses |
| anchor $\sigma_0$ / $\mathtt{\backslash old}$ | `o_` snapshots (reducible-sequence start) |
| yield clause: publish $G$, havoc under $R^*$, reset anchor and phase | guarantee assert, store havoc + `assume R`, `py_` snapshots, `eff := Y`-reset |
| loop clause $\nu W$ with $p=\mathsf{R}$ at head | unconditional `assert leqEff(eff, R)` at the loop head; havoc-cut loop with exact per-iteration `eff ⊑ R` check |
| O4a at symbolic $p_0$ | per-function Boogie procedure with symbolic initial `eff` |
| atomic-call clause; Lemma 6 | call-entry temps (`cs<k>_…`) substituted into callee spec; caller-side effect composition with $e_f$ |
| O1 (V1–V4) | `gen_validity` (`_validity3`, `_validity_commute`) |
| O3 + rely closure for (E) | `gen_rely_checks` ($R = R^*$ for non-atomic relies) |

Two caveats when reading Melvin against this document: Melvin's surface language
adds features (objects, arrays, parameters) formalized here only through the
action abstraction; and Melvin summarizes a loop's *downstream* effect with a
static approximation bumped out of the $\sqsubseteq\mathsf{L}$ region, which is
sound by M-conseq/Theorem 4 because it only ever enlarges the composed effect —
the placement check itself is the unconditional head assert, which must not be
weakened to an exit-path or static check (a loop whose exit is infeasible spins
forever and must still be rejected at a post-commit head).

## 9. Summary

The calculus consists of one domain decision — predicates over
$(t,\sigma_0,\sigma,p)$ — and Definition 3. All of mover logic's distinctive
machinery lands in three places: reducibility is a conjunct per action
($p;M\neq\mathsf{E}$), reduction's termination requirement is a conjunct per
action and per loop head ($p=\mathsf{N}\Rightarrow$ enabled; $p=\mathsf{R}$ at
tests), and interference is a single clause at `yield` (publish $G$; havoc under
$R^*$; reset the anchor). Soundness (Theorem 3) reuses [ML]'s reduction argument
unchanged, replacing its preservation and post-commit-termination lemmas with
sharper wp counterparts whose proofs need no evaluation-context or consequence
lemmas. The transformer is complete for the logic (Theorem 4) and strictly more
precise than it (Remark 1), coinciding with the logic exactly up to arbitrary
disjunction and the left-mover totality discipline (Theorem 5).

## References

- C. Flanagan and S. N. Freund. *Mover Logic: A Concurrent Program Logic for
  Reduction and Rely-Guarantee Reasoning.* ECOOP 2024. (Manuscript:
  `../reduction-rg-logic/main.tex`; appendix theorem/lemma numbers cited as [ML].)
- R. J. Lipton. *Reduction: A method of proving properties of parallel programs.*
  CACM 18(12), 1975.
- C. B. Jones. *Tentative steps toward a development method for interfering
  programs.* TOPLAS 5(4), 1983.
- E. W. Dijkstra. *Guarded commands, nondeterminacy and formal derivation of
  programs.* CACM 18(8), 1975.
- S. A. Cook. *Soundness and completeness of an axiom system for program
  verification.* SIAM J. Comput. 7(1), 1978.
- C. Flanagan and S. N. Freund. *The Anchor verifier for blocking and non-blocking
  concurrent software.* OOPSLA 2020.
- J. Yi and C. Flanagan. *Effects for cooperable and serializable threads.*
  TLDI 2010. (Source of the effect DFA and composition tables.)




