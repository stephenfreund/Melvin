"""Curated example list for the demo UI.

Each entry names a file in the repository's `examples/` directory, with a
title and one-line blurb for the Examples menu.  `group` controls the menu
sections.  Only files listed here are served — the server rejects any other
name, so this doubles as the path-traversal allowlist.
"""

GROUP_VERIFIES = "Verifies"
GROUP_REJECTED = "Rejected (on purpose)"
GROUP_INTERP = "Interpreter demos"

EXAMPLES = [
    # -- programs the verifier accepts ------------------------------------
    {"name": "counter.mml", "title": "Counter",
     "blurb": "Atomic lock-protected add() with an even(x) client — the paper's running example.",
     "group": GROUP_VERIFIES},
    {"name": "counter_client2.mml", "title": "Counter, second client",
     "blurb": "The same add() reused by an x >= 0 client: specification disentanglement.",
     "group": GROUP_VERIFIES},
    {"name": "spinlock.mml", "title": "Spin lock",
     "blurb": "A user-defined spin lock; spin_lock() is an atomic right-mover.",
     "group": GROUP_VERIFIES},
    {"name": "queue.mml", "title": "Lock-free queue",
     "blurb": "Single-element queue built from cas and an unstable read.",
     "group": GROUP_VERIFIES},
    {"name": "stack.mml", "title": "Lock-free stack",
     "blurb": "Lock-free stack over immutable lists.",
     "group": GROUP_VERIFIES},
    {"name": "write_guarded.mml", "title": "Write-guarded variable",
     "blurb": "Locked writes with lock-free reads.",
     "group": GROUP_VERIFIES},
    {"name": "nested_control.mml", "title": "Nested control",
     "blurb": "Nested if inside a critical section (branch join).",
     "group": GROUP_VERIFIES},
    {"name": "nonatomic_two_yields.mml", "title": "Non-atomic worker",
     "blurb": "A non-atomic function with three reducible sequences.",
     "group": GROUP_VERIFIES},
    {"name": "atomic_calls_atomic.mml", "title": "Atomic calls atomic",
     "blurb": "An atomic function calling other atomic functions.",
     "group": GROUP_VERIFIES},
    {"name": "assert_pass.mml", "title": "Assertion (holds)",
     "blurb": "An assertion the verifier proves.",
     "group": GROUP_VERIFIES},

    # -- programs the verifier rejects, each with a distinct diagnostic ---
    {"name": "racy_bad.mml", "title": "Data race",
     "blurb": "x is read without holding its lock.",
     "group": GROUP_REJECTED},
    {"name": "assert_fail.mml", "title": "Assertion (fails)",
     "blurb": "An assertion that need not hold.",
     "group": GROUP_REJECTED},
    {"name": "double_release.mml", "title": "Double release",
     "blurb": "Releasing a lock the thread does not hold.",
     "group": GROUP_REJECTED},
    {"name": "both_mover_loop.mml", "title": "Left-mover loop",
     "blurb": "A both-mover-only loop (left-mover termination fails).",
     "group": GROUP_REJECTED},
    {"name": "rely_not_transitive.mml", "title": "Non-transitive rely",
     "blurb": "A per-step-bounded rely that is not transitively closed.",
     "group": GROUP_REJECTED},
    {"name": "rely_not_reflexive.mml", "title": "Non-reflexive rely",
     "blurb": "A strictly-increasing rely that excludes the no-interference step.",
     "group": GROUP_REJECTED},

    # -- programs meant for the Run (interpreter) button -------------------
    {"name": "oracle_safe.mml", "title": "Oracle: safe",
     "blurb": "Press Run: no interleaving reaches `wrong` (exhaustive search).",
     "group": GROUP_INTERP},
    {"name": "oracle_unsafe.mml", "title": "Oracle: unsafe",
     "blurb": "Press Run: some interleaving reaches `wrong` — see the trace.",
     "group": GROUP_INTERP},
]

BY_NAME = {e["name"]: e for e in EXAMPLES}
