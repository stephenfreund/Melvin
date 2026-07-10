"""Curated example list for the demo UI.

Each entry names a file in the repository's `examples/` directory, with a
title and one-line blurb for the Examples menu.  `group` is the key of a
GROUPS category; the menu renders one flyout submenu per category, in GROUPS
order, so the top level stays short and each flyout shows what its examples
do.  Only files listed here are served — the server rejects any other name,
so this doubles as the path-traversal allowlist.
"""

GROUPS = [
    {"key": "start", "title": "Start here",
     "blurb": "The paper's running example: an atomic counter and the "
              "clients that reuse its specification."},
    {"key": "sync", "title": "Synchronization idioms",
     "blurb": "Locks built from scratch and lock-free structures."},
    {"key": "features", "title": "Language features",
     "blurb": "Small programs showing one construct each."},
    {"key": "bad-sync", "title": "Bugs caught: races & locking",
     "blurb": "Rejected on purpose: synchronization errors and the "
              "diagnostics they produce."},
    {"key": "bad-spec", "title": "Bugs caught: specs & logic",
     "blurb": "Rejected on purpose: assertion and specification problems."},
    {"key": "run", "title": "Run the interpreter",
     "blurb": "Programs meant for the Run button: exhaustive interleaving "
              "search, traces, and final states."},
]

EXAMPLES = [
    # -- start here ---------------------------------------------------------
    {"name": "counter.mml", "title": "Counter",
     "blurb": "Atomic lock-protected add() with an even(x) client — the paper's running example.",
     "group": "start"},
    {"name": "counter_client2.mml", "title": "Counter, second client",
     "blurb": "The same add() reused by an x >= 0 client: specification disentanglement.",
     "group": "start"},

    # -- synchronization idioms ----------------------------------------------
    {"name": "spinlock.mml", "title": "Spin lock",
     "blurb": "A user-defined spin lock; spin_lock() is an atomic right-mover.",
     "group": "sync"},
    {"name": "write_guarded.mml", "title": "Write-guarded variable",
     "blurb": "Locked writes with lock-free reads.",
     "group": "sync"},
    {"name": "queue.mml", "title": "Lock-free queue",
     "blurb": "Single-element queue built from cas and an unstable read.",
     "group": "sync"},
    {"name": "stack.mml", "title": "Lock-free stack",
     "blurb": "Lock-free stack over immutable lists.",
     "group": "sync"},

    # -- language features ----------------------------------------------------
    {"name": "nested_control.mml", "title": "Nested control",
     "blurb": "Nested if inside a critical section (branch join).",
     "group": "features"},
    {"name": "nonatomic_two_yields.mml", "title": "Non-atomic worker",
     "blurb": "A non-atomic function with three reducible sequences.",
     "group": "features"},
    {"name": "atomic_calls_atomic.mml", "title": "Atomic calls atomic",
     "blurb": "An atomic function calling other atomic functions.",
     "group": "features"},
    {"name": "assert_pass.mml", "title": "Assertion (holds)",
     "blurb": "An assertion the verifier proves.",
     "group": "features"},

    # -- rejected: races & locking ---------------------------------------------
    {"name": "racy_bad.mml", "title": "Data race",
     "blurb": "x is read without holding its lock.",
     "group": "bad-sync"},
    {"name": "double_release.mml", "title": "Double release",
     "blurb": "Releasing a lock the thread does not hold.",
     "group": "bad-sync"},

    # -- rejected: specs & logic -------------------------------------------------
    {"name": "assert_fail.mml", "title": "Assertion (fails)",
     "blurb": "An assertion that need not hold.",
     "group": "bad-spec"},
    {"name": "both_mover_loop.mml", "title": "Left-mover loop",
     "blurb": "A both-mover-only loop (left-mover termination fails).",
     "group": "bad-spec"},
    {"name": "rely_not_transitive.mml", "title": "Non-transitive rely",
     "blurb": "A per-step-bounded rely that is not transitively closed.",
     "group": "bad-spec"},
    {"name": "rely_not_reflexive.mml", "title": "Non-reflexive rely",
     "blurb": "A strictly-increasing rely that excludes the no-interference step.",
     "group": "bad-spec"},

    # -- programs meant for the Run (interpreter) button ---------------------
    {"name": "oracle_safe.mml", "title": "Oracle: safe",
     "blurb": "Press Run: no interleaving reaches `wrong` (exhaustive search).",
     "group": "run"},
    {"name": "oracle_unsafe.mml", "title": "Oracle: unsafe",
     "blurb": "Press Run: some interleaving reaches `wrong` — see the trace.",
     "group": "run"},
]

BY_NAME = {e["name"]: e for e in EXAMPLES}
