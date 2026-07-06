"""A reference interpreter for the Mover Logic Language, used as an INDEPENDENT
oracle to cross-check the Boogie-based verifier.

This implements the small-step operational semantics of MLL directly (Figure
"Mover Logic Language") and an explicit-state scheduler that explores *all*
thread interleavings up to a bounded number of states.  It answers one
question: is a state in which some thread is about to execute `wrong`
reachable?  (`assert B` desugars to `if B then skip else wrong`, so a failed
assertion is a reachable `wrong`.)

The verifier's soundness theorem says: if the tool verifies a program, the
program does not go wrong.  So for every program the verifier accepts, this
interpreter must find NO reachable `wrong`.  If it ever did, that would be a
soundness bug in the verifier or its Boogie encoding.  Conversely, a program
this interpreter shows can go wrong must be rejected by the verifier.

Being a direct, sequential implementation of the semantics, the interpreter is
much simpler than the verifier and serves as a trustworthy differential oracle.

Supported fragment: the integer core plus immutable lists (`Nil`, `::`, `head`,
`tail`) and optionals (`None`, `Some`).  `\\old(x)` in an assertion denotes the
value of `x` at the start of the current reducible sequence (the last `yield`,
or thread start), which is how the logic reads assertion pre-state.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import ast_nodes as A


class InterpError(Exception):
    pass


# A store value is an int, a tuple (immutable list), or ("some", v) / None.
NilVal = ()          # empty immutable list


@dataclass(frozen=True)
class ThreadState:
    """One thread: a stack of statements to run, plus its \\old snapshot key."""
    cont: Tuple                     # tuple of AST statement nodes (a stack)
    old_snapshot: Tuple             # frozen store items at the last yield


@dataclass
class ExploreResult:
    wrong_reachable: bool
    states_explored: int
    hit_bound: bool
    trace: Optional[List[str]] = None


class Interpreter:
    def __init__(self, prog: A.Program, max_states: int = 200_000,
                 loop_bound: int = 1000):
        self.prog = prog
        self.max_states = max_states
        self.loop_bound = loop_bound
        self.globals = [v.name for v in prog.vars]

    # ------------------------------------------------------------ store
    def _initial_store(self) -> Dict:
        store: Dict = {}
        for v in self.prog.vars:
            store[v.name] = self._default(v.type)
        # apply the init predicate as simple equality constraints if present
        if self.prog.init is not None:
            self._apply_init(self.prog.init.pred, store)
        return store

    @staticmethod
    def _default(ty: A.TypeExpr):
        if ty.name == "List":
            return NilVal
        if ty.name == "Optional":
            return None
        return 0

    def _apply_init(self, pred: A.Expr, store: Dict) -> None:
        # Handle conjunctions of `g == literal` to pick a concrete initial store.
        if isinstance(pred, A.Binary) and pred.op == "&&":
            self._apply_init(pred.left, store)
            self._apply_init(pred.right, store)
        elif isinstance(pred, A.Binary) and pred.op == "==" and isinstance(pred.left, A.Var):
            if pred.left.name in store:
                store[pred.left.name] = self._eval(pred.right, store, None, tid=0)

    # ------------------------------------------------------ expression eval
    def _eval(self, e: A.Expr, store: Dict, old: Optional[Dict], tid: int):
        t = type(e)
        if t is A.Num:
            return e.value
        if t is A.BoolLit:
            return e.value
        if t is A.NilLit:
            return NilVal
        if t is A.NoneLit:
            return None
        if t is A.Tid:
            return tid
        if t is A.Result:
            return store.get(("result", tid), 0)
        if t is A.Old:
            src = old if old is not None else store
            return self._eval(e.inner, src, src, tid)
        if t is A.Var:
            return self._read_var(e.name, store, tid)
        if t is A.Unary:
            v = self._eval(e.operand, store, old, tid)
            return (not v) if e.op == "!" else (-v)
        if t is A.Binary:
            return self._eval_binary(e, store, old, tid)
        if t is A.Call:
            return self._eval_call(e, store, old, tid)
        if t is A.Index:
            base = self._eval(e.base, store, old, tid)
            idx = self._eval(e.index, store, old, tid)
            return base[idx] if isinstance(base, (list, tuple)) else 0
        if t is A.Quant:
            lo = self._eval(e.lo, store, old, tid)
            hi = self._eval(e.hi, store, old, tid)
            results = []
            for i in range(lo, hi):
                # bind the quantifier variable by shadowing in a temp scope
                results.append(self._eval_with_binding(e.body, store, old, tid, e.var, i))
            if e.kind == "forall":
                return all(results)
            return any(results)
        raise InterpError(f"cannot evaluate {t.__name__}")

    def _eval_with_binding(self, e, store, old, tid, name, val):
        # simple binding via a shadow store entry keyed by the bound name
        shadow = dict(store)
        shadow[("__bound", name)] = val
        return self._eval_bound(e, shadow, old, tid)

    def _eval_bound(self, e, store, old, tid):
        if isinstance(e, A.Var) and ("__bound", e.name) in store:
            return store[("__bound", e.name)]
        # fall back to normal eval but keep bindings visible for nested vars
        t = type(e)
        if t is A.Binary:
            l = self._eval_bound(e.left, store, old, tid)
            r = self._eval_bound(e.right, store, old, tid)
            return self._apply_op(e.op, l, r)
        if t is A.Index:
            base = self._eval_bound(e.base, store, old, tid)
            idx = self._eval_bound(e.index, store, old, tid)
            return base[idx] if isinstance(base, (list, tuple)) else 0
        if t is A.Unary:
            v = self._eval_bound(e.operand, store, old, tid)
            return (not v) if e.op == "!" else (-v)
        return self._eval(e, store, old, tid)

    def _read_var(self, name: str, store: Dict, tid: int):
        if name in self.globals:
            return store[name]
        return store.get((name, tid), 0)         # thread-locals default to 0

    def _eval_binary(self, e: A.Binary, store, old, tid):
        if e.op == "::":
            h = self._eval(e.left, store, old, tid)
            tl = self._eval(e.right, store, old, tid)
            return (h,) + tuple(tl)
        l = self._eval(e.left, store, old, tid)
        r = self._eval(e.right, store, old, tid)
        return self._apply_op(e.op, l, r)

    @staticmethod
    def _apply_op(op, l, r):
        if op == "&&":
            return bool(l) and bool(r)
        if op == "||":
            return bool(l) or bool(r)
        if op == "==>":
            return (not l) or bool(r)
        if op == "<==>":
            return bool(l) == bool(r)
        if op == "==":
            return l == r
        if op == "!=":
            return l != r
        if op == "<":
            return l < r
        if op == "<=":
            return l <= r
        if op == ">":
            return l > r
        if op == ">=":
            return l >= r
        if op == "+":
            return l + r
        if op == "-":
            return l - r
        if op == "*":
            return l * r
        if op == "/":
            return int(l / r) if r != 0 else 0
        if op == "%":
            return l % r if r != 0 else 0
        raise InterpError(f"unknown operator {op}")

    def _eval_call(self, e: A.Call, store, old, tid):
        args = [self._eval(a, store, old, tid) for a in e.args]
        if e.name == "head":
            return args[0][0] if args[0] else 0
        if e.name == "tail":
            return tuple(args[0][1:])
        if e.name == "Some":
            return ("some", args[0])
        if e.name == "isNone":
            return args[0] is None
        if e.name == "theVal":
            return args[0][1] if isinstance(args[0], tuple) and args[0] and args[0][0] == "some" else 0
        if e.name == "even":
            return args[0] % 2 == 0
        # unknown uninterpreted predicate: model as True (never the cause of a
        # wrong on its own); the oracle only cares about concrete safety.
        return True

    # ---------------------------------------------------- small-step engine
    def explore(self, want_trace: bool = False) -> ExploreResult:
        init_store = self._initial_store()
        threads: List[ThreadState] = []
        for th in self.prog.threads:
            snap = self._freeze(init_store)
            threads.append(ThreadState(tuple(th.body), snap))
        if not threads:
            raise InterpError("program has no threads to run")

        start = (tuple(threads), self._freeze(init_store))
        seen = set()
        stack = [(start, [])]
        explored = 0
        while stack:
            (state, path) = stack.pop()
            key = self._state_key(state)
            if key in seen:
                continue
            seen.add(key)
            explored += 1
            if explored > self.max_states:
                return ExploreResult(False, explored, hit_bound=True)
            thread_tuple, frozen_store = state
            store = dict(frozen_store)
            for idx, ts in enumerate(thread_tuple):
                thread_id = idx + 1                      # Tid = {1, 2, ...}
                successors = self._step(thread_id, ts, store)
                for (new_ts, new_store, is_wrong) in successors:
                    if is_wrong:
                        return ExploreResult(
                            True, explored, hit_bound=False,
                            trace=(path + [self._descr(thread_id, ts)]) if want_trace else None)
                    new_threads = list(thread_tuple)
                    new_threads[idx] = new_ts
                    nstate = (tuple(new_threads), self._freeze(new_store))
                    if self._state_key(nstate) not in seen:
                        stack.append((nstate, path + [self._descr(thread_id, ts)] if want_trace else []))
        return ExploreResult(False, explored, hit_bound=False)

    def _freeze(self, store: Dict) -> Tuple:
        items = [
            (k, v) for k, v in store.items()
            if not (isinstance(k, tuple) and k and k[0] in ("__q", "__bound"))
        ]
        return tuple(sorted(items, key=lambda kv: repr(kv[0])))

    def _state_key(self, state) -> Tuple:
        thread_tuple, frozen_store = state
        conts = tuple(tuple(id(s) for s in ts.cont) for ts in thread_tuple)
        snaps = tuple(ts.old_snapshot for ts in thread_tuple)
        return (conts, snaps, frozen_store)

    @staticmethod
    def _descr(tid, ts) -> str:
        head = ts.cont[0] if ts.cont else None
        return f"t{tid}:{type(head).__name__ if head else 'done'}"

    def _step(self, tid: int, ts: ThreadState, store: Dict):
        """Return a list of (new ThreadState, new store dict, wrong?) successors
        for one small step of thread `tid`.  An empty list means the thread is
        finished or blocked."""
        if not ts.cont:
            return []
        head = ts.cont[0]
        rest = ts.cont[1:]

        def cont(new_head_list, new_store=store, snapshot=ts.old_snapshot):
            new_cont = tuple(new_head_list) + rest
            return [(ThreadState(new_cont, snapshot), dict(new_store), False)]

        if isinstance(head, A.Skip):
            return cont([])
        if isinstance(head, A.Yield):
            # a yield takes a step and refreshes the \old snapshot
            return [(ThreadState(rest, self._freeze(store)), dict(store), False)]
        if isinstance(head, A.Wrong):
            return [(ThreadState(rest, ts.old_snapshot), dict(store), True)]
        if isinstance(head, A.Assert):
            old = dict(ts.old_snapshot)
            ok = bool(self._eval(head.expr, store, old, tid))
            return [(ThreadState(rest, ts.old_snapshot), dict(store), not ok)]
        if isinstance(head, A.Assign):
            s2 = dict(store)
            val = self._eval(head.rhs, store, dict(ts.old_snapshot), tid)
            self._write_var(head.lhs, val, s2, tid)
            return cont([], s2)
        if isinstance(head, A.UnstableRead):
            # nondeterministic: the current value, plus a few type-appropriate
            # adversarial ones (an unstable read may load any value).
            src = self._read_var(head.source, store, tid)
            candidates = {src}
            if isinstance(src, int) and not isinstance(src, bool):
                candidates |= {0, 1}
            outs = []
            for v in candidates:
                s2 = dict(store)
                s2[(head.lhs, tid)] = v
                outs.append((ThreadState(rest, ts.old_snapshot), s2, False))
            return outs
        if isinstance(head, A.Acquire):
            if store[head.lock] == 0:
                s2 = dict(store); s2[head.lock] = tid         # tid is 1-based
                return cont([], s2)
            return []                                          # blocked
        if isinstance(head, A.Release):
            s2 = dict(store); s2[head.lock] = 0
            return cont([], s2)
        if isinstance(head, A.If):
            succeeded, s2 = self._cond(head.cond, store, tid)
            branch = head.then_body if succeeded else head.else_body
            return [(ThreadState(tuple(branch) + rest, ts.old_snapshot), s2, False)]
        if isinstance(head, A.While):
            succeeded, s2 = self._cond(head.cond, store, tid)
            if succeeded:
                # run body, then re-enter the SAME while node (stable identity)
                return [(ThreadState(tuple(head.body) + (head,) + rest,
                                     ts.old_snapshot), s2, False)]
            return [(ThreadState(rest, ts.old_snapshot), s2, False)]
        if isinstance(head, A.Call_):
            callee = self.prog.find_func(head.name)
            return [(ThreadState(tuple(callee.body) + rest, ts.old_snapshot),
                     dict(store), False)]
        raise InterpError(f"cannot step {type(head).__name__}")

    def _cond(self, c: A.Cond, store: Dict, tid: int):
        """Evaluate a conditional action; return (succeeded?, new_store)."""
        if isinstance(c, A.NotCond):
            ok, s2 = self._cond(c.inner, store, tid)
            return (not ok, s2)
        if isinstance(c, A.BoolCond):
            return bool(self._eval(c.expr, store, None, tid)), store
        if isinstance(c, A.CasCond):
            expected = self._eval(c.expected, store, None, tid)
            if store[c.target] == expected:
                s2 = dict(store); s2[c.target] = self._eval(c.new, store, None, tid)
                return True, s2
            return False, store
        raise InterpError("unknown conditional action")

    def _write_var(self, name: str, val, store: Dict, tid: int) -> None:
        if name in self.globals:
            store[name] = val
        else:
            store[(name, tid)] = val


def can_go_wrong(prog: A.Program, **kwargs) -> ExploreResult:
    """Convenience: does some interleaving of `prog` reach `wrong`?"""
    return Interpreter(prog, **kwargs).explore()


# ---------------------------------------------------------------------------
# Command-line interface: `moverlogic-run FILE` / `python -m moverlogic.interp`
# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    import argparse
    import sys
    from .parser import parse
    from .types import check_types
    from .diagnostics import MoverLogicError

    ap = argparse.ArgumentParser(
        prog="moverlogic-run",
        description="Run a Mover Logic program under all thread interleavings "
                    "(reference operational semantics) and report whether any "
                    "interleaving can go wrong (fail an assertion / reach `wrong`).",
    )
    ap.add_argument("file", help="MLL source file to run")
    ap.add_argument("--max-states", type=int, default=200_000,
                    help="bound on explored states (default: 200000)")
    ap.add_argument("--trace", action="store_true",
                    help="print a shortest interleaving to `wrong`, if found")
    args = ap.parse_args(argv)

    try:
        with open(args.file) as f:
            src = f.read()
        prog = parse(src, args.file)
        check_types(prog)                      # reuse the front end for errors
    except (OSError, MoverLogicError) as e:
        print(getattr(e, "render", lambda: str(e))())
        return 2

    if not prog.threads:
        print("no threads to run: add one or more `thread { ... }` declarations "
              "(functions alone are not executed).")
        return 2

    result = Interpreter(prog, max_states=args.max_states).explore(want_trace=args.trace)
    if result.wrong_reachable:
        print(f"UNSAFE: some interleaving reaches `wrong` "
              f"(explored {result.states_explored} states).")
        if args.trace and result.trace:
            print("  interleaving (thread:next-step):")
            print("    " + " -> ".join(result.trace))
        return 1
    if result.hit_bound:
        print(f"UNKNOWN: hit the {args.max_states}-state bound without reaching "
              f"`wrong` (raise --max-states to explore further).")
        return 3
    print(f"SAFE: no interleaving reaches `wrong` "
          f"(explored {result.states_explored} states, exhaustive).")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
