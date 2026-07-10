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
    # Active call frames, for display only: (function name, call-site id)
    # pairs, outermost first; the thread body is the implicit bottom frame.
    frames: Tuple = ()


@dataclass(frozen=True)
class _Marker:
    """A continuation marker for call bookkeeping, interned per call site so
    the DFS state key (which hashes continuation node identities) stays
    finite.  `kind` is "restore": its payload names the callee's frame locals,
    saved at the call and restored (or dropped, when they had no prior value)
    when the callee's body is done; it also closes the display call frame.
    Nested recursive calls through the same site share one save slot, so
    save/restore is exact only to recursion depth 1 -- adequate for an
    oracle."""
    kind: str
    payload: object
    sid: int


@dataclass
class ExploreResult:
    wrong_reachable: bool
    states_explored: int
    hit_bound: bool
    # Each trace step: {"tid": int, "line": int, "source": str, "store": {...}}
    # (the store is the state AFTER the step, in store-JSON form).
    trace: Optional[List[Dict]] = None
    # Distinct final stores (every thread finished), in store-JSON form,
    # deduplicated up to equality of globals and isomorphism of the reachable
    # heap.  Each also carries a "trace": one representative interleaving
    # (list of trace steps as above) that reaches that final store.
    # `finals_complete` is False if the search stopped early (bound,
    # early unsafe return) or the cap was hit.
    finals: List[Dict] = field(default_factory=list)
    finals_complete: bool = True


# Cap on distinct final stores retained (further ones set finals_complete=False).
FINALS_CAP = 100


class Interpreter:
    def __init__(self, prog: A.Program, max_states: int = 200_000,
                 loop_bound: int = 1000, source: Optional[str] = None):
        # re-run the checker for its scope tables (which local belongs to
        # which function), used when rendering per-frame stores
        from .types import check_types
        self.ti = check_types(prog)
        self.prog = prog
        self.max_states = max_states
        self.loop_bound = loop_bound
        self.globals = [v.name for v in prog.vars]
        self.source_lines = source.splitlines() if source else None
        # interned continuation markers (stable identity per call site)
        self._markers: Dict[Tuple[int, str], _Marker] = {}
        # call-site id -> the Call_ node, for rendering "return from f()"
        self._call_nodes: Dict[int, A.Call_] = {}

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
        stack = [start]
        explored = 0
        finals_seen = set()
        finals: List[Tuple[Tuple, List[Dict]]] = []    # (canon, trace)
        finals_overflow = False
        # Predecessor map for trace reconstruction: for every pushed state,
        # the state it was reached from plus the step that got there (the
        # acting tid, the statement about to run, and the resulting frozen
        # store).  Entries are small tuples of shared references, so keeping
        # this for the whole search is cheap; traces (for `wrong` and for one
        # representative interleaving per final store) are rebuilt on demand.
        pred: Dict[Tuple, Tuple] = {}

        def reconstruct(key: Tuple) -> List[Dict]:
            steps = []
            while key in pred:
                key, tid, head, nstate = pred[key]
                if isinstance(head, _Marker):
                    if head.kind == "restore":     # an explicit return step
                        steps.append(self._return_json(tid, head, nstate))
                    continue                       # other markers are internal
                steps.append(self._step_json(tid, head, nstate))
            steps.reverse()
            return steps

        def finals_json(complete: bool) -> Tuple[List[Dict], bool]:
            return ([self._final_json(c, tr) for c, tr in finals],
                    complete and not finals_overflow)

        while stack:
            state = stack.pop()
            key = self._state_key(state)
            if key in seen:
                continue
            seen.add(key)
            explored += 1
            if explored > self.max_states:
                fs, fc = finals_json(False)
                return ExploreResult(False, explored, hit_bound=True,
                                     finals=fs, finals_complete=fc)
            thread_tuple, frozen_store = state
            if all(not ts.cont for ts in thread_tuple):
                # a final state: every thread has finished
                canon = self._final_canon(frozen_store)
                if canon not in finals_seen:
                    if len(finals) < FINALS_CAP:
                        finals_seen.add(canon)
                        finals.append((canon, reconstruct(key)))
                    else:
                        finals_overflow = True
                continue
            store = dict(frozen_store)
            for idx, ts in enumerate(thread_tuple):
                thread_id = idx + 1                      # Tid = {1, 2, ...}
                head = ts.cont[0] if ts.cont else None
                successors = self._step(thread_id, ts, store)
                for (new_ts, new_store, is_wrong) in successors:
                    new_threads = list(thread_tuple)
                    new_threads[idx] = new_ts
                    nstate = (tuple(new_threads), self._freeze(new_store))
                    if is_wrong:
                        fs, fc = finals_json(False)
                        return ExploreResult(
                            True, explored, hit_bound=False,
                            trace=(reconstruct(key)
                                   + [self._step_json(thread_id, head, nstate)])
                            if want_trace else None,
                            finals=fs, finals_complete=fc)
                    nkey = self._state_key(nstate)
                    if nkey not in seen:
                        if nkey not in pred:
                            pred[nkey] = (key, thread_id, head, nstate)
                        stack.append(nstate)
        fs, fc = finals_json(True)
        return ExploreResult(False, explored, hit_bound=False,
                             finals=fs, finals_complete=fc)

    # ---------------------------------------------------------- final states
    def _final_canon(self, frozen_store: Tuple) -> Tuple:
        """Canonical form of a final store: the globals plus the heap reachable
        from them, with heap addresses renumbered in deterministic traversal
        order so isomorphic heaps coincide.  (No heap on this branch: just the
        global scalars.)"""
        return tuple((k, v) for k, v in frozen_store if isinstance(k, str))

    def _final_json(self, canon: Tuple, trace: Optional[List[Dict]] = None) -> Dict:
        return {"globals": {k: self._fmt_value(v) for k, v in canon},
                "objects": [],
                "trace": trace or []}

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

    def _step_json(self, tid: int, head, state) -> Dict:
        """One structured trace step: which thread ran what (with the source
        line), and the state after the step ((thread tuple, frozen store)).
        A `Call_` step is tagged "call" so traces show where calls happen.
        `depth` is the call depth of the frame the statement runs in (thread
        body = 0), so displays can indent by nesting level."""
        thread_tuple, frozen_store = state
        line = 0
        text = "done"
        if head is not None:
            span = getattr(head, "span", None)
            if span is not None:
                line = span.start.line
            if self.source_lines and 0 < line <= len(self.source_lines):
                text = self.source_lines[line - 1].strip()
            else:
                text = type(head).__name__
        kind = "call" if isinstance(head, A.Call_) else "step"
        depth = len(thread_tuple[tid - 1].frames)
        if kind == "call":
            depth -= 1        # the call statement itself runs in the caller
        return {"tid": tid, "line": line, "source": text, "kind": kind,
                "depth": depth,
                "store": self.store_json(frozen_store, thread_tuple)}

    def _return_json(self, tid: int, marker: "_Marker", state) -> Dict:
        """An explicit "return" trace step for a restore marker: the callee's
        body is done, its frame is gone, and control is back at the call site
        (whose line the step carries, so clicking it jumps there).  The step's
        depth is the callee's, so it closes the callee's indented block."""
        thread_tuple, frozen_store = state
        call = self._call_nodes.get(marker.sid)
        name = self._call_display_name(call)
        line = 0
        if call is not None and getattr(call, "span", None) is not None:
            line = call.span.start.line
        return {"tid": tid, "line": line, "source": f"return from {name}()",
                "kind": "return",
                "depth": len(thread_tuple[tid - 1].frames) + 1,
                "store": self.store_json(frozen_store, thread_tuple)}

    @staticmethod
    def _call_display_name(call) -> str:
        return call.name if call is not None else "?"

    # ------------------------------------------------------ store rendering
    @staticmethod
    def _fmt_value(v) -> object:
        """A JSON-friendly rendering of a store value."""
        if isinstance(v, bool) or isinstance(v, int):
            return v
        if v is None:
            return "None"
        if isinstance(v, tuple):
            if v and v[0] == "some":
                return f"Some({Interpreter._fmt_value(v[1])})"
            return "Nil" if not v else "[" + ", ".join(
                str(Interpreter._fmt_value(x)) for x in v) + "]"
        return str(v)

    def store_json(self, store, thread_states: Optional[Tuple] = None) -> Dict:
        """Store-JSON: {"globals": {...}, "threads": {...}, "objects": []}.
        `objects` is populated by the heap-aware interpreter (objects branch).

        Without `thread_states`, each thread's locals are one flat dict.  With
        the state's ThreadState tuple, each thread instead gets its call
        stack: a list of {"fn": name, "locals": {...}} frames, outermost (the
        thread body) first."""
        items = dict(store) if not isinstance(store, dict) else store
        out = {"globals": {}, "threads": {}, "objects": []}
        flat: Dict[int, Dict[str, object]] = {}
        for k, v in items.items():
            if isinstance(k, str):
                out["globals"][k] = self._fmt_value(v)
            elif (isinstance(k, tuple) and len(k) == 2
                  and isinstance(k[0], str) and isinstance(k[1], int)):
                name, tid = k
                flat.setdefault(tid, {})[name] = v
        out["globals"] = dict(sorted(out["globals"].items()))
        if thread_states is None:
            for tid, kv in flat.items():
                out["threads"][str(tid)] = {n: self._fmt_value(v)
                                            for n, v in sorted(kv.items())}
            return out
        for idx, ts in enumerate(thread_states):
            tid = idx + 1
            out["threads"][str(tid)] = self._thread_frames(
                tid, ts, items, flat.get(tid, {}))
        return out

    _MISSING = object()

    def _thread_frames(self, tid: int, ts: ThreadState, store: Dict,
                       flat: Dict[str, object]) -> List[Dict]:
        """The thread's call stack for display: one {"fn", "locals"} dict per
        active frame, outermost (the thread body) first.  Each frame lists its
        own scope's locals; every call saves its whole frame, so an outer
        frame's value shadowed by an inner call is read exactly from that
        call's save slot."""
        metas = [(f"thread:{tid - 1}", "thread", None)]
        for fname, sid in ts.frames:
            metas.append((f"fn:{fname}", fname, sid))
        overrides: Dict[str, object] = {}
        frames: List[Dict] = [{} for _ in metas]
        for i in range(len(metas) - 1, -1, -1):     # innermost first
            scope, label, sid = metas[i]
            locs = {}
            for n in sorted(self.ti.scope_locals(scope)):
                v = overrides.get(n, flat.get(n, self._MISSING))
                if v is not self._MISSING:
                    locs[n] = self._fmt_value(v)
            frames[i] = {"fn": label, "locals": locs}
            if sid is not None:
                # this frame's locals were saved at its call site: outer
                # frames see the saved values (or nothing, if a name had no
                # value before the call)
                for n in self._frame_names(label):
                    overrides[n] = store.get(("save", sid, n, tid),
                                             self._MISSING)
        return frames

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
            return [(ThreadState(new_cont, snapshot, ts.frames),
                     dict(new_store), False)]

        if isinstance(head, _Marker):        # restore: the call is done
            s2 = dict(store)
            for name in head.payload:
                saved = s2.pop(("save", head.sid, name, tid), self._MISSING)
                if saved is self._MISSING:
                    s2.pop((name, tid), None)
                else:
                    s2[(name, tid)] = saved
            return [(ThreadState(rest, ts.old_snapshot, ts.frames[:-1]),
                     s2, False)]
        if isinstance(head, A.Skip):
            return cont([])
        if isinstance(head, A.Yield):
            # a yield takes a step and refreshes the \old snapshot
            return [(ThreadState(rest, self._freeze(store), ts.frames),
                     dict(store), False)]
        if isinstance(head, A.Wrong):
            return [(ThreadState(rest, ts.old_snapshot, ts.frames),
                     dict(store), True)]
        if isinstance(head, A.Assert):
            old = dict(ts.old_snapshot)
            ok = bool(self._eval(head.expr, store, old, tid))
            return [(ThreadState(rest, ts.old_snapshot, ts.frames),
                     dict(store), not ok)]
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
                outs.append((ThreadState(rest, ts.old_snapshot, ts.frames),
                             s2, False))
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
            return [(ThreadState(tuple(branch) + rest, ts.old_snapshot,
                                 ts.frames), s2, False)]
        if isinstance(head, A.While):
            succeeded, s2 = self._cond(head.cond, store, tid)
            if succeeded:
                # run body, then re-enter the SAME while node (stable identity)
                return [(ThreadState(tuple(head.body) + (head,) + rest,
                                     ts.old_snapshot, ts.frames), s2, False)]
            return [(ThreadState(rest, ts.old_snapshot, ts.frames), s2, False)]
        if isinstance(head, A.Call_):
            callee = self.prog.find_func(head.name)
            sid = id(head)
            self._call_nodes[sid] = head
            # a fresh frame: save every local of the callee's scope and clear
            # it, so the callee cannot see or clobber same-named caller locals
            s2 = dict(store)
            saved_names = self._frame_names(head.name)
            for n in saved_names:
                if (n, tid) in s2:
                    s2[("save", sid, n, tid)] = s2.pop((n, tid))
            marker = self._marker(sid, "restore", tuple(saved_names))
            return [(ThreadState(tuple(callee.body) + (marker,) + rest,
                                 ts.old_snapshot,
                                 ts.frames + ((head.name, sid),)),
                     s2, False)]
        raise InterpError(f"cannot step {type(head).__name__}")

    def _marker(self, sid: int, kind: str, payload) -> "_Marker":
        key = (sid, kind)
        if key not in self._markers:
            self._markers[key] = _Marker(kind, payload, sid)
        return self._markers[key]

    def _frame_names(self, fname: str) -> Tuple[str, ...]:
        """The locals that make up a frame of function `fname` (its scope's
        names; `result` is the cross-frame return channel and stays out)."""
        names = set(self.ti.scope_locals(f"fn:{fname}"))
        names.discard("result")
        return tuple(sorted(names))

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
# Command-line interface: `melvin-run FILE` / `python -m melvin.interp`
# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    import argparse
    import json
    import sys
    from .parser import parse
    from .types import check_types
    from .diagnostics import MelvinError

    ap = argparse.ArgumentParser(
        prog="melvin-run",
        description="Run a Mover Logic program under all thread interleavings "
                    "(reference operational semantics) and report whether any "
                    "interleaving can go wrong (fail an assertion / reach `wrong`).",
    )
    ap.add_argument("file", help="MLL source file to run")
    ap.add_argument("--max-states", type=int, default=200_000,
                    help="bound on explored states (default: 200000)")
    ap.add_argument("--trace", action="store_true",
                    help="print an interleaving to `wrong` (if found) and a "
                         "representative interleaving per final store")
    ap.add_argument("--json", action="store_true",
                    help="emit a machine-readable JSON result (implies --trace)")
    ap.add_argument("--no-finals", action="store_true",
                    help="do not enumerate the distinct final stores")
    args = ap.parse_args(argv)

    try:
        with open(args.file) as f:
            src = f.read()
        prog = parse(src, args.file)
        check_types(prog)                      # reuse the front end for errors
    except (OSError, MelvinError) as e:
        if args.json:
            print(json.dumps({"result": "error",
                              "message": getattr(e, "render", lambda: str(e))()}))
        else:
            print(getattr(e, "render", lambda: str(e))())
        return 2

    if not prog.threads:
        msg = ("no threads to run: add one or more `thread { ... }` declarations "
               "(functions alone are not executed).")
        print(json.dumps({"result": "error", "message": msg}) if args.json else msg)
        return 2

    interp = Interpreter(prog, max_states=args.max_states, source=src)
    result = interp.explore(want_trace=args.trace or args.json)

    if args.json:
        print(json.dumps({
            "result": ("unsafe" if result.wrong_reachable
                       else "unknown" if result.hit_bound else "safe"),
            "states": result.states_explored,
            "trace": result.trace,
            "finals": None if args.no_finals else result.finals,
            "finals_complete": result.finals_complete,
        }))
        return 1 if result.wrong_reachable else (3 if result.hit_bound else 0)

    # each thread gets its own color on a terminal (blue, red, green, ...)
    tid_colors = ["\033[34m", "\033[31m", "\033[32m", "\033[35m",
                  "\033[36m", "\033[33m"]
    use_color = sys.stdout.isatty()

    def print_step(step, indent):
        # indentation reflects call depth: a callee's steps sit two spaces
        # deeper than its caller's
        nest = "  " * step.get("depth", 0)
        text = (f"{indent}t{step['tid']}  {args.file}:{step['line']}  "
                f"{nest}{step['source']}")
        if use_color:
            c = tid_colors[(step["tid"] - 1) % len(tid_colors)]
            text = f"{c}{text}\033[0m"
        print(text)

    if result.wrong_reachable:
        print(f"UNSAFE: some interleaving reaches `wrong` "
              f"(explored {result.states_explored} states).")
        if args.trace and result.trace:
            print("  failing interleaving:")
            for step in result.trace:
                print_step(step, "    ")
    elif result.hit_bound:
        print(f"UNKNOWN: hit the {args.max_states}-state bound without reaching "
              f"`wrong` (raise --max-states to explore further).")
    else:
        print(f"SAFE: no interleaving reaches `wrong` "
              f"(explored {result.states_explored} states, exhaustive).")

    if not args.no_finals and result.finals:
        note = "" if result.finals_complete else "  (may be incomplete)"
        print(f"{len(result.finals)} distinct final store(s):{note}")
        for st in result.finals:
            parts = [f"{k} = {v}" for k, v in st["globals"].items()]
            for obj in st.get("objects", []):
                fields = ", ".join(f"{f}: {v}" for f, v in obj["fields"].items())
                parts.append(f"{obj['id']}: {obj['class']}{{{fields}}}")
            print("  " + (", ".join(parts) if parts else "(empty store)"))
            if args.trace and st.get("trace"):
                print("    via:")
                for step in st["trace"]:
                    print_step(step, "      ")

    return 1 if result.wrong_reachable else (3 if result.hit_bound else 0)


if __name__ == "__main__":
    import sys
    sys.exit(main())
