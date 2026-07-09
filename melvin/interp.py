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


class StuckWrong(Exception):
    """A run-time fault (null dereference, out-of-bounds index, negative
    allocation size): the step goes wrong, exactly like `wrong`."""


# A store value is an int, a tuple (immutable list), ("some", v) / None, or a
# heap reference ("ref", TypeName, addr) with addr >= 1.  All null references
# are the single value NULL, so `x == null` is plain equality.
NilVal = ()          # empty immutable list
NULL = ("ref", None, 0)


# Heap layout inside the flat store dict (all keys hashable, so the existing
# freeze/DFS machinery applies unchanged):
#   ("next", T)          -> next fresh address for class/array type T
#   ("fld", C, a, f)     -> value of field f of object a of class C
#   ("len", AT, a)       -> length of array a of array type AT
#   ("elem", AT, a, i)   -> element i of array a (absent = type default 0)


@dataclass(frozen=True)
class ThreadState:
    """One thread: a stack of statements to run, plus its \\old snapshot key."""
    cont: Tuple                     # tuple of AST statement nodes (a stack)
    old_snapshot: Tuple             # frozen store items at the last yield


@dataclass(frozen=True)
class _Marker:
    """A continuation marker for call save/restore, interned per call site so
    the DFS state key (which hashes continuation node identities) stays
    finite.  `kind` is "restore" (payload: names to restore) or "bindresult"
    (payload: the local receiving `result`).  Nested recursive calls through
    the same site share one save slot, so save/restore is exact only to
    recursion depth 1 -- adequate for an oracle."""
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
        # (re-)run the checker: it desugars `x = f(args)` into Call_ statements,
        # validates the program, and yields the type tables (nominal array
        # types, resolved call targets) the heap semantics needs
        from .types import check_types
        self.ti = check_types(prog)
        self.prog = prog
        self.max_states = max_states
        self.loop_bound = loop_bound
        self.globals = [v.name for v in prog.vars]
        self.classes = {c.name: c for c in prog.classes}
        self.source_lines = source.splitlines() if source else None
        # interned continuation markers for call save/restore (stable identity
        # per call site, so the DFS state key stays finite)
        self._markers: Dict[Tuple[int, str], object] = {}

    # ------------------------------------------------------------ store
    def _initial_store(self) -> Dict:
        store: Dict = {}
        for v in self.prog.vars:
            store[v.name] = self._default(v.type)
        # apply the init predicate as simple equality constraints if present
        if self.prog.init is not None:
            self._apply_init(self.prog.init.pred, store)
        return store

    def _default(self, ty: A.TypeExpr):
        if ty.is_array:
            return 0     # top-level globals of type T[] keep value semantics
        if ty.name == "List":
            return NilVal
        if ty.name == "Optional":
            return None
        if ty.name in self.classes:
            return NULL
        return 0

    def _field_default(self, cls: str, fld: A.VarDecl):
        if fld.type.is_array or fld.type.name in self.classes:
            return NULL
        return self._default(fld.type)

    @staticmethod
    def _arrtype(cls: str, fld: str) -> str:
        return f"Arr_{cls}_{fld}"

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
        if t is A.NullLit:
            return NULL
        if t is A.Old:
            src = old if old is not None else store
            return self._eval(e.inner, src, src, tid)
        if t is A.Var:
            return self._read_var(e.name, store, tid)
        if t is A.FieldAccess:
            ref = self._eval(e.base, store, old, tid)
            return self._read_field(ref, e.field, store)
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
            if isinstance(base, tuple) and len(base) == 3 and base[0] == "ref":
                return self._read_elem(base, idx, store)
            return base[idx] if isinstance(base, (list, tuple)) else 0
        if t is A.Quant:
            results = []
            for val in self._quant_range(e, store, old, tid):
                shadow = dict(store)
                shadow[("__bound", e.var)] = val
                results.append(self._eval(e.body, shadow, old, tid))
            if e.kind == "forall":
                return all(results)
            return any(results)
        raise InterpError(f"cannot evaluate {t.__name__}")

    def _quant_range(self, e: A.Quant, store, old, tid):
        if e.cls is None:
            lo = self._eval(e.lo, store, old, tid)
            hi = self._eval(e.hi, store, old, tid)
            return range(lo, hi)
        if e.cls == "int":
            # unbounded int quantifier: sample a small adversarial window
            return range(-2, 5)
        if "." in e.cls:
            cname, fname = e.cls.split(".", 1)
            at = self._arrtype(cname, fname)
        else:
            at = e.cls
        n = store.get(("next", at), 1)
        return [("ref", at, a) for a in range(1, n)]

    def _read_field(self, ref, field: str, store: Dict):
        if not (isinstance(ref, tuple) and len(ref) == 3 and ref[0] == "ref") \
                or ref[2] == 0:
            raise StuckWrong("null dereference")
        return store.get(("fld", ref[1], ref[2], field), 0)

    def _read_elem(self, ref, idx, store: Dict):
        if ref[2] == 0:
            raise StuckWrong("null array")
        n = store.get(("len", ref[1], ref[2]), 0)
        if not (0 <= idx < n):
            raise StuckWrong("index out of bounds")
        return store.get(("elem", ref[1], ref[2], idx), 0)

    def _read_var(self, name: str, store: Dict, tid: int):
        if ("__bound", name) in store:
            return store[("__bound", name)]
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
        if e.name == "length":
            ref = args[0]
            if not (isinstance(ref, tuple) and len(ref) == 3 and ref[0] == "ref") \
                    or ref[2] == 0:
                raise StuckWrong("length of null array")
            return store.get(("len", ref[1], ref[2]), 0)
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
                key, tid, head, fstore = pred[key]
                if isinstance(head, _Marker):
                    continue      # internal call save/restore, not a user step
                steps.append(self._step_json(tid, head, fstore))
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
                    if is_wrong:
                        fs, fc = finals_json(False)
                        frozen = self._freeze(new_store)
                        return ExploreResult(
                            True, explored, hit_bound=False,
                            trace=(reconstruct(key)
                                   + [self._step_json(thread_id, head, frozen)])
                            if want_trace else None,
                            finals=fs, finals_complete=fc)
                    new_threads = list(thread_tuple)
                    new_threads[idx] = new_ts
                    nstate = (tuple(new_threads), self._freeze(new_store))
                    nkey = self._state_key(nstate)
                    if nkey not in seen:
                        if nkey not in pred:
                            pred[nkey] = (key, thread_id, head, nstate[1])
                        stack.append(nstate)
        fs, fc = finals_json(True)
        return ExploreResult(False, explored, hit_bound=False,
                             finals=fs, finals_complete=fc)

    # ---------------------------------------------------------- final states
    @staticmethod
    def _is_ref(v) -> bool:
        return isinstance(v, tuple) and len(v) == 3 and v[0] == "ref"

    def _class_fields(self, cls: str) -> List[str]:
        c = self.classes.get(cls)
        return [f.name for f in c.fields] if c else []

    def _final_canon(self, frozen_store: Tuple) -> Tuple:
        """Canonical form of a final store: the globals plus the heap REACHABLE
        from the globals AND from every thread's still-live locals, with heap
        addresses renumbered in deterministic traversal order so isomorphic
        heaps coincide.  Rooting at the locals keeps objects a thread allocated
        and still holds (like `c` in each client) instead of discarding them as
        garbage; each object node also carries its allocating thread, so two
        threads' otherwise-identical objects stay distinct."""
        store = dict(frozen_store)
        globals_items = sorted(
            (k, v) for k, v in store.items() if isinstance(k, str))
        # thread-local roots: keys (name, tid); visit in (tid, name) order so
        # the renumbering -- and hence the canonical form -- is deterministic.
        local_roots = sorted(
            (k, v) for k, v in store.items()
            if isinstance(k, tuple) and len(k) == 2
            and isinstance(k[0], str) and isinstance(k[1], int))

        idmap: Dict[Tuple, int] = {}
        order: List[Tuple] = []

        def visit(v) -> None:
            if not self._is_ref(v) or v[2] == 0 or v in idmap:
                return
            idmap[v] = len(order) + 1
            order.append(v)
            t, a = v[1], v[2]
            for fld in self._class_fields(t):
                visit(store.get(("fld", t, a, fld), 0))

        for _k, v in globals_items:
            visit(v)
        for (_name, _tid), v in local_roots:
            visit(v)

        def cv(v):
            if self._is_ref(v):
                return "null" if v[2] == 0 else f"#{idmap[v]}"
            return v

        nodes = []
        for ref in order:
            t, a = ref[1], ref[2]
            owner = store.get(("owner", t, a))
            if t in self.classes:
                nodes.append((t, owner, tuple(
                    (fld, cv(store.get(("fld", t, a, fld), 0)))
                    for fld in sorted(self._class_fields(t)))))
            else:                             # a heap array
                n = store.get(("len", t, a), 0)
                elems = tuple(store.get(("elem", t, a, i), 0)
                              for i in range(min(n, 4096)))
                nodes.append((t, owner, ("len", n), elems))
        return (tuple((k, cv(v)) for k, v in globals_items), tuple(nodes))

    def _arr_label(self, at: str, length) -> str:
        elem = self.ti.arrays.get(at, "int")
        return f"{elem}[{length}]"

    def _final_json(self, canon: Tuple, trace: Optional[List[Dict]] = None) -> Dict:
        globals_items, nodes = canon
        objects = []
        for i, node in enumerate(nodes, 1):
            if len(node) == 3:                # an object
                t, owner, fields = node
                objects.append({"id": f"#{i}", "class": t,
                                "allocated_by": owner,
                                "fields": {f: self._fmt_value(v)
                                           for f, v in fields}})
            else:                             # an array
                t, owner, (_lenlbl, n), elems = node
                fields = {str(j): self._fmt_value(v)
                          for j, v in enumerate(elems[:16])}
                if n > 16:
                    fields["…"] = f"({n - 16} more)"
                objects.append({"id": f"#{i}",
                                "class": self._arr_label(t, n),
                                "allocated_by": owner,
                                "fields": fields})
        return {"globals": {k: self._fmt_value(v) for k, v in globals_items},
                "objects": objects,
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

    def _step_json(self, tid: int, head, store_after) -> Dict:
        """One structured trace step: which thread ran what (with the source
        line), and the store after the step (a dict or a frozen store)."""
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
        return {"tid": tid, "line": line, "source": text,
                "store": self.store_json(store_after)}

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

    def store_json(self, store) -> Dict:
        """Store-JSON: {"globals": {...}, "threads": {"1": {...}}, "objects":
        [{"id": "#1", "class": "C", "fields": {...}}, ...]}.  Every allocated
        heap object/array is shown (renumbered deterministically); reference
        values render as the matching "#n" so the UI can draw arrows."""
        items = dict(store) if not isinstance(store, dict) else store

        # deterministic ids for every allocated object/array
        idmap: Dict[Tuple, int] = {}
        for t in sorted(list(self.classes) + list(self.ti.arrays)):
            for a in range(1, items.get(("next", t), 1)):
                idmap[("ref", t, a)] = len(idmap) + 1

        def fmt(v):
            if self._is_ref(v):
                return "null" if v[2] == 0 else f"#{idmap.get(v, '?')}"
            return self._fmt_value(v)

        out = {"globals": {}, "threads": {}, "objects": []}
        for k, v in items.items():
            if isinstance(k, str):
                out["globals"][k] = fmt(v)
            elif isinstance(k, tuple) and len(k) == 2 \
                    and isinstance(k[0], str) and isinstance(k[1], int):
                name, tid = k
                out["threads"].setdefault(str(tid), {})[name] = fmt(v)
        for ref, i in idmap.items():
            _tag, t, a = ref
            owner = items.get(("owner", t, a))
            if t in self.classes:
                out["objects"].append({
                    "id": f"#{i}", "class": t, "allocated_by": owner,
                    "fields": {f: fmt(items.get(("fld", t, a, f), 0))
                               for f in self._class_fields(t)}})
            else:
                n = items.get(("len", t, a), 0)
                fields = {str(j): fmt(items.get(("elem", t, a, j), 0))
                          for j in range(min(n, 16))}
                if n > 16:
                    fields["…"] = f"({n - 16} more)"
                out["objects"].append({"id": f"#{i}", "class": self._arr_label(t, n),
                                       "allocated_by": owner, "fields": fields})
        out["globals"] = dict(sorted(out["globals"].items()))
        for t in out["threads"]:
            out["threads"][t] = dict(sorted(out["threads"][t].items()))
        return out

    def _step(self, tid: int, ts: ThreadState, store: Dict):
        """Return a list of (new ThreadState, new store dict, wrong?) successors
        for one small step of thread `tid`.  An empty list means the thread is
        finished or blocked."""
        try:
            return self._step_inner(tid, ts, store)
        except StuckWrong:
            # a run-time fault (null dereference, bad index, bad allocation)
            return [(ThreadState(ts.cont[1:], ts.old_snapshot), dict(store), True)]

    def _marker(self, sid: int, kind: str, payload) -> "_Marker":
        key = (sid, kind)
        if key not in self._markers:
            self._markers[key] = _Marker(kind, payload, sid)
        return self._markers[key]

    def _step_inner(self, tid: int, ts: ThreadState, store: Dict):
        if not ts.cont:
            return []
        head = ts.cont[0]
        rest = ts.cont[1:]

        def cont(new_head_list, new_store=store, snapshot=ts.old_snapshot):
            new_cont = tuple(new_head_list) + rest
            return [(ThreadState(new_cont, snapshot), dict(new_store), False)]

        if isinstance(head, _Marker):
            s2 = dict(store)
            if head.kind == "restore":
                for name in head.payload:
                    saved = s2.pop(("save", head.sid, name, tid), None)
                    if saved is None:
                        s2.pop((name, tid), None)
                    else:
                        s2[(name, tid)] = saved
            else:  # "bindresult"
                s2[(head.payload, tid)] = s2.get(("result", tid), 0)
            return cont([], s2)
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
            if isinstance(head.rhs, A.New):
                val = self._allocate(head.rhs.cls, s2, tid)
            elif isinstance(head.rhs, A.NewArray):
                cls = head.rhs
                size = self._eval(cls.size, store, dict(ts.old_snapshot), tid)
                if size < 0:
                    raise StuckWrong("negative array size")
                at = self.ti.expr_class[id(head.rhs)]   # nominal array type
                addr = s2.get(("next", at), 1)
                s2[("next", at)] = addr + 1
                s2[("owner", at, addr)] = tid           # allocating thread
                s2[("len", at, addr)] = size
                val = ("ref", at, addr)
            else:
                val = self._eval(head.rhs, store, dict(ts.old_snapshot), tid)
            self._write_var(head.lhs, val, s2, tid)
            return cont([], s2)
        if isinstance(head, A.FieldWrite):
            ref = self._eval(head.base, store, dict(ts.old_snapshot), tid)
            if not (isinstance(ref, tuple) and len(ref) == 3 and ref[0] == "ref") \
                    or ref[2] == 0:
                raise StuckWrong("null dereference")
            val = self._eval(head.rhs, store, dict(ts.old_snapshot), tid)
            s2 = dict(store)
            s2[("fld", ref[1], ref[2], head.field)] = val
            return cont([], s2)
        if isinstance(head, A.ArrayWrite):
            ref = self._eval(head.base, store, dict(ts.old_snapshot), tid)
            if not (isinstance(ref, tuple) and len(ref) == 3 and ref[0] == "ref") \
                    or ref[2] == 0:
                raise StuckWrong("null array")
            idx = self._eval(head.index, store, dict(ts.old_snapshot), tid)
            n = store.get(("len", ref[1], ref[2]), 0)
            if not (0 <= idx < n):
                raise StuckWrong("index out of bounds")
            val = self._eval(head.rhs, store, dict(ts.old_snapshot), tid)
            s2 = dict(store)
            s2[("elem", ref[1], ref[2], idx)] = val
            return cont([], s2)
        if isinstance(head, A.UnstableRead):
            # nondeterministic: the current value, plus a few type-appropriate
            # adversarial ones (an unstable read may load any value).
            if head.source_expr is not None:
                ref = self._eval(head.source_expr.base, store, None, tid)
                src = self._read_field(ref, head.source, store)
            else:
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
            if head.lock_expr is not None:
                ref = self._eval(head.lock_expr.base, store, None, tid)
                cur = self._read_field(ref, head.lock, store)
                if cur != 0:
                    return []                                  # blocked
                s2 = dict(store)
                s2[("fld", ref[1], ref[2], head.lock)] = tid
                return cont([], s2)
            if store[head.lock] == 0:
                s2 = dict(store); s2[head.lock] = tid         # tid is 1-based
                return cont([], s2)
            return []                                          # blocked
        if isinstance(head, A.Release):
            if head.lock_expr is not None:
                ref = self._eval(head.lock_expr.base, store, None, tid)
                self._read_field(ref, head.lock, store)        # null check
                s2 = dict(store)
                s2[("fld", ref[1], ref[2], head.lock)] = 0
                return cont([], s2)
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
            target = self.ti.call_target.get(id(head), head.name)
            callee = self.prog.find_func(target)
            s2 = dict(store)
            sid = id(head)
            saved_names = []
            if head.receiver is not None:
                ref = self._eval(head.receiver, store, None, tid)
                if not (isinstance(ref, tuple) and len(ref) == 3
                        and ref[0] == "ref") or ref[2] == 0:
                    raise StuckWrong("null receiver")
                if ("this", tid) in s2:
                    s2[("save", sid, "this", tid)] = s2[("this", tid)]
                s2[("this", tid)] = ref
                saved_names.append("this")
            for p, arg in zip(callee.params, head.args):
                val = self._eval(arg, store, None, tid)
                if (p.name, tid) in s2:
                    s2[("save", sid, p.name, tid)] = s2[(p.name, tid)]
                s2[(p.name, tid)] = val
                saved_names.append(p.name)
            tail = ()
            if saved_names:
                tail += (self._marker(sid, "restore", tuple(saved_names)),)
            if head.assign_to is not None and head.assign_to != "result":
                tail += (self._marker(sid, "bindresult", head.assign_to),)
            return [(ThreadState(tuple(callee.body) + tail + rest,
                                 ts.old_snapshot), s2, False)]
        raise InterpError(f"cannot step {type(head).__name__}")

    def _allocate(self, cls: str, store: Dict, tid: int):
        addr = store.get(("next", cls), 1)
        store[("next", cls)] = addr + 1
        store[("owner", cls, addr)] = tid          # allocating thread
        cdecl = self.classes[cls]
        for fld in cdecl.fields:
            store[("fld", cls, addr, fld.name)] = self._field_default(cls, fld)
        return ("ref", cls, addr)

    def _cond(self, c: A.Cond, store: Dict, tid: int):
        """Evaluate a conditional action; return (succeeded?, new_store)."""
        if isinstance(c, A.NotCond):
            ok, s2 = self._cond(c.inner, store, tid)
            return (not ok, s2)
        if isinstance(c, A.BoolCond):
            return bool(self._eval(c.expr, store, None, tid)), store
        if isinstance(c, A.CasCond):
            expected = self._eval(c.expected, store, None, tid)
            if c.target_expr is not None:
                ref = self._eval(c.target_expr.base, store, None, tid)
                cur = self._read_field(ref, c.target, store)
                if cur == expected:
                    s2 = dict(store)
                    s2[("fld", ref[1], ref[2], c.target)] = \
                        self._eval(c.new, store, None, tid)
                    return True, s2
                return False, store
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

    if result.wrong_reachable:
        print(f"UNSAFE: some interleaving reaches `wrong` "
              f"(explored {result.states_explored} states).")
        if args.trace and result.trace:
            print("  failing interleaving:")
            for step in result.trace:
                print(f"    t{step['tid']}  {args.file}:{step['line']}  "
                      f"{step['source']}")
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
                owner = obj.get("allocated_by")
                by = f" (allocated by t{owner})" if owner is not None else ""
                parts.append(f"{obj['id']}: {obj['class']}{{{fields}}}{by}")
            print("  " + (", ".join(parts) if parts else "(empty store)"))
            if args.trace and st.get("trace"):
                print("    via:")
                for step in st["trace"]:
                    print(f"      t{step['tid']}  {args.file}:{step['line']}  "
                          f"{step['source']}")

    return 1 if result.wrong_reachable else (3 if result.hit_bound else 0)


if __name__ == "__main__":
    import sys
    sys.exit(main())
