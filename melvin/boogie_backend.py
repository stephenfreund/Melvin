"""Boogie prover backend.

This module is the *only* place that knows about the external theorem prover.
It runs the Boogie verifier on a generated `.bpl` program and maps Boogie's
`file(line,col): Error ...` diagnostics back to the Mover Logic source using an
obligation table keyed by the line number of each emitted `assert`.

Note on "Boogie Python bindings": there is no official Python binding for the
Boogie verifier (the `boogie` package on PyPI is an unrelated Django library).
We therefore shell out to the Boogie executable.  The backend is deliberately
small and self-contained so a real binding could be dropped in behind
`BoogieBackend.verify` without touching the rest of the tool.
"""

from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import tools
from .diagnostics import Diagnostic, Span

# Default wall-clock budget for a single Boogie run: 5 minutes.
DEFAULT_TIMEOUT = 300


@dataclass
class Obligation:
    """A single verification condition, tracked so failures map back to source."""
    span: Optional[Span]
    message: str
    good_note: str = ""      # optional note printed when this obligation holds
    # Source-level variable names in scope where this obligation lives; used to
    # restrict the counterexample store to what the user can actually see
    # (e.g. the internal `result` return slot is hidden in functions that never
    # use it).  None means "no restriction".
    in_scope: Optional[frozenset] = None


@dataclass
class Emitter:
    """Accumulates Boogie source and remembers where each obligation lives.

    `assert_` emits a Boogie assertion and records the obligation at the line it
    occupies, so a Boogie error at that line can be reported against the right
    Mover Logic construct.
    """
    lines: List[str] = field(default_factory=list)
    obligations: Dict[int, Obligation] = field(default_factory=dict)
    _indent: int = 0
    # in-scope variable names stamped onto every obligation emitted while set
    # (the vcgen sets this per function body); None = no restriction.
    scope_names: Optional[frozenset] = None

    def line(self, text: str = "") -> int:
        self.lines.append(("  " * self._indent) + text if text else "")
        return len(self.lines)  # 1-based line number of what we just wrote

    def raw(self, text: str) -> int:
        self.lines.append(text)
        return len(self.lines)

    def indent(self) -> None:
        self._indent += 1

    def dedent(self) -> None:
        self._indent = max(0, self._indent - 1)

    def blank(self) -> None:
        self.lines.append("")

    def assert_(self, expr: str, span: Optional[Span], message: str, good_note: str = "") -> None:
        ln = self.line(f"assert {expr};")
        self.obligations[ln] = Obligation(span, message, good_note, self.scope_names)

    def text(self) -> str:
        return "\n".join(self.lines) + "\n"


_ERROR_RE = re.compile(r"^(?P<file>.*?)\((?P<line>\d+),(?P<col>\d+)\):\s*(?:Error|error)\b.*?:?\s*(?P<msg>.*)$")
_SUMMARY_RE = re.compile(r"(?P<verified>\d+)\s+verified,\s+(?P<errors>\d+)\s+error")

# Boogie model entries: `name -> value` (function/map entries open a `{` block).
_MODEL_ENTRY_RE = re.compile(r"^(?P<name>\S+)\s+->\s+(?P<value>.*)$")
# Opaque model values like T@List!val!0.
_OPAQUE_RE = re.compile(r"^T@(?P<type>\w+)!val!(?P<n>\d+)$")

# Effect codes (prelude.py) back to mover letters, for eff/mv model values.
_EFF_LETTER = {0: "Y", 1: "B", 2: "R", 3: "L", 4: "N", 5: "E"}


def _parse_model_block(lines: List[str]) -> Tuple[Dict[str, str], Dict[str, List]]:
    """Parse a `*** MODEL` block into (scalar entries, function graphs).
    Scalars are name -> value; each function graph is a list of
    (arg-tuple, value) rows, with its default row kept as (("else",), value)."""
    out: Dict[str, str] = {}
    funcs: Dict[str, List] = {}
    fname: Optional[str] = None
    for raw in lines:
        line = raw.strip()
        if fname is not None:
            if line == "}":
                fname = None
                continue
            # row format: `arg1 arg2 ... -> value` (or `else -> value`)
            if line.startswith("else") and "->" in line:
                funcs[fname].append((("else",),
                                     line.split("->", 1)[1].strip()))
            elif "->" in line:
                argstr, val = line.rsplit("->", 1)
                funcs[fname].append((tuple(argstr.split()), val.strip()))
            continue
        m = _MODEL_ENTRY_RE.match(line)
        if not m:
            continue
        value = m.group("value").strip()
        if value.endswith("{"):
            fname = m.group("name")
            funcs[fname] = []
            continue
        out[m.group("name")] = value
    return out, funcs


def _clean_value(v: str) -> str:
    """Normalize a Boogie model value for display."""
    v = v.strip()
    m = re.match(r"^\(-\s*(\d+)\)$", v)
    if m:
        return f"-{m.group(1)}"
    m = _OPAQUE_RE.match(v)
    if m:
        return f"{m.group('type')}#{m.group('n')}"
    return v


def _last_incarnation(raw: Dict[str, str], base: str) -> Optional[str]:
    """Boogie models list SSA incarnations (`v_x`, `v_x@0`, `v_x@1`, ...);
    the highest incarnation is the value at the end of the failing path."""
    best_k, best = -1, None
    for name, value in raw.items():
        stem, _, idx = name.partition("@")
        if stem != base:
            continue
        k = int(idx) if idx.isdigit() else -0.5  # bare name = initial value
        if best is None or k >= best_k:
            best_k, best = k, value
    return best


def model_table(raw: Dict[str, str], funcs: Optional[Dict[str, List]] = None,
                class_fields: Optional[Dict[str, Dict]] = None,
                in_scope: Optional[frozenset] = None) -> List[Tuple[str, str]]:
    """Map a raw Boogie model to source-level rows for the failing procedure:
    tid, the running effect as a mover letter, each store variable's current
    value (and its `\\old` value when the model constrains it and it differs),
    and -- via the model's Select_ graphs -- the known field values of heap
    objects, as `C#k.f` rows.

    If `in_scope` is given, plain (non-heap) store variables are shown only when
    their source name is in that set, so internal slots that leak into a
    procedure's encoding (notably the `result` return channel of a callee) are
    hidden in functions that do not actually use them.  In-scope variables the
    model does not constrain at all (Boogie prunes SSA incarnations irrelevant
    to the failing path) are listed with the value `?` so the omission is
    explicit rather than silent."""
    funcs = funcs or {}
    class_fields = class_fields or {}
    rows: List[Tuple[str, str]] = []
    tid = _last_incarnation(raw, "tid")
    if tid is not None:
        rows.append(("tid", _clean_value(tid)))
    eff = _last_incarnation(raw, "eff")
    if eff is not None and _clean_value(eff).lstrip("-").isdigit():
        code = int(_clean_value(eff))
        rows.append(("eff", _EFF_LETTER.get(code, str(code))))

    # index all two-argument Select_ rows: (map value, index value) -> value,
    # and each Select_ graph's default (`else`) row when it is a plain value
    # (in a first-order model the default IS the value of every unlisted
    # lookup, so it fills in fields the failing path never pinned down)
    select: Dict[Tuple[str, str], str] = {}
    elses: Dict[str, str] = {}
    for name, frows in funcs.items():
        if name.startswith("Select_"):
            for args, val in frows:
                if len(args) == 2:
                    select[(args[0].strip("|"), args[1].strip("|"))] = val
                elif args == ("else",) and not val.lstrip().startswith("("):
                    elses[name] = val

    # `null_<T> -> val` entries identify each type's null reference: such a
    # value displays as `null`, and heap rows keyed at a null address are
    # dropped (they describe no allocated object).
    nulls = {v.strip() for n, v in raw.items() if n.startswith("null_")}

    # every non-null object reference we display, so the full object graph
    # can be synthesized afterwards: "C#k" -> (type name, raw model value)
    seen_objs: Dict[str, Tuple[str, str]] = {}

    def clean(v: str) -> str:
        v = v.strip().strip("|")
        if v in nulls:
            return "null"
        m = _OPAQUE_RE.match(v)
        if m and (m.group("type") in class_fields
                  or m.group("type").startswith("Arr_")):
            disp = f"{m.group('type')}#{m.group('n')}"
            seen_objs[disp] = (m.group("type"), v)
        return _clean_value(v)

    def heap_rows(var: str, base: str) -> List[Tuple[str, str]]:
        """Decode a field-map variable f_<C>_<fld> into per-object rows."""
        for cname in sorted(class_fields, key=len, reverse=True):
            if var.startswith(f"f_{cname}_"):
                fld = var[len(f"f_{cname}_"):]
                mapval = _last_incarnation(raw, base)
                if mapval is None:
                    return []
                mapval = mapval.strip("|")
                out = []
                for (m, o), val in sorted(select.items()):
                    if m == mapval and o not in nulls:
                        out.append((f"{clean(o)}.{fld}", clean(val)))
                return out
        return []

    def _idx_key(i: str):
        i = _clean_value(i)
        return (0, int(i)) if i.lstrip("-").isdigit() else (1, i)

    def array_rows(var: str, base: str) -> List[Tuple[str, str]]:
        """Decode the array heap maps: `elems_<C>_<fld>` ([at][int]T) via a
        two-level Select_ lookup into `at#k[i]` element rows, and
        `len_<C>_<fld>` ([at]int) into `at#k.length` rows."""
        mapval = _last_incarnation(raw, base)
        if mapval is None:
            return []
        mapval = mapval.strip("|")
        out: List[Tuple[str, str]] = []
        if var.startswith("len_"):
            for (m, a), val in sorted(select.items()):
                if m == mapval and a not in nulls:
                    out.append((f"{clean(a)}.length", clean(val)))
            return out
        # elems: the outer graph yields each array's inner [int]T map value,
        # the inner graph that map's per-index elements.
        for (m, a), inner in sorted(select.items()):
            if m != mapval or a in nulls:
                continue
            inner = inner.strip("|")
            elems = [(i, val) for (m2, i), val in select.items() if m2 == inner]
            for i, val in sorted(elems, key=lambda e: _idx_key(e[0])):
                out.append((f"{clean(a)}[{_clean_value(i)}]", clean(val)))
        return out

    bases = sorted({name.partition("@")[0] for name in raw})
    shown = set()
    for base in bases:
        if not base.startswith("v_"):
            continue
        var = base[2:]
        if var.startswith(("elems_", "len_")):
            rows.extend(array_rows(var, base))
            continue
        if var.startswith(("f_", "alloc_")):
            rows.extend(heap_rows(var, base))
            continue
        if in_scope is not None and var not in in_scope:
            continue                       # out-of-scope internal slot (e.g. result)
        cur = _last_incarnation(raw, base)
        if cur is not None:
            rows.append((var, clean(cur)))
            shown.add(var)
        old = _last_incarnation(raw, f"o_{var}")
        if old is not None and old != cur:
            rows.append((f"\\old({var})", clean(old)))

    # Every referenced object gets its FULL field list, so the diagram shows
    # the whole object graph: a field the failing path never pinned down is
    # read from its Select_ graph's default row, or shown as `?`.  clean()
    # can discover new references while synthesizing, so iterate to fixpoint.
    def field_lookup(cname: str, fld: str, fty: str, rawref: str,
                     graph_prefix: str = "f") -> Optional[str]:
        base = (f"v_{graph_prefix}_{cname}_{fld}" if graph_prefix == "f"
                else f"v_len_{cname[4:]}")
        mapval = _last_incarnation(raw, base)
        if mapval is not None:
            val = select.get((mapval.strip("|"), rawref))
            if val is not None:
                return val
        token = {"int": "$int", "bool": "$bool"}.get(fty, fty)
        return elses.get(f"Select_[{cname}]{token}")

    while True:
        have = {n for n, _v in rows}
        added = []
        for disp in sorted(seen_objs):
            cname, rawref = seen_objs[disp]
            if cname in class_fields:
                for fld, fty in sorted(class_fields[cname].items()):
                    if f"{disp}.{fld}" not in have:
                        val = field_lookup(cname, fld, fty, rawref)
                        added.append((f"{disp}.{fld}",
                                      clean(val) if val is not None else "?"))
            elif cname.startswith("Arr_"):
                if not any(n.startswith(disp) for n in have):
                    val = field_lookup(cname, "length", "int", rawref, "len")
                    added.append((f"{disp}.length",
                                  clean(val) if val is not None else "?"))
        if not added:
            break
        rows.extend(added)

    if in_scope is not None:
        for var in sorted(set(in_scope) - shown):
            rows.append((var, "?"))
    return rows


class BoogieError(RuntimeError):
    pass


class BoogieBackend:
    def __init__(self, boogie_path: Optional[str] = None, extra_args: Optional[List[str]] = None):
        self.boogie_path = boogie_path or self._discover()
        self.extra_args = extra_args or []

    @staticmethod
    def _discover() -> str:
        """Locate Boogie (MELVIN_BOOGIE, PATH, then Melvin's tools directory)."""
        found = tools.find_boogie()
        if found:
            return found
        raise BoogieError(
            "could not find the Boogie executable; run `melvin-install-boogie` "
            "(or set MELVIN_BOOGIE to the path of an existing install)"
        )

    def _prover_args(self) -> List[str]:
        """Tell Boogie where Z3 is when it is not on PATH.

        `pip install melvin[z3]` drops the `z3` binary in the interpreter's
        script directory, which need not be on PATH (pipx, uv tool, an
        unactivated venv).  Boogie only searches PATH, so hand it the path.
        """
        if tools.z3_on_path():
            return []
        z3 = tools.find_z3()
        return [f"/proverOpt:PROVER_PATH={z3}"] if z3 else []

    def run_raw(self, bpl_path: str, timeout: int = 120,
                extra: Optional[List[str]] = None) -> subprocess.CompletedProcess:
        cmd = [self.boogie_path, *self.extra_args, *self._prover_args(),
               *(extra or []), bpl_path]
        try:
            return subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout
            )
        except FileNotFoundError as e:  # pragma: no cover
            raise BoogieError(f"failed to launch Boogie ({self.boogie_path}): {e}")

    def verify(
        self,
        emitter: Emitter,
        bpl_path: str,
        timeout: int = DEFAULT_TIMEOUT,
        want_model: bool = False,
        class_fields: Optional[Dict[str, Dict]] = None,
    ) -> "VerifyResult":
        """Write the emitter's program to `bpl_path`, run Boogie, map results.

        With `want_model`, Boogie prints a counterexample model per error;
        each is parsed and attached to its diagnostic as source-level rows
        (unparseable models degrade to no counterexample, never a failure).

        If Boogie does not finish within `timeout` seconds it is killed and a
        result with `timed_out=True` (and `ok=False`) is returned rather than
        propagating the exception.
        """
        with open(bpl_path, "w") as f:
            f.write(emitter.text())
        try:
            proc = self.run_raw(bpl_path, timeout=timeout,
                                extra=["/printModel:1"] if want_model else None)
        except subprocess.TimeoutExpired as e:
            partial = ""
            if e.stdout:
                partial = e.stdout if isinstance(e.stdout, str) else e.stdout.decode(errors="replace")
            return VerifyResult(
                ok=False,
                diagnostics=[Diagnostic(
                    None,
                    f"verification timed out after {timeout}s "
                    f"(raise the limit with --timeout)")],
                verified=0,
                n_errors=0,
                raw_output=partial,
                timed_out=True,
            )
        return self._interpret(proc, emitter, bpl_path, class_fields)

    def _interpret(self, proc, emitter: Emitter, bpl_path: str,
                   class_fields: Optional[Dict[str, Dict]] = None) -> "VerifyResult":
        out = (proc.stdout or "") + "\n" + (proc.stderr or "")
        diagnostics: List[Diagnostic] = []
        n_errors = 0
        verified = None
        seen_lines = set()
        base = os.path.basename(bpl_path)
        # Where a counterexample model sits relative to the error it explains
        # depends on the Boogie version: 2.x prints the model first, 3.x prints
        # it after.  Both are handled -- a model block is attached to the error
        # just reported when that one has none yet, and otherwise held for the
        # next error.  Decoding is deferred until the error, and hence the
        # obligation's in-scope names, is known.
        pending_data: Optional[Tuple[Dict[str, str], Dict[str, List]]] = None
        model_lines: Optional[List[str]] = None
        last_diag: Optional[Diagnostic] = None
        last_oblig: Optional[Obligation] = None

        def decode(data, oblig: Optional[Obligation]) -> Optional[List[Tuple[str, str]]]:
            if data is None:
                return None
            try:
                in_scope = oblig.in_scope if oblig is not None else None
                return model_table(data[0], data[1], class_fields, in_scope)
            except Exception:                # malformed model: no cex, no crash
                return None

        for raw in out.splitlines():
            stripped = raw.strip()
            if stripped == "*** MODEL":
                model_lines = []
                continue
            if stripped == "*** END_MODEL":
                data = None
                if model_lines is not None:
                    try:
                        data = _parse_model_block(model_lines)
                    except Exception:
                        data = None
                model_lines = None
                if data is not None and last_diag is not None and last_diag.model is None:
                    last_diag.model = decode(data, last_oblig)   # Boogie 3.x order
                else:
                    pending_data = data                          # Boogie 2.x order
                continue
            if model_lines is not None:
                model_lines.append(raw)
                continue
            m = _SUMMARY_RE.search(raw)
            if m:
                verified = int(m.group("verified"))
                continue
            m = _ERROR_RE.match(stripped)
            if m and (base in m.group("file") or m.group("file").endswith(".bpl")):
                bline = int(m.group("line"))
                if bline in seen_lines:
                    continue
                seen_lines.add(bline)
                oblig = self._nearest_obligation(emitter, bline)
                if oblig is not None:
                    diag = Diagnostic(oblig.span, oblig.message,
                                      model=decode(pending_data, oblig))
                else:
                    diag = Diagnostic(
                        None, f"Boogie error at {base}({bline}): {m.group('msg')}",
                        model=decode(pending_data, None))
                diagnostics.append(diag)
                pending_data = None
                last_diag, last_oblig = diag, oblig
                n_errors += 1

        # Detect Boogie parse/type errors (no summary line, unexpected output).
        tool_failure = None
        if verified is None and "error" in out.lower() and not diagnostics:
            tool_failure = out.strip()

        return VerifyResult(
            ok=(n_errors == 0 and tool_failure is None),
            diagnostics=diagnostics,
            verified=verified or 0,
            n_errors=n_errors,
            raw_output=out,
            tool_failure=tool_failure,
            timed_out=False,
        )

    @staticmethod
    def _nearest_obligation(emitter: Emitter, bline: int) -> Optional[Obligation]:
        if bline in emitter.obligations:
            return emitter.obligations[bline]
        # Boogie sometimes reports the enclosing block line; take the nearest
        # obligation at or before the reported line.
        best = None
        for ln in sorted(emitter.obligations):
            if ln <= bline:
                best = emitter.obligations[ln]
            else:
                break
        return best


@dataclass
class VerifyResult:
    ok: bool
    diagnostics: List[Diagnostic]
    verified: int
    n_errors: int
    raw_output: str
    tool_failure: Optional[str] = None
    timed_out: bool = False
