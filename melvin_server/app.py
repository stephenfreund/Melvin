"""Melvin demo server: a small, robust FastAPI app around the verifier.

Design notes (vs. the Anchor demo this replaces as inspiration):
  * verification runs IN-PROCESS via `melvin.checker.check_source` — structured
    diagnostics, no stdout parsing; Boogie's own subprocess timeout is reused.
  * the interpreter runs in a SUBPROCESS (`python -m melvin.interp`) because it
    is CPU-bound pure Python and cannot be cancelled from a thread; the server
    kills it on timeout.  The front end (parse/type-check) is re-run in-process
    first so front-end errors come back structured, never from the subprocess.
  * bounded concurrency + queue, per-IP rate limit, source-size cap, and an
    LRU result cache.  Handlers never leak stack traces.

Run locally:   melvin-server [--reload]   (or: uvicorn melvin_server.app:app)
Configuration is via MELVIN_DEMO_* environment variables (see below).
"""

from __future__ import annotations

import asyncio
import hashlib
import json
import logging
import os
import re
import sys
import tempfile
import time
from collections import OrderedDict
from pathlib import Path
from typing import List, Optional

from fastapi import FastAPI, HTTPException, Request
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel
from starlette.concurrency import run_in_threadpool

from melvin.annotate import line_details, mover_annotations
from melvin.boogie_backend import BoogieBackend, BoogieError
from melvin.checker import check_source
from melvin.diagnostics import NO_SPAN, MelvinError
from melvin.parser import parse
from melvin.tools import examples_dir
from melvin.types import check_types

from .examples_manifest import BY_NAME, EXAMPLES, GROUPS

# --------------------------------------------------------------- configuration

REPO_ROOT = Path(__file__).resolve().parents[1]
STATIC_DIR = Path(__file__).resolve().parent / "static"
# In a checkout the examples sit at the repository root; in an installed wheel
# they ship inside the package (melvin/examples).  MELVIN_EXAMPLES_DIR wins.
EXAMPLES_DIR = examples_dir() or (REPO_ROOT / "examples")

VERIFY_TIMEOUT = int(os.environ.get("MELVIN_DEMO_VERIFY_TIMEOUT", "30"))   # s
RUN_TIMEOUT = int(os.environ.get("MELVIN_DEMO_RUN_TIMEOUT", "10"))         # s
MAX_SOURCE = int(os.environ.get("MELVIN_DEMO_MAX_SOURCE", "65536"))        # bytes
MAX_JOBS = int(os.environ.get("MELVIN_DEMO_MAX_JOBS", "2"))                # concurrent
MAX_QUEUE = int(os.environ.get("MELVIN_DEMO_MAX_QUEUE", "8"))              # waiting
MAX_STATES = int(os.environ.get("MELVIN_DEMO_MAX_STATES", "200000"))       # interp bound
RATE_PER_MINUTE = int(os.environ.get("MELVIN_DEMO_RATE", "30"))            # per IP
CACHE_SIZE = int(os.environ.get("MELVIN_DEMO_CACHE", "128"))

log = logging.getLogger("melvin.demo")
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(name)s %(message)s")

app = FastAPI(title="Melvin demo", docs_url=None, redoc_url=None, openapi_url=None)

# ------------------------------------------------------------------- plumbing

_jobs = asyncio.Semaphore(MAX_JOBS)
_waiting = 0

BUSY_MESSAGE = ("The demo server is busy right now — please try again in a few "
                "seconds, or install Melvin locally for unlimited use.")


class _JobSlot:
    """Bounded admission: at most MAX_JOBS running, MAX_QUEUE waiting."""

    async def __aenter__(self):
        global _waiting
        if _waiting >= MAX_QUEUE:
            raise HTTPException(429, BUSY_MESSAGE)
        _waiting += 1
        try:
            await _jobs.acquire()
        finally:
            _waiting -= 1

    async def __aexit__(self, *exc):
        _jobs.release()


class _RateLimiter:
    """Per-IP token bucket: RATE_PER_MINUTE requests/min, same burst size."""

    def __init__(self):
        self.buckets = {}                      # ip -> [tokens, last_ts]

    def allow(self, ip: str) -> bool:
        now = time.monotonic()
        tokens, last = self.buckets.get(ip, (float(RATE_PER_MINUTE), now))
        tokens = min(RATE_PER_MINUTE, tokens + (now - last) * RATE_PER_MINUTE / 60.0)
        if tokens < 1.0:
            self.buckets[ip] = (tokens, now)
            return False
        self.buckets[ip] = (tokens - 1.0, now)
        if len(self.buckets) > 10_000:          # drop stale entries wholesale
            self.buckets = {k: v for k, v in self.buckets.items() if v[1] > now - 300}
        return True


_rate = _RateLimiter()


def _client_ip(request: Request) -> str:
    fwd = request.headers.get("x-forwarded-for")
    if fwd:
        return fwd.split(",")[0].strip()
    return request.client.host if request.client else "unknown"


class _LRU:
    def __init__(self, size: int):
        self.size = size
        self.data: OrderedDict = OrderedDict()

    def get(self, key):
        if key in self.data:
            self.data.move_to_end(key)
            return self.data[key]
        return None

    def put(self, key, value):
        self.data[key] = value
        self.data.move_to_end(key)
        while len(self.data) > self.size:
            self.data.popitem(last=False)


_cache = _LRU(CACHE_SIZE)


def _admit(request: Request, source: str) -> None:
    """Shared request gate: rate limit + size cap (raises HTTPException)."""
    if not _rate.allow(_client_ip(request)):
        raise HTTPException(429, "Rate limit exceeded — please slow down.")
    if len(source.encode("utf-8", errors="replace")) > MAX_SOURCE:
        raise HTTPException(413, f"Program too large for the demo "
                                 f"(limit {MAX_SOURCE // 1024} KB).")


def _diag_json(d) -> dict:
    span = d.span if d.span is not None and d.span is not NO_SPAN else None
    return {
        "line": span.start.line if span else None,
        "col": span.start.col if span else None,
        "end_line": span.end.line if span else None,
        "end_col": span.end.col if span else None,
        "kind": getattr(d, "kind", "error"),
        "message": d.message,
        "model": getattr(d, "model", None),
    }


# ------------------------------------------------------------------ API: meta

@app.get("/api/health")
async def health():
    try:
        boogie = BoogieBackend._discover()
    except BoogieError:
        boogie = None
    ok = boogie is not None
    return JSONResponse(status_code=200 if ok else 503,
                        content={"ok": ok, "boogie": boogie or "not found"})


@app.get("/api/examples")
async def examples():
    return [{k: e[k] for k in ("name", "title", "blurb", "group")} for e in EXAMPLES]


@app.get("/api/example-groups")
async def example_groups():
    """The Examples menu categories, in display order."""
    return GROUPS


@app.get("/api/examples/{name}")
async def example(name: str):
    if name not in BY_NAME:                      # allowlist: no path traversal
        raise HTTPException(404, f"unknown example {name!r}")
    path = EXAMPLES_DIR / name
    try:
        return {"name": name, "source": path.read_text()}
    except OSError:
        raise HTTPException(404, f"example {name!r} is missing on the server")


# ---------------------------------------------------------------- API: verify

class SourceRequest(BaseModel):
    source: str
    counterexample: bool = False


@app.post("/api/verify")
async def verify(req: SourceRequest, request: Request):
    _admit(request, req.source)
    key = ("verify", hashlib.sha256(req.source.encode()).hexdigest(),
           bool(req.counterexample))
    cached = _cache.get(key)
    if cached is not None:
        return {**cached, "cached": True}

    t0 = time.monotonic()
    async with _JobSlot():
        try:
            result = await run_in_threadpool(
                check_source, req.source, "input.mml", timeout=VERIFY_TIMEOUT,
                counterexample=req.counterexample)
        except Exception:
            log.exception("verify: internal error (source hash %s)", key[1][:12])
            return _error_response("internal error while verifying the program")
    elapsed_ms = int((time.monotonic() - t0) * 1000)

    if result.tool_failure:
        log.error("verify: prover failure: %s", result.tool_failure[:500])
        return _error_response("the prover failed on this input")
    if result.timed_out:
        status = "timeout"
    elif result.ok:
        status = "verified"
    else:
        status = "rejected"

    payload = {
        "status": status,
        "verified": result.verified,
        "elapsed_ms": elapsed_ms,
        "diagnostics": [_diag_json(d) for d in result.diagnostics],
        "boogie": result.boogie_text,
        "movers": _movers_json(req.source),
    }
    if status in ("verified", "rejected"):       # don't cache transient outcomes
        _cache.put(key, payload)
    log.info("verify %s: %s in %dms (%d obligations)",
             key[1][:12], status, elapsed_ms, result.verified)
    return payload


def _movers_json(source: str) -> list:
    """Per-line mover records for the editor gutter: the letter, an
    explanation of why, and the schematic abstract store before the line
    ([] if the front end fails — the verify diagnostics already report why)."""
    try:
        prog = parse(source, "input.mml")
        ti = check_types(prog)
        return line_details(prog, ti, source)
    except MelvinError:
        return []


def _error_response(message: str) -> dict:
    return {
        "status": "error", "verified": 0, "elapsed_ms": 0, "boogie": "",
        "movers": [],
        "diagnostics": [{"line": None, "col": None, "end_line": None,
                         "end_col": None, "kind": "error", "message": message}],
    }


# ------------------------------------------------------------------- API: run

@app.post("/api/run")
async def run(req: SourceRequest, request: Request):
    _admit(request, req.source)
    key = ("run", hashlib.sha256(req.source.encode()).hexdigest())
    cached = _cache.get(key)
    if cached is not None:
        return {**cached, "cached": True}

    # Front end in-process: structured errors without launching a subprocess.
    try:
        prog = parse(req.source, "input.mml")
        check_types(prog)
    except MelvinError as e:
        return {"status": "error", "states": 0, "trace": None, "elapsed_ms": 0,
                "diagnostics": [_diag_json(e)]}
    if not prog.threads:
        return {"status": "error", "states": 0, "trace": None, "elapsed_ms": 0,
                "diagnostics": [{"line": None, "col": None, "end_line": None,
                                 "end_col": None, "kind": "error",
                                 "message": "no threads to run: add one or more "
                                            "`thread { ... }` declarations"}]}

    t0 = time.monotonic()
    async with _JobSlot():
        payload = await _run_interpreter(req.source)
    payload["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    if payload["status"] in ("safe", "unsafe"):
        _cache.put(key, payload)
    log.info("run %s: %s in %dms", key[1][:12], payload["status"],
             payload["elapsed_ms"])
    return payload


async def _run_interpreter(source: str) -> dict:
    """`python -m melvin.interp` in a killable subprocess (exit 0/1/2/3)."""
    with tempfile.NamedTemporaryFile("w", suffix=".mml", delete=False) as f:
        f.write(source)
        path = f.name
    try:
        proc = await asyncio.create_subprocess_exec(
            sys.executable, "-m", "melvin.interp", path,
            "--max-states", str(MAX_STATES), "--json",
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
        try:
            stdout, _ = await asyncio.wait_for(proc.communicate(), RUN_TIMEOUT)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            return {"status": "unknown", "states": None, "trace": None,
                    "message": f"the interpreter hit the demo's {RUN_TIMEOUT}s "
                               f"time limit", "diagnostics": []}
    finally:
        os.unlink(path)

    out = stdout.decode(errors="replace")
    status = {0: "safe", 1: "unsafe", 3: "unknown"}.get(proc.returncode, "error")
    try:
        data = json.loads(out)
    except ValueError:
        data = {}
    return {"status": data.get("result", status),
            "states": data.get("states"),
            "trace": data.get("trace"),
            "finals": data.get("finals"),
            "finals_complete": data.get("finals_complete", True),
            "message": data.get("message", ""), "diagnostics": []}


# ------------------------------------------------------------------ static UI

@app.get("/")
async def index():
    return FileResponse(STATIC_DIR / "index.html")


app.mount("/", StaticFiles(directory=STATIC_DIR), name="static")


# ------------------------------------------------------------------ CLI entry

def main() -> None:
    """`melvin-server`: run the demo server locally with uvicorn."""
    import argparse

    import uvicorn

    ap = argparse.ArgumentParser(
        prog="melvin-server", description="Run the Melvin web demo server.")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--reload", action="store_true",
                    help="restart on source changes (development)")
    args = ap.parse_args()
    uvicorn.run("melvin_server.app:app", host=args.host, port=args.port,
                reload=args.reload)
