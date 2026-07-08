"""Tests for the demo web server (demo/server/app.py).

The demo dependencies (fastapi, httpx) are NOT core dependencies; this module
skips itself when they are missing.  Boogie-dependent tests use the same
`needs_boogie` marker as the rest of the suite.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # for `demo.*`

fastapi = pytest.importorskip("fastapi")
pytest.importorskip("httpx")

from fastapi.testclient import TestClient

from _util import EXAMPLES, needs_boogie

from demo.server.app import app, MAX_SOURCE
from demo.server.examples_manifest import EXAMPLES as MANIFEST


@pytest.fixture(scope="module")
def client():
    with TestClient(app) as c:
        yield c


def read_example(name):
    return (EXAMPLES / name).read_text()


# ------------------------------------------------------------------ metadata

def test_health(client):
    res = client.get("/api/health")
    assert res.status_code in (200, 503)
    body = res.json()
    assert "ok" in body and "boogie" in body


def test_examples_list_matches_manifest(client):
    listed = client.get("/api/examples").json()
    assert [e["name"] for e in listed] == [e["name"] for e in MANIFEST]
    for e in listed:
        assert e["title"] and e["blurb"] and e["group"]


def test_every_manifest_example_is_served(client):
    for e in MANIFEST:
        res = client.get(f"/api/examples/{e['name']}")
        assert res.status_code == 200, e["name"]
        assert res.json()["source"] == read_example(e["name"])


def test_unknown_example_404(client):
    assert client.get("/api/examples/nope.mml").status_code == 404


def test_path_traversal_rejected(client):
    # not in the allowlist -> 404, and never read from disk
    res = client.get("/api/examples/..%2Fpyproject.toml")
    assert res.status_code == 404


def test_index_served(client):
    res = client.get("/")
    assert res.status_code == 200
    assert "Melvin" in res.text


# ------------------------------------------------- verify: no prover needed

def test_verify_front_end_error_is_structured(client):
    res = client.post("/api/verify", json={"source": "var int x ; ;;"})
    assert res.status_code == 200
    body = res.json()
    assert body["status"] == "rejected"
    d = body["diagnostics"][0]
    assert d["line"] == 1 and d["col"] is not None
    assert "expected" in d["message"]


def test_verify_source_too_large(client):
    big = "// x\n" * (MAX_SOURCE // 4)
    res = client.post("/api/verify", json={"source": big})
    assert res.status_code == 413


def test_verify_malformed_body(client):
    res = client.post("/api/verify", json={"src": "oops"})
    assert res.status_code == 422


# ------------------------------------------------------ verify: with Boogie

@needs_boogie
def test_verify_counter(client):
    res = client.post("/api/verify", json={"source": read_example("counter.mml")})
    body = res.json()
    assert body["status"] == "verified"
    assert body["verified"] == 23
    assert "procedure" in body["boogie"]


@needs_boogie
def test_verify_racy_bad_has_line_mapped_race(client):
    res = client.post("/api/verify", json={"source": read_example("racy_bad.mml")})
    body = res.json()
    assert body["status"] == "rejected"
    assert any("race" in d["message"] and d["line"] == 18
               for d in body["diagnostics"])


@needs_boogie
def test_verify_returns_mover_annotations(client):
    src = read_example("counter.mml")
    body = client.post("/api/verify", json={"source": src}).json()
    movers = {m["line"]: m["effect"] for m in body["movers"]}
    lines = src.splitlines()
    acquire_line = next(i for i, l in enumerate(lines, 1) if "acquire(m);" in l)
    release_line = next(i for i, l in enumerate(lines, 1) if "release(m);" in l)
    assert movers[acquire_line] == "R"
    assert movers[release_line] == "L"


def test_verify_front_end_error_has_no_movers(client):
    body = client.post("/api/verify", json={"source": "var int x ; ;;"}).json()
    assert body["movers"] == []


@needs_boogie
def test_verify_result_is_cached(client):
    src = read_example("counter.mml")
    client.post("/api/verify", json={"source": src})
    body = client.post("/api/verify", json={"source": src}).json()
    assert body.get("cached") is True
    assert body["status"] == "verified"


# --------------------------------------------------------- run (interpreter)

def test_run_safe(client):
    res = client.post("/api/run", json={"source": read_example("oracle_safe.mml")})
    body = res.json()
    assert body["status"] == "safe"
    assert body["states"] > 0
    assert body["trace"] is None


def test_run_unsafe_with_trace(client):
    res = client.post("/api/run", json={"source": read_example("oracle_unsafe.mml")})
    body = res.json()
    assert body["status"] == "unsafe"
    assert body["trace"]
    assert all(step["line"] > 0 and step["source"] for step in body["trace"])


def test_run_front_end_error(client):
    res = client.post("/api/run", json={"source": "thread { ; }"})
    body = res.json()
    assert body["status"] == "error"
    assert body["diagnostics"]


def test_run_no_threads(client):
    res = client.post("/api/run",
                      json={"source": "var int x both-mover if m == tid;\n"
                                      "lock m write right-mover if \\old(m)==0 && m==tid\n"
                                      "       write left-mover if \\old(m)==tid && m==0;"})
    body = res.json()
    assert body["status"] == "error"
    assert "thread" in body["diagnostics"][0]["message"]
