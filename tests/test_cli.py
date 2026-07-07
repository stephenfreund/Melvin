"""Unit tests for melvin.cli (argument handling + exit codes).

These mock the checker so they run without a Boogie install.
"""

import pytest

from melvin import cli
from melvin.checker import CheckResult
from melvin.boogie_backend import DEFAULT_TIMEOUT


@pytest.fixture
def fake_check(monkeypatch):
    calls = []

    def make(result):
        def _check(path, **kwargs):
            calls.append((path, kwargs))
            return result
        monkeypatch.setattr(cli, "check_program", _check)
        return calls
    return make


def test_exit_ok(fake_check, capsys):
    fake_check(CheckResult(ok=True, verified=3))
    assert cli.main(["a.mml"]) == cli.EXIT_OK
    assert "verified (3" in capsys.readouterr().out


def test_exit_failed(fake_check, capsys):
    fake_check(CheckResult(ok=False, diagnostics=[]))
    assert cli.main(["a.mml"]) == cli.EXIT_FAILED


def test_exit_timeout(fake_check):
    fake_check(CheckResult(ok=False, timed_out=True))
    assert cli.main(["a.mml"]) == cli.EXIT_TIMEOUT


def test_default_timeout_passed_through(fake_check):
    calls = fake_check(CheckResult(ok=True))
    cli.main(["a.mml"])
    assert calls[0][1]["timeout"] == DEFAULT_TIMEOUT


def test_custom_timeout(fake_check):
    calls = fake_check(CheckResult(ok=True))
    cli.main(["--timeout", "42", "a.mml"])
    assert calls[0][1]["timeout"] == 42


def test_nonpositive_timeout_errors(fake_check):
    fake_check(CheckResult(ok=True))
    with pytest.raises(SystemExit):
        cli.main(["--timeout", "0", "a.mml"])


def test_multiple_files_aggregate_status(fake_check):
    # if any file fails, overall status is failure
    results = iter([CheckResult(ok=True), CheckResult(ok=False)])
    calls = []

    import melvin.cli as m

    def _check(path, **kwargs):
        calls.append(path)
        return next(results)
    m.check_program = _check
    assert cli.main(["a.mml", "b.mml"]) == cli.EXIT_FAILED
    assert calls == ["a.mml", "b.mml"]


def test_emit_bpl_only_first_file(fake_check):
    calls = fake_check(CheckResult(ok=True))
    cli.main(["--emit-bpl", "out.bpl", "a.mml", "b.mml"])
    assert calls[0][1]["keep_bpl"] == "out.bpl"
    assert calls[1][1]["keep_bpl"] is None


def test_show_bpl_prints_generated_program(fake_check, capsys):
    fake_check(CheckResult(ok=True, boogie_text="// BOOGIE HERE"))
    cli.main(["--show-bpl", "a.mml"])
    assert "// BOOGIE HERE" in capsys.readouterr().out


def test_show_movers_prints_annotated_listing(fake_check, capsys, tmp_path):
    from _util import EXAMPLES
    f = tmp_path / "counter.mml"
    f.write_text((EXAMPLES / "counter.mml").read_text())
    fake_check(CheckResult(ok=True, verified=23))
    cli.main(["--show-movers", str(f)])
    out = capsys.readouterr().out
    assert f"== {f} (movers) ==" in out
    assert " R |   acquire(m);" in out
    assert " L |   release(m);" in out
    assert " Y |   yield;" in out


def test_show_movers_missing_file_stays_quiet(fake_check, capsys):
    # the listing is best-effort; the verification pass reports the error
    fake_check(CheckResult(ok=False, diagnostics=[]))
    assert cli.main(["--show-movers", "no_such.mml"]) == cli.EXIT_FAILED
    assert "(movers)" not in capsys.readouterr().out


def test_main_module_entrypoint(monkeypatch):
    import runpy
    import sys
    monkeypatch.setattr(sys, "argv", ["melvin"])   # no files -> argparse exit
    with pytest.raises(SystemExit):
        runpy.run_module("melvin.__main__", run_name="__main__")
