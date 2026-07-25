"""Toolchain discovery and the `melvin-install-boogie` entry point."""

import io
import subprocess
from pathlib import Path

import pytest

from melvin import tools


def _fake_exe(path: Path) -> Path:
    path.write_text("#!/bin/sh\nexit 0\n")
    path.chmod(0o755)
    return path


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    for var in ("MELVIN_BOOGIE", "MELVIN_Z3", "MELVIN_EXAMPLES_DIR",
                "MELVIN_BOOGIE_VERSION"):
        monkeypatch.delenv(var, raising=False)


# ------------------------------------------------------------------ discovery

def test_find_boogie_prefers_env(monkeypatch, tmp_path):
    exe = _fake_exe(tmp_path / "boogie")
    monkeypatch.setenv("MELVIN_BOOGIE", str(exe))
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/boogie")
    assert tools.find_boogie() == str(exe)


def test_find_boogie_uses_path(monkeypatch):
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/boogie"
                        if name == "boogie" else None)
    assert tools.find_boogie() == "/usr/bin/boogie"


def test_find_boogie_uses_tools_dir(monkeypatch, tmp_path):
    """What `melvin-install-boogie` installs is found without touching PATH."""
    exe = _fake_exe(tmp_path / "boogie")
    monkeypatch.setattr("shutil.which", lambda name: None)
    monkeypatch.setattr(tools, "_dotnet_tool_dirs", lambda: [tmp_path])
    monkeypatch.setattr(tools, "LEGACY_BOOGIE_PATHS", [])
    assert tools.find_boogie() == str(exe)


def test_find_boogie_missing(monkeypatch, tmp_path):
    monkeypatch.setattr("shutil.which", lambda name: None)
    monkeypatch.setattr(tools, "_dotnet_tool_dirs", lambda: [tmp_path])
    monkeypatch.setattr(tools, "LEGACY_BOOGIE_PATHS", [])
    assert tools.find_boogie() is None


def test_find_z3_in_script_dir(monkeypatch, tmp_path):
    """The z3-solver wheel drops `z3` in a script dir that may not be on PATH."""
    exe = _fake_exe(tmp_path / "z3")
    monkeypatch.setattr("shutil.which", lambda name: None)
    monkeypatch.setattr(tools, "_script_dirs", lambda: [tmp_path])
    monkeypatch.setattr(tools, "_dotnet_tool_dirs", lambda: [])
    assert tools.find_z3() == str(exe)
    assert tools.z3_on_path() is False


def test_find_z3_env_override(monkeypatch, tmp_path):
    exe = _fake_exe(tmp_path / "z3")
    monkeypatch.setenv("MELVIN_Z3", str(exe))
    assert tools.find_z3() == str(exe)


def test_examples_dir_finds_bundled_examples():
    d = tools.examples_dir()
    assert d is not None and (d / "counter.mml").is_file()


def test_examples_dir_env_override(monkeypatch, tmp_path):
    monkeypatch.setenv("MELVIN_EXAMPLES_DIR", str(tmp_path))
    assert tools.examples_dir() == tmp_path


# --------------------------------------------------------------- installation

def test_install_boogie_without_dotnet(monkeypatch):
    monkeypatch.setattr("shutil.which", lambda name: None)
    with pytest.raises(tools.InstallError) as e:
        tools.install_boogie()
    assert "dotnet" in str(e.value)


def test_install_boogie_invokes_dotnet(monkeypatch, tmp_path):
    calls = []

    def fake_run(cmd, **kw):
        calls.append(cmd)
        _fake_exe(Path(cmd[cmd.index("--tool-path") + 1]) / "boogie")
        return subprocess.CompletedProcess(cmd, 0, "installed", "")

    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/dotnet")
    monkeypatch.setattr(subprocess, "run", fake_run)
    path = tools.install_boogie(version="3.4.3", tools_dir=tmp_path)
    assert path == str(tmp_path / "boogie")
    assert calls[0][:4] == ["/usr/bin/dotnet", "tool", "install", "--tool-path"]
    assert calls[0][-3:] == [tools.BOOGIE_PACKAGE, "--version", "3.4.3"]


def test_install_boogie_reports_dotnet_failure(monkeypatch, tmp_path):
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/dotnet")
    monkeypatch.setattr(
        subprocess, "run",
        lambda cmd, **kw: subprocess.CompletedProcess(cmd, 1, "", "boom"))
    with pytest.raises(tools.InstallError) as e:
        tools.install_boogie(tools_dir=tmp_path)
    assert "boom" in str(e.value) and "dotnet tool update" in str(e.value)


def test_install_boogie_tolerates_already_installed(monkeypatch, tmp_path):
    _fake_exe(tmp_path / "boogie")
    monkeypatch.setattr("shutil.which", lambda name: "/usr/bin/dotnet")
    monkeypatch.setattr(
        subprocess, "run",
        lambda cmd, **kw: subprocess.CompletedProcess(cmd, 1, "already installed", ""))
    assert tools.install_boogie(tools_dir=tmp_path) == str(tmp_path / "boogie")


# ---------------------------------------------------------------- doctor / CLI

def test_doctor_reports_missing_tools(monkeypatch):
    monkeypatch.setattr(tools, "find_boogie", lambda: None)
    monkeypatch.setattr(tools, "find_z3", lambda: None)
    out = io.StringIO()
    assert tools.doctor(out) is False
    assert "melvin-install-boogie" in out.getvalue()
    assert "melvin-verifier[z3]" in out.getvalue()


def test_doctor_reports_found_tools(monkeypatch, tmp_path):
    monkeypatch.setattr(tools, "find_boogie", lambda: str(tmp_path / "boogie"))
    monkeypatch.setattr(tools, "find_z3", lambda: str(tmp_path / "z3"))
    monkeypatch.setattr(tools, "z3_on_path", lambda: False)
    monkeypatch.setattr(tools, "_version_of", lambda exe, args: "v1")
    out = io.StringIO()
    assert tools.doctor(out) is True
    assert "not on PATH" in out.getvalue()


def test_main_check_only(monkeypatch, capsys):
    monkeypatch.setattr(tools, "doctor", lambda *a: True)
    assert tools.main(["--check"]) == 0
    monkeypatch.setattr(tools, "doctor", lambda *a: False)
    assert tools.main(["--check"]) == 1


def test_main_skips_install_when_already_present(monkeypatch, capsys):
    monkeypatch.setattr(tools, "find_boogie", lambda: "/usr/bin/boogie")
    monkeypatch.setattr(tools, "doctor", lambda *a: True)
    monkeypatch.setattr(tools, "install_boogie",
                        lambda *a, **k: pytest.fail("should not install"))
    assert tools.main([]) == 0
    assert "already available" in capsys.readouterr().out


def test_main_installs_and_reports_error(monkeypatch, capsys):
    monkeypatch.setattr(tools, "find_boogie", lambda: None)

    def boom(*a, **k):
        raise tools.InstallError("no dotnet")

    monkeypatch.setattr(tools, "install_boogie", boom)
    assert tools.main([]) == 1
    assert "no dotnet" in capsys.readouterr().err
