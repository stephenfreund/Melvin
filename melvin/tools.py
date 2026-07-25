"""Locating (and installing) the external toolchain: Boogie and Z3.

Melvin itself is pure-stdlib Python, but it discharges its proof obligations
with the **Boogie** verifier, which in turn needs **Z3**.  Neither is a Python
package, so this module is the one place that knows how to find them and how
to bootstrap a working install:

* **Z3** ships as a real PyPI wheel (`z3-solver`), so `pip install melvin-verifier[z3]`
  is enough — :func:`find_z3` also looks inside the interpreter's script
  directory, which is where that wheel puts the `z3` binary.
* **Boogie** is a .NET tool with no PyPI distribution.  `melvin-install-boogie`
  installs it with `dotnet tool install --tool-path ~/.melvin/tools boogie`,
  a private location that needs no `PATH` surgery: :func:`find_boogie` looks
  there.  If .NET is missing, the command says exactly what to install.

Search order (both tools): the `MELVIN_BOOGIE` / `MELVIN_Z3` environment
variable, then `PATH`, then Melvin's own tools directory, then the .NET global
tools directory (`~/.dotnet/tools`).
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import sysconfig
from pathlib import Path
from typing import List, Optional

# Where `melvin-install-boogie` puts things.  Overridable so CI (and the Docker
# image) can install into a shared location.
MELVIN_HOME = Path(os.environ.get("MELVIN_HOME", Path.home() / ".melvin"))
TOOLS_DIR = Path(os.environ.get("MELVIN_TOOLS_DIR", MELVIN_HOME / "tools"))

# NuGet package id; a version can be pinned with MELVIN_BOOGIE_VERSION.
BOOGIE_PACKAGE = "Boogie"

# Development convenience: a Boogie built as part of an Anchor / Synchronicity
# workspace checked out beside this repository.
LEGACY_BOOGIE_PATHS = [
    Path.home() / "other/Synchronicity/workspace/Synchronicity/boogie/Binaries/boogie",
]

_WINDOWS = os.name == "nt"


def _exe(name: str) -> str:
    return f"{name}.exe" if _WINDOWS else name


def _script_dirs() -> List[Path]:
    """Directories where a pip-installed console script / binary can land.

    `z3-solver` installs its `z3` executable here, which may not be on `PATH`
    when Melvin was installed with pipx/uv or into a non-activated venv.
    """
    dirs = []
    for key in ("scripts", "purelib"):
        try:
            p = sysconfig.get_path(key)
        except (KeyError, OSError):  # pragma: no cover - exotic layouts
            continue
        if p:
            dirs.append(Path(p))
    dirs.append(Path(sys.prefix) / ("Scripts" if _WINDOWS else "bin"))
    dirs.append(Path(sys.executable).resolve().parent)
    return dirs


def _dotnet_tool_dirs() -> List[Path]:
    dirs = [TOOLS_DIR, Path.home() / ".dotnet" / "tools"]
    root = os.environ.get("DOTNET_ROOT")
    if root:
        dirs.append(Path(root) / "tools")
    return dirs


def _first_existing(paths) -> Optional[str]:
    for p in paths:
        p = Path(p)
        if p.is_file() and (_WINDOWS or os.access(p, os.X_OK)):
            return str(p)
    return None


def find_boogie() -> Optional[str]:
    """Full path to the Boogie executable, or None if it cannot be found."""
    env = os.environ.get("MELVIN_BOOGIE")
    if env and Path(env).exists():
        return env
    for cand in ("boogie", "Boogie"):
        found = shutil.which(cand)
        if found:
            return found
    found = _first_existing(d / _exe(n)
                            for d in _dotnet_tool_dirs() for n in ("boogie", "Boogie"))
    if found:
        return found
    # Last resort: the Boogie bundled with an Anchor / Synchronicity checkout
    # sitting next to this one (how Melvin's own development machines are set up).
    return _first_existing(LEGACY_BOOGIE_PATHS)


def find_z3() -> Optional[str]:
    """Full path to a Z3 executable, or None.

    Boogie finds Z3 on `PATH` by itself; this is for the case where Z3 came
    from the `z3-solver` wheel and lives in a script directory that is not on
    `PATH`.  :class:`melvin.boogie_backend.BoogieBackend` then passes it to
    Boogie explicitly with `/proverOpt:PROVER_PATH=`.
    """
    env = os.environ.get("MELVIN_Z3")
    if env and Path(env).exists():
        return env
    found = shutil.which("z3")
    if found:
        return found
    cands = []
    for d in _script_dirs():
        cands.append(d / _exe("z3"))
        cands.append(d / "z3" / "bin" / _exe("z3"))   # z3-solver's own package dir
    cands.extend(d / _exe("z3") for d in _dotnet_tool_dirs())
    return _first_existing(cands)


def z3_on_path() -> bool:
    """True when Boogie will find Z3 on its own (no PROVER_PATH needed)."""
    return shutil.which("z3") is not None


def examples_dir() -> Optional[Path]:
    """Directory holding the bundled `.mml` examples, or None.

    Wheels ship them inside the package (`melvin/examples`); a source checkout
    keeps them at the repository root.
    """
    override = os.environ.get("MELVIN_EXAMPLES_DIR")
    if override and Path(override).is_dir():
        return Path(override)
    here = Path(__file__).resolve().parent
    for cand in (here / "examples", here.parent / "examples"):
        if cand.is_dir() and any(cand.glob("*.mml")):
            return cand
    return None


# --------------------------------------------------------------- installation

class InstallError(RuntimeError):
    pass


DOTNET_HELP = """\
Boogie is a .NET tool and has no PyPI distribution, so installing it needs the
.NET SDK (which provides `dotnet`):

  macOS       brew install dotnet-sdk
  Debian      apt-get install -y dotnet-sdk-8.0
  Windows     winget install Microsoft.DotNet.SDK.8
  any OS      https://dotnet.microsoft.com/download

Then re-run `melvin-install-boogie`.  Alternatively, install Boogie however you
like and point Melvin at it:  export MELVIN_BOOGIE=/path/to/boogie
"""


def install_boogie(version: Optional[str] = None,
                   tools_dir: Optional[Path] = None) -> str:
    """Install Boogie as a .NET tool under `tools_dir`; return its path."""
    tools_dir = Path(tools_dir or TOOLS_DIR)
    dotnet = shutil.which("dotnet")
    if not dotnet:
        raise InstallError("could not find `dotnet` on PATH.\n\n" + DOTNET_HELP)
    tools_dir.mkdir(parents=True, exist_ok=True)
    cmd = [dotnet, "tool", "install", "--tool-path", str(tools_dir), BOOGIE_PACKAGE]
    version = version or os.environ.get("MELVIN_BOOGIE_VERSION")
    if version:
        cmd += ["--version", version]
    print("+ " + " ".join(cmd))
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        output = (proc.stdout or "") + (proc.stderr or "")
        already = "already installed" in output
        if not already:
            hint = ""
            # NU1202: the installed SDK is older than the framework Boogie targets.
            if "NU1202" in output or "is not compatible with" in output:
                sdk = _version_of(dotnet, ["--version"])
                hint = (f"\nYour .NET SDK ({sdk}) is too old for the current Boogie. "
                        "Install .NET 8 or newer,\nor pick a Boogie that matches your "
                        "SDK, e.g.:\n  melvin-install-boogie --version 2.16.5\n")
            raise InstallError(
                "`dotnet tool install` failed:\n" + output + hint
                + "\nTo upgrade an existing install, run:\n"
                f"  dotnet tool update --tool-path {tools_dir} {BOOGIE_PACKAGE}"
            )
        print(proc.stdout.strip())
    else:
        print(proc.stdout.strip())
    path = _first_existing(tools_dir / _exe(n) for n in ("boogie", "Boogie"))
    if not path:
        raise InstallError(f"Boogie was installed but no executable appeared in {tools_dir}")
    return path


def _version_of(exe: str, args: List[str]) -> str:
    try:
        out = subprocess.run([exe, *args], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):  # pragma: no cover - defensive
        return "?"
    text = (out.stdout or out.stderr or "").strip().splitlines()
    return text[0] if text else "?"


def doctor(stream=None) -> bool:
    """Report the state of the toolchain; True when Melvin can verify."""
    out = stream or sys.stdout
    from . import __version__

    boogie = find_boogie()
    z3 = find_z3()
    print(f"melvin {__version__}  (python {sys.version.split()[0]})", file=out)
    if boogie:
        print(f"  boogie : {boogie}\n           {_version_of(boogie, ['/version'])}", file=out)
    else:
        print("  boogie : NOT FOUND — run `melvin-install-boogie`", file=out)
    if z3:
        note = "" if z3_on_path() else "  (not on PATH; passed to Boogie explicitly)"
        print(f"  z3     : {z3}{note}\n           {_version_of(z3, ['--version'])}", file=out)
    else:
        print("  z3     : NOT FOUND — `pip install melvin-verifier[z3]`, or install Z3 "
              "and put it on PATH", file=out)
    ex = examples_dir()
    print(f"  examples: {ex if ex else 'not bundled'}", file=out)
    return bool(boogie and z3)


def main(argv=None) -> int:
    """Entry point for `melvin-install-boogie`."""
    import argparse

    ap = argparse.ArgumentParser(
        prog="melvin-install-boogie",
        description="Install the Boogie verifier (a .NET tool) for Melvin, "
                    "or report on the current toolchain.",
    )
    ap.add_argument("--check", action="store_true",
                    help="only report what is installed; do not install anything")
    ap.add_argument("--version", metavar="V",
                    help="Boogie NuGet version to install (default: latest)")
    ap.add_argument("--tools-dir", metavar="DIR", default=str(TOOLS_DIR),
                    help=f"where to install Boogie (default: {TOOLS_DIR})")
    ap.add_argument("--force", action="store_true",
                    help="install even if a Boogie executable is already visible")
    args = ap.parse_args(argv)

    if args.check:
        return 0 if doctor() else 1

    existing = find_boogie()
    if existing and not args.force:
        print(f"Boogie already available: {existing}")
    else:
        try:
            path = install_boogie(args.version, Path(args.tools_dir))
        except InstallError as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
        print(f"Boogie installed: {path}")
    print()
    ok = doctor()
    if not ok:
        print("\nMelvin cannot verify yet — see the NOT FOUND line(s) above.",
              file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
