"""Command-line interface: `python -m melvin file.mml [...]`."""

from __future__ import annotations

import argparse
import sys

from .annotate import mover_annotations, render_listing
from .boogie_backend import DEFAULT_TIMEOUT
from .checker import check_program
from .diagnostics import MelvinError
from .parser import parse
from .types import check_types

# Distinct exit codes so scripts can tell a real refutation from a timeout.
EXIT_OK = 0
EXIT_FAILED = 1
EXIT_TIMEOUT = 2


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="melvin",
        description="Verify Mover Logic Language (.mll) programs using Boogie.",
    )
    ap.add_argument("files", nargs="+", help="MLL source files to verify")
    ap.add_argument("--boogie", help="path to the Boogie executable")
    ap.add_argument("--emit-bpl", metavar="PATH",
                    help="write the generated Boogie program to PATH (for the "
                         "first input file) and keep it")
    ap.add_argument("--show-bpl", action="store_true",
                    help="print the generated Boogie program")
    ap.add_argument("--show-movers", action="store_true",
                    help="print the program with a mover-annotation margin "
                         "(R/B/L/N per statement, Y at yields) before verifying")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, metavar="SECONDS",
                    help="per-file Boogie verification timeout in seconds "
                         f"(default: {DEFAULT_TIMEOUT} = 5 minutes). On timeout the "
                         "file fails with exit code 2.")
    ap.add_argument("--counterexample", action="store_true",
                    help="on verification failure, show a source-level "
                         "counterexample store (from the Boogie model) under "
                         "each error")
    args = ap.parse_args(argv)

    if args.timeout <= 0:
        ap.error("--timeout must be a positive number of seconds")

    overall_ok = True
    any_timeout = False
    for i, path in enumerate(args.files):
        if args.show_movers:
            _print_movers(path)
        keep = args.emit_bpl if (args.emit_bpl and i == 0) else None
        result = check_program(
            path, boogie_path=args.boogie, keep_bpl=keep, timeout=args.timeout,
            counterexample=args.counterexample,
        )
        if args.show_bpl:
            print(f"// ===== Boogie for {path} =====")
            print(result.boogie_text)
        print(f"== {path} ==")
        print(result.render())
        print()
        overall_ok = overall_ok and result.ok
        any_timeout = any_timeout or result.timed_out
    if any_timeout:
        return EXIT_TIMEOUT
    return EXIT_OK if overall_ok else EXIT_FAILED


def _print_movers(path: str) -> None:
    """Best-effort annotated listing; front-end errors surface via the
    subsequent verification pass, so they are not repeated here."""
    try:
        with open(path) as f:
            source = f.read()
        prog = parse(source, path)
        ti = check_types(prog)
    except (OSError, MelvinError):
        return
    print(f"== {path} (movers) ==")
    print(render_listing(source, mover_annotations(prog, ti)))
    print()


if __name__ == "__main__":
    sys.exit(main())
