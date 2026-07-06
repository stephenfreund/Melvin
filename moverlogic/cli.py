"""Command-line interface: `python -m moverlogic file.mml [...]`."""

from __future__ import annotations

import argparse
import sys

from .boogie_backend import DEFAULT_TIMEOUT
from .checker import check_program

# Distinct exit codes so scripts can tell a real refutation from a timeout.
EXIT_OK = 0
EXIT_FAILED = 1
EXIT_TIMEOUT = 2


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="moverlogic",
        description="Verify Mover Logic Language (.mll) programs using Boogie.",
    )
    ap.add_argument("files", nargs="+", help="MLL source files to verify")
    ap.add_argument("--boogie", help="path to the Boogie executable")
    ap.add_argument("--emit-bpl", metavar="PATH",
                    help="write the generated Boogie program to PATH (for the "
                         "first input file) and keep it")
    ap.add_argument("--show-bpl", action="store_true",
                    help="print the generated Boogie program")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT, metavar="SECONDS",
                    help="per-file Boogie verification timeout in seconds "
                         f"(default: {DEFAULT_TIMEOUT} = 5 minutes). On timeout the "
                         "file fails with exit code 2.")
    args = ap.parse_args(argv)

    if args.timeout <= 0:
        ap.error("--timeout must be a positive number of seconds")

    overall_ok = True
    any_timeout = False
    for i, path in enumerate(args.files):
        keep = args.emit_bpl if (args.emit_bpl and i == 0) else None
        result = check_program(
            path, boogie_path=args.boogie, keep_bpl=keep, timeout=args.timeout
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


if __name__ == "__main__":
    sys.exit(main())
