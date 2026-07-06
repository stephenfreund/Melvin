"""Command-line interface: `python -m moverlogic file.mml [...]`."""

from __future__ import annotations

import argparse
import sys

from .checker import check_program


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
    ap.add_argument("--timeout", type=int, default=120, help="Boogie timeout (s)")
    args = ap.parse_args(argv)

    overall_ok = True
    for i, path in enumerate(args.files):
        keep = args.emit_bpl if (args.emit_bpl and i == 0) else None
        result = check_program(
            path, boogie_path=args.boogie, keep_bpl=keep, timeout=args.timeout
        )
        if args.show_bpl:
            print(f"// ===== Boogie for {path} =====")
            print(result.boogie_text)
        header = f"== {path} =="
        print(header)
        print(result.render())
        print()
        overall_ok = overall_ok and result.ok
    return 0 if overall_ok else 1


if __name__ == "__main__":
    sys.exit(main())
