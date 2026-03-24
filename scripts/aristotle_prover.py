#!/usr/bin/env python3
"""
aristotle_prover.py - Automated sorry-stub resolution for LegalLean Lean 4 files.

Integrates with Aristotle (harmonic.fun) via aristotlelib to prove sorry stubs.
Proofs can take 1-5 minutes; progress is reported throughout.

Usage:
    python3 scripts/aristotle_prover.py --file LegalLean/CaseStudies/IRC163h.lean
    python3 scripts/aristotle_prover.py --all --dry-run
    python3 scripts/aristotle_prover.py --all
"""

import argparse
import asyncio
import os
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# API key setup - translate ARISTOTLE_HARMONIC_API_KEY → ARISTOTLE_API_KEY
# before importing aristotlelib, because the library reads the env var at
# import time if set_api_key() has not yet been called.
# ---------------------------------------------------------------------------

def _configure_api_key() -> str:
    """Read ARISTOTLE_HARMONIC_API_KEY and expose it as ARISTOTLE_API_KEY."""
    # Load from ~/.env if the env var is absent
    env_file = Path("~/.env")
    key: str | None = os.environ.get("ARISTOTLE_HARMONIC_API_KEY")

    if not key and env_file.exists():
        for line in env_file.read_text().splitlines():
            line = line.strip()
            if line.startswith("ARISTOTLE_HARMONIC_API_KEY="):
                key = line.split("=", 1)[1].strip()
                break

    if not key:
        sys.exit(
            "ERROR: ARISTOTLE_HARMONIC_API_KEY not found in environment or "
            "~/.env. Cannot proceed."
        )

    os.environ["ARISTOTLE_API_KEY"] = key
    return key


_configure_api_key()

# Now safe to import aristotlelib (it will pick up ARISTOTLE_API_KEY)
import aristotlelib
from aristotlelib.project import Project, ProjectStatus, ProjectInputType
from aristotlelib.api_request import AristotleAPIError

# ---------------------------------------------------------------------------
# Sorry detection
# ---------------------------------------------------------------------------

# Matches bare `sorry` tokens - not inside strings, not part of longer names.
# Handles:
#   sorry
#   sorry -- comment
#   := by sorry
#   | _ => sorry
_SORRY_RE = re.compile(r"\bsorry\b")


@dataclass
class SorryLocation:
    line_no: int      # 1-based
    line_text: str    # stripped line content
    context: str      # brief description extracted from surrounding context


def find_sorry_stubs(file_path: Path) -> list[SorryLocation]:
    """Return every line in *file_path* that contains a `sorry` token."""
    stubs: list[SorryLocation] = []
    lines = file_path.read_text(encoding="utf-8").splitlines()

    for idx, line in enumerate(lines):
        if _SORRY_RE.search(line):
            # Extract nearest theorem/def/lemma name from preceding lines for context
            context = _nearest_decl(lines, idx)
            stubs.append(SorryLocation(
                line_no=idx + 1,
                line_text=line.strip(),
                context=context,
            ))
    return stubs


def _nearest_decl(lines: list[str], from_idx: int) -> str:
    """Walk backwards from *from_idx* to find the enclosing declaration name."""
    decl_re = re.compile(
        r"^\s*(?:theorem|lemma|def|abbrev|noncomputable def)\s+(\S+)"
    )
    for i in range(from_idx, -1, -1):
        m = decl_re.match(lines[i])
        if m:
            return m.group(1)
    return "<unknown>"


# ---------------------------------------------------------------------------
# Result tracking
# ---------------------------------------------------------------------------

@dataclass
class FileResult:
    file_path: Path
    sorries_before: list[SorryLocation]
    sorries_after: list[SorryLocation] = field(default_factory=list)
    output_path: Path | None = None
    project_id: str | None = None
    error: str | None = None
    skipped: bool = False  # True when dry-run or no sorries found

    @property
    def resolved(self) -> int:
        return len(self.sorries_before) - len(self.sorries_after)

    @property
    def remaining(self) -> int:
        return len(self.sorries_after)


# ---------------------------------------------------------------------------
# Core proving logic
# ---------------------------------------------------------------------------

async def prove_file(
    file_path: Path,
    *,
    polling_interval: int = 30,
    max_polling_failures: int = 5,
    timeout_minutes: int = 15,
) -> FileResult:
    """
    Submit *file_path* to Aristotle and wait for a proven result.

    Returns a FileResult regardless of outcome (errors are captured, not raised).
    """
    result = FileResult(
        file_path=file_path,
        sorries_before=find_sorry_stubs(file_path),
    )

    if not result.sorries_before:
        print(f"  [skip] {file_path.name} - no sorry stubs found")
        result.skipped = True
        return result

    # Derive output path: <stem>_aristotle.lean alongside the original
    output_path = file_path.with_stem(file_path.stem + "_aristotle")
    result.output_path = output_path

    print(
        f"  [submit] {file_path.name} "
        f"({len(result.sorries_before)} sorry stub(s)) → {output_path.name}"
    )

    start = time.monotonic()
    deadline = start + timeout_minutes * 60

    try:
        # prove_from_file handles: project creation, import gathering, polling,
        # and solution download. We use its built-in polling with our interval.
        # wait_for_completion=True is the default; we rely on max_polling_failures
        # and our own timeout guard via the outer asyncio.wait_for.
        solved_path_str = await asyncio.wait_for(
            Project.prove_from_file(
                input_file_path=file_path,
                auto_add_imports=True,
                validate_lean_project=True,
                polling_interval_seconds=polling_interval,
                max_polling_failures=max_polling_failures,
                output_file_path=output_path,
                project_input_type=ProjectInputType.FORMAL_LEAN,
            ),
            timeout=deadline - time.monotonic(),
        )

        elapsed = time.monotonic() - start
        print(f"  [done]  {file_path.name} in {elapsed:.0f}s → {solved_path_str}")

        # Diff: count remaining sorries in the output file
        solved_path = Path(solved_path_str)
        result.output_path = solved_path
        if solved_path.exists():
            result.sorries_after = find_sorry_stubs(solved_path)
        else:
            # API returned success but file not written - treat all as remaining
            result.sorries_after = list(result.sorries_before)

    except asyncio.TimeoutError:
        elapsed = time.monotonic() - start
        result.error = f"Timed out after {elapsed:.0f}s (limit: {timeout_minutes}m). Project may still be running in the background."
        print(f"  [timeout] {file_path.name}: {result.error}")

    except AristotleAPIError as exc:
        result.error = str(exc)
        print(f"  [api-error] {file_path.name}: {exc}")

    except Exception as exc:  # noqa: BLE001
        result.error = f"{type(exc).__name__}: {exc}"
        print(f"  [error] {file_path.name}: {result.error}")

    return result


# ---------------------------------------------------------------------------
# File discovery
# ---------------------------------------------------------------------------

def find_lean_files_with_sorries(root: Path) -> list[Path]:
    """Return all .lean files under *root* that contain at least one sorry."""
    hits: list[Path] = []
    for lean_file in sorted(root.rglob("*.lean")):
        # Skip generated / cache files
        if ".lake" in lean_file.parts:
            continue
        if find_sorry_stubs(lean_file):
            hits.append(lean_file)
    return hits


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def print_sorry_listing(file_path: Path, stubs: list[SorryLocation]) -> None:
    print(f"\n  {file_path}")
    for stub in stubs:
        print(f"    line {stub.line_no:4d}  [{stub.context}]  {stub.line_text}")


def print_summary(results: list[FileResult], dry_run: bool) -> None:
    print("\n" + "=" * 70)
    if dry_run:
        print("DRY RUN SUMMARY")
    else:
        print("PROVE SUMMARY")
    print("=" * 70)

    total_before = sum(len(r.sorries_before) for r in results)
    total_after = sum(len(r.sorries_after) for r in results if not r.skipped and not r.error)
    total_resolved = sum(r.resolved for r in results if not r.skipped and not r.error)
    errors = [r for r in results if r.error]

    print(f"Files processed : {len(results)}")
    print(f"Sorry stubs found: {total_before}")

    if not dry_run:
        print(f"Resolved        : {total_resolved}")
        print(f"Remaining       : {total_after}")
        print(f"Errors          : {len(errors)}")

    # Per-file breakdown
    print()
    for r in results:
        if r.skipped and not r.sorries_before:
            print(f"  [no sorries] {r.file_path}")
            continue

        if dry_run:
            print(f"\n  [{len(r.sorries_before)} sorries] {r.file_path}")
            for stub in r.sorries_before:
                print(f"    line {stub.line_no:4d}  [{stub.context}]  {stub.line_text}")
            continue

        if r.error:
            print(f"  [ERROR] {r.file_path}")
            print(f"          {r.error}")
        elif r.output_path:
            status = "FULLY PROVEN" if r.remaining == 0 else f"{r.remaining} REMAINING"
            print(
                f"  [{status}] {r.file_path.name}"
                f"  ({r.resolved}/{len(r.sorries_before)} resolved)"
                f"  → {r.output_path}"
            )
            if r.sorries_after:
                print("    Remaining sorry stubs:")
                for stub in r.sorries_after:
                    print(f"      line {stub.line_no:4d}  [{stub.context}]  {stub.line_text}")

    print()


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Prove sorry stubs in LegalLean Lean 4 files using Aristotle (harmonic.fun).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Prove all sorries in IRC §163(h)
  python3 scripts/aristotle_prover.py --file LegalLean/CaseStudies/IRC163h.lean

  # List sorry stubs without calling the API
  python3 scripts/aristotle_prover.py --all --dry-run

  # Prove all files with sorry stubs
  python3 scripts/aristotle_prover.py --all

  # Prove a file with a longer timeout (some proofs take several minutes)
  python3 scripts/aristotle_prover.py --file LegalLean/Core.lean --timeout 20
""",
    )

    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument(
        "--file",
        metavar="PATH",
        help="Path to a specific .lean file to prove.",
    )
    target.add_argument(
        "--all",
        action="store_true",
        help="Process all .lean files (excluding .lake/) that contain sorry stubs.",
    )

    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="List sorry stubs without submitting anything to the API.",
    )
    parser.add_argument(
        "--root",
        metavar="DIR",
        default=".",
        help="Project root to search when --all is used (default: current directory).",
    )
    parser.add_argument(
        "--polling-interval",
        type=int,
        default=30,
        metavar="SECONDS",
        help="Seconds between status polls while waiting for a proof (default: 30).",
    )
    parser.add_argument(
        "--max-polling-failures",
        type=int,
        default=5,
        metavar="N",
        help="Max consecutive poll failures before aborting (default: 5).",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=15,
        metavar="MINUTES",
        help="Per-file timeout in minutes (default: 15). "
             "The Aristotle project continues running server-side even if we time out.",
    )
    parser.add_argument(
        "--sequential",
        action="store_true",
        help="Prove files one at a time (default: parallel). "
             "Use when you have hit the 5-concurrent-project API limit.",
    )
    return parser


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

async def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    # --- Resolve target files ---
    if args.file:
        target_path = Path(args.file)
        if not target_path.exists():
            print(f"ERROR: file not found: {target_path}", file=sys.stderr)
            return 1
        if not target_path.suffix == ".lean":
            print(f"ERROR: not a .lean file: {target_path}", file=sys.stderr)
            return 1
        files = [target_path]
    else:
        root = Path(args.root).resolve()
        print(f"Scanning {root} for .lean files with sorry stubs...")
        files = find_lean_files_with_sorries(root)
        if not files:
            print("No .lean files with sorry stubs found.")
            return 0
        print(f"Found {len(files)} file(s) with sorry stubs.")

    # --- Dry run: just list stubs ---
    if args.dry_run:
        results = []
        for f in files:
            stubs = find_sorry_stubs(f)
            results.append(FileResult(file_path=f, sorries_before=stubs, skipped=True))
        print_summary(results, dry_run=True)
        return 0

    # --- Prove ---
    prove_kwargs = dict(
        polling_interval=args.polling_interval,
        max_polling_failures=args.max_polling_failures,
        timeout_minutes=args.timeout,
    )

    print(f"\nSubmitting {len(files)} file(s) to Aristotle (proofs take 1-5 min each)...")
    print(f"Polling every {args.polling_interval}s, timeout {args.timeout}min per file.\n")

    results: list[FileResult] = []

    if args.sequential or len(files) == 1:
        for f in files:
            print(f"[{files.index(f) + 1}/{len(files)}] {f}")
            r = await prove_file(f, **prove_kwargs)
            results.append(r)
    else:
        # Parallel: submit all, then gather. The Aristotle API allows up to 5
        # concurrent projects; we cap at 5 to avoid 429 errors.
        max_concurrent = 5
        semaphore = asyncio.Semaphore(max_concurrent)

        async def bounded_prove(f: Path) -> FileResult:
            async with semaphore:
                print(f"[starting] {f}")
                return await prove_file(f, **prove_kwargs)

        tasks = [asyncio.create_task(bounded_prove(f)) for f in files]
        results = list(await asyncio.gather(*tasks))

    print_summary(results, dry_run=False)

    # Exit non-zero if any file errored or still has sorries
    has_errors = any(r.error for r in results)
    has_remaining = any(r.remaining > 0 for r in results)
    return 1 if (has_errors or has_remaining) else 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
