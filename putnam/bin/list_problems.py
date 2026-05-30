#!/usr/bin/env python3
"""List all PutnamBench problems and show local submission status."""

import json
import sys
from pathlib import Path
from urllib.request import urlopen

if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

PUTNAM_DIR = Path(__file__).resolve().parent.parent
PROBLEMS_FILE = PUTNAM_DIR / "putnam.json"
SUBMISSIONS_DIR = PUTNAM_DIR / "submissions"
PUTNAM_JSON_URL = "https://raw.githubusercontent.com/trishullab/PutnamBench/main/informal/putnam.json"
PUTNAM_SRC_URL = "https://raw.githubusercontent.com/trishullab/PutnamBench/main/lean4/src"


def load_or_fetch_problems():
    """Load putnam.json locally, fetching from GitHub if missing."""
    if PROBLEMS_FILE.exists():
        with open(PROBLEMS_FILE, encoding="utf-8") as f:
            return json.load(f)
    print(f"Fetching {PUTNAM_JSON_URL} ...")
    with urlopen(PUTNAM_JSON_URL) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    PROBLEMS_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return data


def submission_status(problem_name):
    sub_dir = SUBMISSIONS_DIR / problem_name
    if not sub_dir.is_dir():
        return " "
    sub_file = sub_dir / "Submission.lean"
    if not sub_file.is_file():
        return "E"
    content = sub_file.read_text(encoding="utf-8")
    if "sorry" in content.lower():
        return "."
    return "X"


def lean_file_exists(problem_name):
    """Check if the Lean source file exists in the PutnamBench repo."""
    # We don't want to fetch every file; just flag if we know it's missing
    return True  # assume exists unless we learn otherwise


def main():
    problems = load_or_fetch_problems()

    # Build problem name -> tags lookup
    by_tags = {}
    for p in problems:
        for tag in p.get("tags", []):
            by_tags.setdefault(tag, []).append(p["problem_name"])

    print(f"{'S':<2} {'Problem':<25} {'Year':<6} {'Tags':<50}")
    print(f"{'':->2} {'':->25} {'':->6} {'':->50}")

    for p in problems:
        name = p["problem_name"]
        status = submission_status(name)
        # Extract year from name like putnam_1962_a1
        parts = name.split("_")
        year = parts[1] if len(parts) > 1 else "?"
        tags = ", ".join(p.get("tags", []))
        print(f"{status:<2} {name:<25} {year:<6} {tags:<50}")

    total = len(problems)
    solved = sum(1 for p in problems if submission_status(p["problem_name"]) == "X")
    in_progress = sum(1 for p in problems if submission_status(p["problem_name"]) == ".")

    print(f"\n  X=solved  .=in-progress  E=empty  =not-attempted")
    print(f"  {solved} solved, {in_progress} in progress, {total} total")

    all_tags = sorted(by_tags.keys())
    print(f"\n  Tags ({len(all_tags)}): {', '.join(all_tags)}")


if __name__ == "__main__":
    main()
