#!/usr/bin/env python3
"""List all LeanEval benchmark problems and show local submission status."""

import json
import sys
from pathlib import Path

# Force UTF-8 on Windows consoles
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

REPO_ROOT = Path(__file__).resolve().parent.parent
PROBLEMS_FILE = REPO_ROOT / "problems.json"
SUBMISSIONS_DIR = REPO_ROOT / "submissions"


def load_problems():
    with open(PROBLEMS_FILE) as f:
        return json.load(f)


def submission_status(problem_id):
    """Check if a submission exists for this problem and has content beyond `sorry`."""
    sub_dir = SUBMISSIONS_DIR / problem_id
    if not sub_dir.is_dir():
        return " "
    sub_file = sub_dir / "Submission.lean"
    if not sub_file.is_file():
        return "E"  # empty — dir exists but no Submission.lean
    content = sub_file.read_text(encoding="utf-8")
    if "sorry" in content.lower():
        return "."  # has file but still has sorry
    return "X"  # proof written (no sorry found)


def main():
    problems = load_problems()
    print(f"{'S':<2} {'Problem ID':<60} {'Th':<3} {'Df':<3} {'Title':<50}")
    print(f"{'':->2} {'':->60} {'':->3} {'':->3} {'':->50}")

    for pid, info in sorted(problems.items()):
        if pid == "ci_regenerate_main_check":
            continue
        status = submission_status(pid)
        n_thm = len(info.get("theorem_names", []))
        n_def = len(info.get("definition_names", []))
        title = info.get("title", "")[:48]
        print(f"{status:<2} {pid:<60} {n_thm:<3} {n_def:<3} {title:<50}")

    total = len(problems) - 1  # exclude ci_regenerate_main_check
    solved = sum(
        1 for pid in problems if pid != "ci_regenerate_main_check" and submission_status(pid) == "X"
    )
    in_progress = sum(
        1 for pid in problems if pid != "ci_regenerate_main_check" and submission_status(pid) == "."
    )
    print(f"\n  X=solved  .=in-progress  E=empty-dir  =not-attempted")
    print(f"  {solved} solved, {in_progress} in progress, {total} total")


if __name__ == "__main__":
    main()
