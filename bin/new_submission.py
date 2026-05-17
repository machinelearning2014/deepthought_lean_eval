#!/usr/bin/env python3
"""Scaffold a submission directory for a LeanEval benchmark problem.

Usage:
    python bin/new_submission.py <problem_id>
    python bin/new_submission.py bakerWustholz_linearForms_logs
"""

import json
import sys
from pathlib import Path
from urllib.request import urlopen

# Force UTF-8 on Windows consoles
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

REPO_ROOT = Path(__file__).resolve().parent.parent
SUBMISSIONS_DIR = REPO_ROOT / "submissions"
PROBLEMS_FILE = REPO_ROOT / "problems.json"

BENCHMARK_RAW = "https://raw.githubusercontent.com/leanprover/lean-eval/main/generated"

LAKEFILE_TEMPLATE = """name = "{problem_id}"
"""


def fetch_problem_template(problem_id):
    """Fetch the Challenge.lean and Submission.lean templates from the benchmark repo."""
    base = f"{BENCHMARK_RAW}/{problem_id}"

    try:
        with urlopen(f"{base}/Challenge.lean") as resp:
            challenge = resp.read().decode("utf-8")
    except Exception:
        challenge = None

    try:
        with urlopen(f"{base}/Submission.lean") as resp:
            submission = resp.read().decode("utf-8")
    except Exception:
        submission = None

    return challenge, submission


def main():
    if len(sys.argv) < 2:
        print("Usage: python bin/new_submission.py <problem_id>")
        print("Run `python bin/list_problems.py` to see all problem IDs.")
        sys.exit(1)

    problem_id = sys.argv[1]

    with open(PROBLEMS_FILE) as f:
        problems = json.load(f)

    if problem_id not in problems:
        print(f"Unknown problem: {problem_id}")
        print("Run `python bin/list_problems.py` for a complete list.")
        sys.exit(1)

    sub_dir = SUBMISSIONS_DIR / problem_id
    if sub_dir.exists():
        print(f"Submission directory already exists: {sub_dir}")
        print("Delete it first if you want to re-scaffold.")
        sys.exit(1)

    sub_dir.mkdir(parents=True)
    helpers_dir = sub_dir / "Submission"
    helpers_dir.mkdir()

    # Write lakefile.toml
    (sub_dir / "lakefile.toml").write_text(LAKEFILE_TEMPLATE.format(problem_id=problem_id), encoding="utf-8")

    # Fetch upstream templates
    print(f"Fetching templates for {problem_id} ...")
    challenge, submission = fetch_problem_template(problem_id)

    if submission:
        (sub_dir / "Submission.lean").write_text(submission, encoding="utf-8")
        print(f"  Wrote Submission.lean")
    else:
        print(f"  [WARN] Could not fetch Submission.lean — write it manually")

    # Helpers stub
    (helpers_dir / "Helpers.lean").write_text(
        "namespace Submission.Helpers\n\nend Submission.Helpers\n",
        encoding="utf-8"
    )

    # Show info
    info = problems[problem_id]
    thms = info.get("theorem_names", [])
    defs = info.get("definition_names", [])

    print(f"\nScaffolded submission for: {problem_id}")
    if thms:
        print(f"  Theorems to prove:")
        for t in thms:
            print(f"    - {t}")
    if defs:
        print(f"  Definitions to fill:")
        for d in defs:
            print(f"    - {d}")
    print(f"\n  {sub_dir}/")
    print(f"    lakefile.toml")
    print(f"    Submission.lean     <-- replace `sorry` with your proof")
    print(f"    Submission/")
    print(f"      Helpers.lean    <-- add helper lemmas here")

    print(f"\nWhen ready, run: python bin/submit.py {problem_id}")


if __name__ == "__main__":
    main()
