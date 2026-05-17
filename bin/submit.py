#!/usr/bin/env python3
"""Help submit a proof to the LeanEval leaderboard.

The submission process described at https://lean-lang.org/eval/submit/ is:
  1. Host the proof on a GitHub repo or public gist.
  2. Ensure each problem has: lakefile.toml (name=<problem_id>) + Submission.lean.
  3. Open a GitHub issue on leanprover/lean-eval with your repo/gist URL.

Usage:
    python bin/submit.py <problem_id>           # single problem
    python bin/submit.py --all                  # all solved/unsubmitted problems

The script opens the pre-filled GitHub issue form in your browser.
"""

import json
import sys
import webbrowser
from pathlib import Path

# Force UTF-8 on Windows consoles
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

REPO_ROOT = Path(__file__).resolve().parent.parent
SUBMISSIONS_DIR = REPO_ROOT / "submissions"
PROBLEMS_FILE = REPO_ROOT / "problems.json"

SUBMIT_PAGE = "https://lean-lang.org/eval/submit/"


def get_repo_url():
    """Try to guess the GitHub repo URL from git remote."""
    import subprocess
    try:
        remote = subprocess.check_output(
            ["git", "config", "--get", "remote.origin.url"],
            cwd=REPO_ROOT, text=True
        ).strip()
        if remote.startswith("git@github.com:"):
            remote = "https://github.com/" + remote.split(":")[1]
        if remote.endswith(".git"):
            remote = remote[:-4]
        return remote
    except Exception:
        return None


def verify_submission(problem_id):
    """Check that the submission has the required files and is not just `sorry`."""
    sub_dir = SUBMISSIONS_DIR / problem_id
    if not sub_dir.is_dir():
        return False, "No submission directory exists."

    lakefile = sub_dir / "lakefile.toml"
    if not lakefile.is_file():
        return False, "Missing lakefile.toml"

    sub_file = sub_dir / "Submission.lean"
    if not sub_file.is_file():
        return False, "Missing Submission.lean"

    content = sub_file.read_text(encoding="utf-8").lower()
    if "sorry" in content:
        return False, "Submission.lean still contains `sorry`."

    return True, "Ready to submit."


def submit_single(problem_id):
    ok, msg = verify_submission(problem_id)
    if not ok:
        print(f"  {problem_id}: NOT READY — {msg}")
        return False

    repo_url = get_repo_url()
    if not repo_url:
        print("Could not detect GitHub repo URL. Provide it manually:")
        repo_url = input("Repo URL: ").strip()

    print(f"  {problem_id}: ready")
    print(f"    Submission URL: {repo_url}")
    print(f"    -> Opening submit page at lean-lang.org/eval/submit/ ...")

    webbrowser.open(SUBMIT_PAGE)
    return True


def main():
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python bin/submit.py <problem_id>      # single problem")
        print("  python bin/submit.py --all             # all solved problems")
        print("  python bin/submit.py --list-ready      # list ready-to-submit")
        sys.exit(0)

    with open(PROBLEMS_FILE) as f:
        problems = json.load(f)

    if sys.argv[1] == "--list-ready":
        ready = []
        for pid in problems:
            if pid == "ci_regenerate_main_check":
                continue
            ok, _ = verify_submission(pid)
            if ok:
                ready.append(pid)
        if ready:
            print(f"{len(ready)} submissions ready:")
            for pid in ready:
                print(f"  {pid}")
        else:
            print("No submissions ready.")
        return

    if sys.argv[1] == "--all":
        repo_url = get_repo_url()
        if repo_url:
            print(f"Repo URL: {repo_url}")
        else:
            print("Could not detect GitHub repo URL.")
            repo_url = input("Repo URL: ").strip()

        ready = []
        for pid in problems:
            if pid == "ci_regenerate_main_check":
                continue
            ok, msg = verify_submission(pid)
            if ok:
                ready.append(pid)
                print(f"  READY: {pid}")
            else:
                print(f"  SKIP:  {pid} — {msg}")

        print(f"\n{len(ready)} submissions ready. Opening the submit page...")
        print(f"Use URL: {repo_url}")
        webbrowser.open(SUBMIT_PAGE)
        return

    # Single problem
    problem_id = sys.argv[1]
    if problem_id not in problems:
        print(f"Unknown problem: {problem_id}")
        sys.exit(1)

    submit_single(problem_id)


if __name__ == "__main__":
    main()
