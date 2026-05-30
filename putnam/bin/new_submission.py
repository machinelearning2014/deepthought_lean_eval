#!/usr/bin/env python3
"""Scaffold a submission directory for a PutnamBench problem.

Usage:
    python putnam/bin/new_submission.py <problem_name>
    python putnam/bin/new_submission.py putnam_1962_a1
"""

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
SUBMISSIONS_DIR = PUTNAM_DIR / "submissions"
PROBLEMS_FILE = PUTNAM_DIR / "putnam.json"

PUTNAM_JSON_URL = "https://raw.githubusercontent.com/trishullab/PutnamBench/main/informal/putnam.json"
PUTNAM_SRC_URL = "https://raw.githubusercontent.com/trishullab/PutnamBench/main/lean4/src"

LAKEFILE_TEMPLATE = """name = "{problem_name}"
"""


def fetch_raw(url):
    try:
        with urlopen(url) as resp:
            return resp.read().decode("utf-8")
    except Exception:
        return None


def load_or_fetch_problems():
    if PROBLEMS_FILE.exists():
        with open(PROBLEMS_FILE, encoding="utf-8") as f:
            return json.load(f)
    print(f"Fetching {PUTNAM_JSON_URL} ...")
    data = json.loads(urlopen(PUTNAM_JSON_URL).read().decode("utf-8"))
    PROBLEMS_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return data


def problem_metadata(problems, problem_name):
    for p in problems:
        if p["problem_name"] == problem_name:
            return p
    return None


def parse_lean_source(text):
    """Extract preamble, abbrev, and theorem from a PutnamBench Lean file."""
    lines = text.splitlines()
    preamble = []   # import, open, noncomputable lines
    abbrevs = []
    theorem_lines = []
    in_doc = False
    in_theorem = False

    for line in lines:
        stripped = line.strip()

        if stripped.startswith("import ") or stripped.startswith("open ") or stripped == "noncomputable":
            preamble.append(stripped)
            continue

        if stripped == "":
            continue

        if stripped.startswith("/-"):
            in_doc = True
            continue
        if in_doc:
            if stripped == "-/":
                in_doc = False
            continue

        if stripped.startswith("abbrev "):
            abbrevs.append(stripped)
            continue

        if stripped.startswith("theorem ") and not in_theorem:
            in_theorem = True
            theorem_lines.append(line)
            continue

        if in_theorem:
            theorem_lines.append(line)

    return {
        "preamble": preamble,
        "abbrevs": abbrevs,
        "theorem_text": "\n".join(theorem_lines) if theorem_lines else None,
    }


def render_submission(parsed):
    """Render the Submission.lean file for a PutnamBench problem."""
    rendered = []

    # Preamble (import Mathlib + any opens from source)
    # Always ensure import Mathlib is present
    has_mathlib = any("Mathlib" in p for p in parsed["preamble"])
    if not has_mathlib:
        rendered.append("import Mathlib")
    for p in parsed["preamble"]:
        if p not in ("import Mathlib",):
            rendered.append(p)
    rendered.append("import Submission.Helpers")
    rendered.append("")

    rendered.append("namespace Submission")
    rendered.append("")
    rendered.append("open Submission.Helpers")
    rendered.append("")

    # If there are abbrevs, include them
    for a in parsed["abbrevs"]:
        rendered.append(a)
        rendered.append("")

    # Theorem
    if parsed["theorem_text"]:
        for line in parsed["theorem_text"].splitlines():
            if line.strip().startswith("theorem "):
                # Keep the theorem signature but remove the proof body
                rendered.append(line.rstrip())
            elif line.strip() in ("sorry", ":=", ":= sorry", ":= by", ":= by sorry"):
                continue
            else:
                rendered.append(line.rstrip())
        rendered.append("  sorry")
        rendered.append("")

    rendered.append("end Submission")
    rendered.append("")
    return "\n".join(rendered)


def main():
    if len(sys.argv) < 2:
        print("Usage: python putnam/bin/new_submission.py <problem_name>")
        print("Example: python putnam/bin/new_submission.py putnam_1962_a1")
        sys.exit(1)

    problem_name = sys.argv[1]

    problems = load_or_fetch_problems()
    meta = problem_metadata(problems, problem_name)

    if meta is None:
        print(f"Unknown problem: {problem_name}")
        print("Run `python putnam/bin/list_problems.py` for the complete list.")
        sys.exit(1)

    sub_dir = SUBMISSIONS_DIR / problem_name
    if sub_dir.exists():
        print(f"Submission directory already exists: {sub_dir}")
        print("Delete it first if you want to re-scaffold.")
        sys.exit(1)

    # Fetch source from PutnamBench
    url = f"{PUTNAM_SRC_URL}/{problem_name}.lean"
    print(f"Fetching {url} ...")
    source = fetch_raw(url)
    if source is None:
        print(f"[ERROR] Could not fetch {problem_name}.lean from PutnamBench")
        sys.exit(1)

    parsed = parse_lean_source(source)

    if not parsed["theorem_text"]:
        print(f"[ERROR] No theorem found in {problem_name}.lean")
        sys.exit(1)

    # Create directory structure
    sub_dir.mkdir(parents=True)
    helpers_dir = sub_dir / "Submission"
    helpers_dir.mkdir()

    # Write lakefile.toml
    (sub_dir / "lakefile.toml").write_text(
        LAKEFILE_TEMPLATE.format(problem_name=problem_name), encoding="utf-8"
    )

    # Write Submission.lean
    (sub_dir / "Submission.lean").write_text(render_submission(parsed), encoding="utf-8")

    # Helpers stub
    (helpers_dir / "Helpers.lean").write_text(
        "import Mathlib\n\nnamespace Submission.Helpers\n\nend Submission.Helpers\n",
        encoding="utf-8",
    )

    tags = ", ".join(meta.get("tags", []))
    solution = meta.get("informal_solution", "None.")
    print(f"\nScaffolded submission for: {problem_name}")
    print(f"  Year: {problem_name.split('_')[1]}")
    print(f"  Tags: {tags}")
    print(f"  Answer hint: {solution[:80]}{'...' if len(solution) > 80 else ''}")
    print(f"\n  {sub_dir}/")
    print(f"    lakefile.toml")
    print(f"    Submission.lean     <-- replace `sorry` with your proof")
    print(f"    Submission/")
    print(f"      Helpers.lean      <-- add helper lemmas here")


if __name__ == "__main__":
    main()
