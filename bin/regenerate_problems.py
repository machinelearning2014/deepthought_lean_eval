#!/usr/bin/env python3
"""Regenerate problems.json from the upstream lean-eval benchmark index.

Fetches https://raw.githubusercontent.com/leanprover/lean-eval/main/generated/index.json
and converts it to the local problems.json format.
"""

import json
from pathlib import Path
from urllib.request import urlopen

UPSTREAM_INDEX = "https://raw.githubusercontent.com/leanprover/lean-eval/main/generated/index.json"
REPO_ROOT = Path(__file__).resolve().parent.parent
PROBLEMS_FILE = REPO_ROOT / "problems.json"


def fetch_index():
    print(f"Fetching {UPSTREAM_INDEX} ...")
    with urlopen(UPSTREAM_INDEX) as resp:
        return json.loads(resp.read().decode("utf-8"))


def index_to_problems(entries):
    problems = {}
    for entry in entries:
        pid = entry["id"]
        holes = entry.get("holes", [pid])
        problems[pid] = {
            "theorem_names": list(holes),
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "title": entry.get("title", ""),
            "module": entry.get("module", ""),
            "submitter": entry.get("submitter", ""),
        }
    return problems


def refine_from_local(problems):
    """Preserve theorem/definition splits from existing problems.json."""
    if not PROBLEMS_FILE.exists():
        return
    with open(PROBLEMS_FILE, encoding="utf-8") as f:
        old = json.load(f)
    for pid, info in problems.items():
        if pid in old:
            info["theorem_names"] = old[pid].get("theorem_names", info["theorem_names"])
            info["definition_names"] = old[pid].get("definition_names", info["definition_names"])


def main():
    entries = fetch_index()
    problems = index_to_problems(entries)
    refine_from_local(problems)

    with open(PROBLEMS_FILE, "w", encoding="utf-8", newline="\n") as f:
        json.dump(problems, f, indent=2, ensure_ascii=False)
        f.write("\n")

    n_real = len(problems) - 1  # exclude ci_regenerate_main_check
    print(f"Wrote {PROBLEMS_FILE} with {n_real} problems (+ ci_regenerate_main_check)")


if __name__ == "__main__":
    main()
