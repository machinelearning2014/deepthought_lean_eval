#!/usr/bin/env python3
"""Extract a solved Lean file into a leaderboard submission layout.

Usage:
    python bin/extract_submission.py <problem_id>
    python bin/extract_submission.py two_plus_two_eq_four

The script looks for DeepthoughtLeanEval/<problem_id>.lean and writes to
submissions/<problem_id>/.
Target problem declarations are written to submissions/<problem_id>/Submission.lean.
All other declarations from the solved file are written to
submissions/<problem_id>/Submission/Helpers.lean.
"""

import argparse
import json
import re
import sys
from pathlib import Path

# Force UTF-8 on Windows consoles.
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIR = REPO_ROOT / "DeepthoughtLeanEval"
SUBMISSIONS_DIR = REPO_ROOT / "submissions"
PROBLEMS_FILE = REPO_ROOT / "problems.json"

DECL_KEYWORDS = (
    "abbrev",
    "axiom",
    "class",
    "def",
    "example",
    "inductive",
    "instance",
    "lemma",
    "opaque",
    "structure",
    "theorem",
)

DECL_START_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?P<keyword>" + "|".join(DECL_KEYWORDS) + r")\b"
)
DECL_NAME_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?P<keyword>" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>`[^`]+`|[^\s:({[]+)"
)
IMPORT_RE = re.compile(r"^\s*import\s+")
ATTRIBUTE_RE = re.compile(r"^\s*@\[")
COMMENT_RE = re.compile(r"^\s*--")


def load_problem(problem_id):
    with open(PROBLEMS_FILE, encoding="utf-8") as f:
        problems = json.load(f)
    return problems.get(problem_id)


def find_source_file(problem_id):
    candidate = SOURCE_DIR / f"{problem_id}.lean"
    if candidate.is_file():
        return candidate
    raise SystemExit(f"Could not find solved Lean file: {candidate}")


class Item:
    def __init__(self, text, name=None):
        self.text = text
        self.name = name


def declaration_name(line):
    match = DECL_NAME_RE.match(line)
    if not match:
        return None
    return match.group("name").strip("`")


def split_items(text):
    """Split a Lean file into import lines, declarations, and other command blocks.

    This intentionally stays lightweight. It recognizes top-level declarations
    and keeps attributes/comments immediately before a declaration with it.
    """
    lines = text.splitlines()
    items = []
    buffer = []
    pending_prefix = []
    current_name = None
    in_decl = False

    def flush_buffer():
        nonlocal buffer, current_name, in_decl
        if buffer:
            items.append(Item("\n".join(buffer).rstrip() + "\n", current_name))
        buffer = []
        current_name = None
        in_decl = False

    def flush_prefix_as_other():
        nonlocal pending_prefix
        if pending_prefix:
            items.append(Item("\n".join(pending_prefix).rstrip() + "\n"))
            pending_prefix = []

    for line in lines:
        is_prefix = ATTRIBUTE_RE.match(line) or COMMENT_RE.match(line) or line.strip() == ""
        is_decl = DECL_START_RE.match(line)

        if is_decl:
            flush_buffer()
            buffer = pending_prefix + [line]
            pending_prefix = []
            current_name = declaration_name(line)
            in_decl = True
            continue

        if in_decl:
            buffer.append(line)
            continue

        if IMPORT_RE.match(line):
            flush_prefix_as_other()
            items.append(Item(line.rstrip() + "\n"))
            continue

        if is_prefix:
            pending_prefix.append(line)
            continue

        flush_prefix_as_other()
        items.append(Item(line.rstrip() + "\n"))

    flush_buffer()
    flush_prefix_as_other()
    return items


def is_target_name(name, target_names):
    if not name:
        return False
    bare_name = name.split(".")[-1]
    return any(name == target or bare_name == target.split(".")[-1] for target in target_names)


def collect_parts(source_text, target_names):
    imports = []
    helper_items = []
    target_items = []

    for item in split_items(source_text):
        if item.text.lstrip().startswith("import "):
            imports.append(item.text.strip())
        elif is_target_name(item.name, target_names):
            target_items.append(item.text.strip())
        else:
            helper_items.append(item.text.strip())

    if not target_items:
        targets = ", ".join(target_names)
        raise SystemExit(f"No target declarations found in source file for: {targets}")

    return sorted(set(imports)), helper_items, target_items


def indent_block(text, spaces=2):
    prefix = " " * spaces
    return "\n".join(prefix + line if line else "" for line in text.splitlines())


RE_NAMESPACE_CMD = re.compile(r"^\s*(namespace|end)\s+\S+.*$")

def _strip_namespace_wrappers(items):
    """Remove `namespace Foo` / `end Foo` lines that wrapped the source file.

    The submission layout provides its own namespace (`Submission.Helpers` for
    helpers, `Submission` for the target theorem), so any namespace commands
    carried over from the source file would cause double-wrapping.
    """
    return [item for item in items if not RE_NAMESPACE_CMD.match(item)]


def render_helpers(imports, helper_items):
    clean = _strip_namespace_wrappers(helper_items)
    body = "\n\n".join(item for item in clean if item)
    rendered = []
    rendered.extend(imports or ["import Mathlib"])
    rendered.append("")
    rendered.append("namespace Submission.Helpers")
    if body:
        rendered.append("")
        rendered.append(indent_block(body))
    rendered.append("")
    rendered.append("end Submission.Helpers")
    rendered.append("")
    return "\n".join(rendered)


def render_submission(imports, target_items):
    body = "\n\n".join(item for item in target_items if item)
    rendered = []
    rendered.extend(imports or ["import Mathlib"])
    rendered.append("import Submission.Helpers")
    rendered.append("")
    rendered.append("namespace Submission")
    rendered.append("")
    rendered.append("open Submission.Helpers")
    rendered.append("")
    rendered.append(indent_block(body))
    rendered.append("")
    rendered.append("end Submission")
    rendered.append("")
    return "\n".join(rendered)


def write_submission(problem_id, imports, helper_items, target_items):
    sub_dir = SUBMISSIONS_DIR / problem_id
    helpers_dir = sub_dir / "Submission"
    sub_dir.mkdir(parents=True, exist_ok=True)
    helpers_dir.mkdir(parents=True, exist_ok=True)

    lakefile = sub_dir / "lakefile.toml"
    if not lakefile.exists():
        lakefile.write_text(f'name = "{problem_id}"\n', encoding="utf-8")

    helpers_file = helpers_dir / "Helpers.lean"
    submission_file = sub_dir / "Submission.lean"
    helpers_file.write_text(render_helpers(imports, helper_items), encoding="utf-8")
    submission_file.write_text(render_submission(imports, target_items), encoding="utf-8")
    return submission_file, helpers_file


def main():
    parser = argparse.ArgumentParser(
        description="Extract DeepthoughtLeanEval/<problem_id>.lean into submissions/<problem_id>."
    )
    parser.add_argument("problem_id")
    parser.add_argument(
        "--source",
        type=Path,
        help="Explicit solved Lean file to extract instead of auto-detecting.",
    )
    args = parser.parse_args()

    problem = load_problem(args.problem_id)
    target_names = [args.problem_id]
    if problem:
        target_names.extend(problem.get("theorem_names", []))
        target_names.extend(problem.get("definition_names", []))

    source_file = args.source if args.source else find_source_file(args.problem_id)
    if not source_file.is_file():
        raise SystemExit(f"Source file does not exist: {source_file}")

    source_text = source_file.read_text(encoding="utf-8")
    imports, helper_items, target_items = collect_parts(source_text, target_names)
    submission_file, helpers_file = write_submission(args.problem_id, imports, helper_items, target_items)

    print(f"Extracted {source_file.relative_to(REPO_ROOT)}")
    print(f"  target declarations: {len(target_items)} -> {submission_file.relative_to(REPO_ROOT)}")
    print(f"  helper items:        {len([item for item in helper_items if item])} -> {helpers_file.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
