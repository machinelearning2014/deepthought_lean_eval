#!/usr/bin/env python3
"""Extract a solved PutnamBench .lean file into a submission layout.

Usage:
    python putnam/bin/extract_submission.py <problem_name>
    python putnam/bin/extract_submission.py putnam_1962_a1
    python putnam/bin/extract_submission.py --source path/to/solved.lean putnam_1962_a1

The script reads the solved Lean file and writes to putnam/submissions/<problem_name>/.
"""

import argparse
import re
import sys
from pathlib import Path

if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

PUTNAM_DIR = Path(__file__).resolve().parent.parent
SUBMISSIONS_DIR = PUTNAM_DIR / "submissions"

DECL_KEYWORDS = (
    "abbrev", "axiom", "class", "def", "example",
    "inductive", "instance", "lemma", "opaque", "structure", "theorem",
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
IMPORT_RE = re.compile(r"^\s*(?:noncomputable\s+)?import\s+")
DOC_START_RE = re.compile(r"^\s*/-")
DOC_END_RE = re.compile(r"-/\s*$")
RE_NAMESPACE_CMD = re.compile(r"^\s*(namespace|end)\s+\S+.*$")


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
    """Split Lean source into docstring, imports, and declaration blocks."""
    lines = text.splitlines()
    items = []
    buffer = []
    pending_prefix = []
    current_name = None
    in_decl = False
    in_doc = False
    doc_lines = []

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
        stripped = line.strip()

        if in_doc:
            doc_lines.append(line)
            if DOC_END_RE.search(stripped):
                in_doc = False
                flush_prefix_as_other()
                items.append(Item("\n".join(doc_lines).rstrip() + "\n"))
                doc_lines = []
            continue

        if DOC_START_RE.match(stripped):
            doc_lines.append(line)
            in_doc = True
            continue

        if IMPORT_RE.match(stripped) and not in_decl:
            flush_prefix_as_other()
            items.append(Item(line.rstrip() + "\n"))
            continue

        is_prefix = stripped == "" or stripped.startswith("@[") or stripped.startswith("--")
        is_decl = DECL_START_RE.match(stripped)

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
    return any(name == t or bare_name == t.split(".")[-1] for t in target_names)


def indent_block(text, spaces=2):
    prefix = " " * spaces
    return "\n".join(prefix + line if line else "" for line in text.splitlines())


def _strip_namespace_wrappers(items):
    return [item for item in items if not RE_NAMESPACE_CMD.match(item)]


def render_helpers(helper_items):
    clean = _strip_namespace_wrappers(helper_items)
    body = "\n\n".join(item for item in clean if item)
    rendered = ["import Mathlib", "", "namespace Submission.Helpers"]
    if body:
        rendered.append("")
        rendered.append(indent_block(body))
    rendered.append("")
    rendered.append("end Submission.Helpers")
    rendered.append("")
    return "\n".join(rendered)


def render_submission(target_items, has_abbrev=False):
    body = "\n\n".join(item for item in target_items if item)
    rendered = ["import Mathlib", "import Submission.Helpers", "", "namespace Submission", "", "open Submission.Helpers", ""]
    rendered.append(indent_block(body))
    rendered.append("")
    rendered.append("end Submission")
    rendered.append("")
    return "\n".join(rendered)


def collect_parts(source_text, target_names):
    """Split source into imports, helpers, and target declarations."""
    helper_items = []
    target_items = []

    for item in split_items(source_text):
        text = item.text.strip()
        if text.lstrip().startswith("import ") or text.lstrip().startswith("noncomputable import "):
            continue  # imports handled by render functions
        elif is_target_name(item.name, target_names):
            target_items.append(item.text.strip())
        elif item.name and item.name.startswith("putnam_"):
            # Other Putnam abbrevs/theorems — keep in helpers if they're our solution abbrev
            target_items.append(item.text.strip())
        else:
            helper_items.append(item.text.strip())

    if not target_items:
        raise SystemExit(f"No target declarations found for: {target_names}")

    return helper_items, target_items


def write_submission(problem_name, helper_items, target_items):
    sub_dir = SUBMISSIONS_DIR / problem_name
    helpers_dir = sub_dir / "Submission"
    sub_dir.mkdir(parents=True, exist_ok=True)
    helpers_dir.mkdir(parents=True, exist_ok=True)

    lakefile = sub_dir / "lakefile.toml"
    if not lakefile.exists():
        lakefile.write_text(f'name = "{problem_name}"\n', encoding="utf-8")

    helpers_file = helpers_dir / "Helpers.lean"
    submission_file = sub_dir / "Submission.lean"
    helpers_file.write_text(render_helpers(helper_items), encoding="utf-8")
    submission_file.write_text(render_submission(target_items), encoding="utf-8")
    return submission_file, helpers_file


def main():
    parser = argparse.ArgumentParser(
        description="Extract solved PutnamBench .lean file into submission layout."
    )
    parser.add_argument("problem_name")
    parser.add_argument(
        "--source", type=Path,
        help="Explicit solved Lean file to extract.",
    )
    args = parser.parse_args()

    if args.source:
        source_file = args.source
    else:
        # Default: look for solved file alongside the submission
        source_file = SUBMISSIONS_DIR / args.problem_name / "solved.lean"
    if not source_file.is_file():
        raise SystemExit(f"Source file does not exist: {source_file}")

    source_text = source_file.read_text(encoding="utf-8")
    target_names = [args.problem_name, f"{args.problem_name}_solution"]
    helper_items, target_items = collect_parts(source_text, target_names)
    submission_file, helpers_file = write_submission(
        args.problem_name, helper_items, target_items
    )

    print(f"Extracted {source_file}")
    print(f"  target declarations: {len(target_items)} -> {submission_file.relative_to(PUTNAM_DIR)}")
    print(f"  helper items:        {len([h for h in helper_items if h])} -> {helpers_file.relative_to(PUTNAM_DIR)}")


if __name__ == "__main__":
    main()
