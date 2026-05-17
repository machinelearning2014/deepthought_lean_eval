# deepthought_lean_eval

Submissions to the [Lean AI Formalization Leaderboard](https://lean-lang.org/eval/).

## Quick start

```bash
# List all benchmark problems and their submission status
python bin/list_problems.py

# Scaffold a new submission
python bin/new_submission.py <problem_id>

# Check which submissions are ready
python bin/submit.py --list-ready
```

## Workflow

1. **Pick a problem** — `python bin/list_problems.py` shows all 60 problems and your local status.

2. **Scaffold** — `python bin/new_submission.py <problem_id>` creates `submissions/<problem_id>/` with:
   - `lakefile.toml` — declares `name = "<problem_id>"` so CI can match it
   - `Submission.lean` — the theorem with `sorry` placeholder (fetched from upstream)
   - `Submission/Helpers.lean` — stub for helper lemmas

3. **Prove** — Replace `sorry` in `Submission.lean` with your proof. Add helper lemmas under `Submission/`.

4. **Submit** — Push to GitHub, then `python bin/submit.py <problem_id>` opens the issue form at [lean-lang.org/eval/submit/](https://lean-lang.org/eval/submit/).

## What CI sees

The leaderboard CI scans every directory that contains **both** a `lakefile.toml` with a matching problem `name` and a `Submission.lean`. It overlays only two things onto a pristine benchmark workspace:

- `Submission.lean`
- `Submission/**/*.lean`

Everything else (`Solution.lean`, `Challenge.lean`, modified `lakefile.toml`) is **ignored**.

## Directory layout

```
submissions/
  <problem_id>/
    lakefile.toml          # name = "<problem_id>"
    Submission.lean        # your proof
    Submission/
      Helpers.lean         # helper lemmas (optional)
```

## Requirements

- The proof must be hosted on a **public GitHub repo** (or public gist)
- Private repos require installing the `lean-eval-bot` GitHub App
- Submissions are **cumulative** — every success is sticky, no submission limit

## Benchmark problems

| Status | Description |
|--------|-------------|
| `X` | solved — no `sorry` in Submission.lean |
| `.` | in progress — Submission.lean still has `sorry` |
| `E` | empty directory — scaffolding incomplete |
| ` ` | not attempted |

Run `python bin/list_problems.py` to see the full list.
