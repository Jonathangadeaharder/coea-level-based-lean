---
description: Pick next ready node in proofs/ DAG and try to close it (or split into subproofs).
---

# /proof-next — Close the next sorry

You are working inside the Lean repo at `/Users/jonathangadeaharder/projects/phd/lean-runtime-analysis/`.
The proof-closure plan lives at `proofs/PLAN.md`; the worker contract at `proofs/WORKER_PROMPT.md`.

## What you do this turn

### 1. Find the next ready leaf

Run the dashboard:

```bash
bash proofs/scripts/dashboard.sh
```

The "Frontier" section lists folders with `state: todo` and no unmet dependencies. Pick the **first** one. If the frontier is empty, look for folders with `state: split` whose children are all `state: done` — those are now mergeable; promote the parent.

If everything is `done` and `proofs/scripts/dashboard.sh` reports `Sorries: 0`, the project is closed — print a victory summary and stop.

If the user passed an argument (`/proof-next L703` etc.), use that folder instead of the dashboard pick.

### 2. Load the node's context

For the selected folder `proofs/<NODE>/`:

```
Read proofs/<NODE>/signature.lean
Read proofs/<NODE>/paper_source.md
Read proofs/<NODE>/status.md
Read proofs/<NODE>/attempt.lean
```

Also read the actual sorry-site:

```
grep -n "sorry" LBTCoupling.lean | head
Read the relevant ±30 lines around the line listed in signature.lean
```

If the node has `state: split`, also read every child's `status.md` to see what's done and what's pending.

### 3. Mark `in_progress`

Edit `proofs/<NODE>/status.md` and set `state: in_progress`. Add a timestamp comment.

### 4. Attempt the proof

Follow `proofs/WORKER_PROMPT.md` rules verbatim. Key constraints:

- **No new sorry, anywhere.** If you cannot close a step, split into `proofs/<NODE>/subproofs/<child-key>/` with the standard 5-file layout (`signature.lean`, `paper_source.md`, `status.md`, `attempt.lean`, empty `subproofs/`).
- **Try direct proof first**, ~2 hours of focused effort. Use `exact?`, `apply?`, `rw?`. Build often: `lake build LBTCoupling 2>&1 | tail -20`.
- **If splitting**, declare a placeholder `axiom child_name : <type>` in your `attempt.lean` (clearly TODO-marked, scoped to scratchpad only) and use it to develop the rest of the parent proof. The placeholder dies before merge.

### 5. Merge upward (only when truly green)

If `attempt.lean` compiles, contains no `sorry`, and contains no placeholder `axiom`:

```
# replace the sorry in LBTCoupling.lean with the proof body from attempt.lean
# lake build (full project) must be green
lake build 2>&1 | tail
# update status.md
state: done
```

Then re-run the dashboard. If new nodes became unblocked (their `depends_on` is now all `done`), update their `status.md` from `blocked` to `todo`.

### 6. Honest reporting

Whether you closed the node or split it, finish by:

- Updating `proofs/<NODE>/status.md` with state, what you tried, what worked / didn't.
- Printing a one-line summary to the user (e.g. `L703: split into 3 children; built green with placeholder axioms`).
- Suggesting the next `/proof-next` invocation if appropriate.

## Hard invariants (verified at end of turn)

```bash
# must be true after your turn finishes
bash proofs/scripts/dashboard.sh
# 1. Sorries count is strictly ≤ what it was at the start of the turn.
# 2. Axioms count is exactly 1 (level_based_theorem).
# 3. lake build is GREEN (or red only because of the specific sorry you intentionally left).
```

If any invariant breaks: revert and report. Do not commit partial work that breaks the build.

## Banned

- Adding `sorry` anywhere outside the existing 6 sites in `LBTCoupling.lean` (your job is to remove one of them, not add more).
- Adding `axiom` outside `attempt.lean` scratchpads.
- Modifying other nodes' folders.
- `native_decide`.
- Skipping the dashboard / lake build sanity checks at the end.
- Claiming `done` without `lake build` green over the full project.

## Quick reference

```
proofs/PLAN.md           DAG, dispatch rules
proofs/WORKER_PROMPT.md  Full worker contract (read this first if unsure)
proofs/scripts/dashboard.sh   Current state
LBTCoupling.lean         Where the 6 sorries live (lines 661, 669, 693, 703, 715, 1012)
```

**Argument handling:** `$ARGUMENTS` may contain a node key (e.g. `L703`). If set, work that node; otherwise pick from the frontier.
