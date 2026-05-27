# Six-Sorry Closure Plan — Parallel Workers + Tree of Subproofs

> **OpenSpec:** Canonical tracking lives in `openspec/changes/close-six-sorries/`.
> Baseline spec: `openspec/specs/lean-proof-closure/spec.md`.
> Use `/opsx:apply` in Cursor to work the task checklist.

## Goal

Close all 6 `sorry` in `LBTCoupling.lean`. Only `axiom level_based_theorem` (line 479) may remain.

Hard rule (user-imposed 2026-05-27): no new `sorry`. Workers either prove their goal end-to-end or define a tree of subgoals — never leave a bare `sorry` behind. A subgoal that itself defeats a worker becomes a child node in the tree; recursion continues until every leaf is provable.

## Dependency DAG (downstream depends on upstream)

```
                  ┌──> coea_sel_measure_cdf (L669) ──┐
                  │                                  │
r_local_G2 ───────┤                                  ├──> sel_monotone_level (L693)
   (L1012)        │                                  │
                  ├──> coea_measure_ge_from_count (L715) ──> mutation_prob_lower_bound (L703)
                  │
                  └──> sel_amplification_bound  [already proved, uses L669 + L715]

   coea_sel_measure_prob (L661)  [siblings L669 via shared telescoping; used by IsMarkovKernel coea_sel_kernel]
```

Frontier (independent, dispatch in parallel):
1. **L703** mutation lower bound  (pure analytic, no deps)
2. **L661** sel measure prob       (combinatorial)
3. **L669** sel measure CDF        (combinatorial, shares infra with L661)

Second wave (run after frontier closes):
4. **L693** sel_monotone_level     (needs L669)
5. **L715** coea_measure_ge_from_count  (needs L703)

Final:
6. **L1012** r_local_G2            (needs L669 + L715, plus already-proved `sel_amplification_bound` chain)

## Six-worker dispatch (theoretical maximum parallelism)

Each worker owns one folder under `proofs/`. Folders:

```
proofs/
├── PLAN.md                              ← this file
├── L661_coea_sel_measure_prob/
├── L669_coea_sel_measure_cdf/
├── L693_sel_monotone_level/
├── L703_mutation_prob_lower_bound/
├── L715_coea_measure_ge_from_count/
└── L1012_r_local_G2/
```

Per-folder contract:

```
<folder>/
├── signature.lean        - exact theorem signature copied from LBTCoupling.lean
├── paper_source.md       - paper / textbook reference + paper-style proof
├── attempt.lean          - direct proof attempt; either compiles (DONE) or has TODOs pointing to subproofs/
├── status.md             - state ∈ {todo, in_progress, split, blocked, done}; if split, lists child nodes
└── subproofs/            - empty initially; populated only if worker splits
    ├── <child-key>/      - same internal structure as parent (recursive)
    │   ├── signature.lean
    │   ├── attempt.lean
    │   └── status.md
    └── ...
```

`status.md` is the routing hint: `todo` = nobody owns yet, `in_progress` = active, `split` = see subproofs/, `blocked` = needs upstream sibling, `done` = ready to merge into `LBTCoupling.lean`.

## Worker assignments

The DAG's outdegree-zero nodes are the ones that can be dispatched immediately. With 6 workers, dispatch in two rounds:

**Round 1** (3 independent leaves):
- W1 → `L703_mutation_prob_lower_bound`
- W2 → `L661_coea_sel_measure_prob`
- W3 → `L669_coea_sel_measure_cdf`

**Round 2** (depends on Round 1):
- W4 → `L693_sel_monotone_level`     (waits for L669)
- W5 → `L715_coea_measure_ge_from_count` (waits for L703)
- W6 → `L1012_r_local_G2`             (waits for L669 + L715)

To achieve 6-way parallelism, Round-2 workers may start immediately by assuming their upstream signatures (with `axiom` placeholders in their `attempt.lean` scratchpad). They can develop the assembly proof against the assumed signatures; once upstream closes, they swap the placeholder for the real lemma. **Important:** these placeholder axioms live only inside the worker's `attempt.lean` and are stripped before merge.

## Worker contract (binding)

Each worker:

1. **Reads** the paper source and writes `paper_source.md` with the human-readable proof. Cite Corus et al. 2018 / Mathlib lemma / textbook exactly. No hand-waving.

2. **Tries direct proof** in `attempt.lean`. Time-box: ~2 hours. If the proof compiles cleanly with no `sorry`, mark `status.md` = `done` and stop.

3. **If stuck**, identifies the offending sub-claim(s). For each:
   - Create a child folder under `subproofs/<descriptive-key>/` with the same 5-file layout.
   - In the parent `attempt.lean`, replace the unproven step with a call to the not-yet-existing child theorem name (compiles via local `axiom` scaffold).
   - Set parent `status.md` = `split` and list each child.

4. **Never writes a `sorry`.** Every dead-end is a child folder, not a sorry.

5. **Reports progress** in `status.md`: which Mathlib lemmas tried, why each failed (rewrite couldn't unify, missing instance, etc.), what the child folder needs.

6. **Merges only proves**, in the order leaves → ... → root. When a worker's `attempt.lean` is fully `done` and no child is `split`, the worker copies the proof body back into `LBTCoupling.lean` replacing the original `sorry` and re-runs `lake build`.

## How to focus work

The dashboard is `git ls-tree`-able: any folder whose `status.md` = `todo` and whose `subproofs/` is empty (or all children are `done`) is a **leaf ready for work**. The PLAN's "Pick next" rule:

```
1. Find the deepest folder with status=todo and no unmet child dependencies.
2. If multiple such folders exist, prefer the one whose parent has the most siblings already done (highest leverage).
3. Dispatch.
```

A coordinator script (TODO: `scripts/proof_dashboard.py`) can scan and print the frontier.

## Honest accounting at any point

- 6 sorries in `LBTCoupling.lean`.
- Each closure decreases the count by exactly 1 (no replacement-with-helper-sorries; helpers go in `proofs/.../subproofs/`, not in the main tree).
- Final state: 0 sorries in any `*.lean` file under the lakefile; one `axiom level_based_theorem` survives by design.

## Quick-start commands

```
# from the lean repo root
bash proofs/scripts/dashboard.sh                                    # state + frontier + invariants
find proofs -name status.md -exec grep -l '^state: todo$' {} \;     # alt: list leaves
lake build LBTCoupling                                              # smoke after each merge
grep -rn '^\s*sorry' --include='*.lean' --exclude-dir='.lake' --exclude-dir='proofs' --exclude-dir='.worktrees' .
```

## Slash command

A Claude Code slash command is shipped at `.claude/commands/proof-next.md`.
When `claude` is launched with this repo as CWD:

```
/proof-next            # auto-pick the next ready leaf and try to close it
/proof-next L703       # work on the named node specifically
```

The command reads `WORKER_PROMPT.md`, picks a frontier node via the dashboard, attempts the proof, and either merges or splits into `subproofs/` — all under the no-new-sorry rule.
