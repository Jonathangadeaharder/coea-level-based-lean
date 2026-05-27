# Worker prompt template — drop into Agent subagent_type=general-purpose

You are closing one `sorry` in `LBTCoupling.lean` inside the Lean repo at
`/Users/jonathangadeaharder/projects/phd/lean-runtime-analysis/`.

**Your assignment**: `<ASSIGNMENT_FOLDER>` (e.g. `proofs/L703_mutation_prob_lower_bound/`)

## Hard rules

1. **Never write a new `sorry`** in any `*.lean` file in the project tree, including your scratchpad. If you cannot close a step, split it into a child folder with its own signature.lean + paper_source.md + status.md, and call the child as if it were already proved (via a local `axiom` declaration scoped to your `attempt.lean`).

2. **Read everything first**: your folder's `signature.lean`, `paper_source.md`, `status.md`; the actual sorry-site in `LBTCoupling.lean`; the surrounding definitions; the README at `proofs/PLAN.md`.

3. **Try direct proof first.** Mathlib has most of the analytic / combinatorial / measure-theoretic primitives you need. Use `exact?`, `apply?`, `rw?` liberally. Time-box: ~2 hours of focused attempt before considering a split.

4. **Build after every plausible state**: `lake build LBTCoupling 2>&1 | tail -20`. If green, you're done; if red, fix the topmost error.

5. **Honest reporting**: log what you tried (which Mathlib lemmas, which tactic combinations, why each failed) in `status.md`. Future workers benefit.

## Workflow

```
1. cd <ASSIGNMENT_FOLDER>
2. Read signature.lean, paper_source.md, status.md.
3. Read the relevant block in /Users/jonathangadeaharder/projects/phd/lean-runtime-analysis/LBTCoupling.lean
   (line range is in the signature).
4. Draft proof in attempt.lean.
5. Iterate against `lake build LBTCoupling`.
6. If stuck for ~2 hours:
   a. Identify the offending sub-claim(s).
   b. For each, create subproofs/<key>/ with the 5-file layout.
      - signature.lean: precise type of the sub-claim
      - paper_source.md: where it comes from + paper-style argument
      - status.md: state=todo, depends_on=<parents>
      - attempt.lean: empty scaffold
   c. In your attempt.lean, declare a local `axiom child_lemma : ...` (clearly
      marked with a TODO comment naming the subproofs folder) and use it.
   d. Set this folder's status.md = "split", list children.
7. When attempt.lean compiles and contains no `sorry` and no local placeholder
   `axiom`s, you are done:
   a. Copy the proof body into LBTCoupling.lean replacing the original `sorry`.
   b. `lake build 2>&1 | tail` — confirm the whole project is green.
   c. Set this folder's status.md = "done".
   d. Stop.
8. If at any point you realise a child can be merged back (its attempt.lean is
   done), apply step 7 recursively from the leaf upward.
```

## What you may NOT do

- Add a new `sorry` anywhere.
- Add an `axiom` outside your local scratchpad (only `level_based_theorem` is permitted in `LBTCoupling.lean`).
- Modify other workers' folders.
- Modify `LBTCoupling.lean` except to replace the specific `sorry` you own.
- Use `native_decide` (banned by `LintOptions.lean`).
- Skip the `lake build` after merging.

## Reading list

- `proofs/PLAN.md` — DAG, parallel dispatch order.
- Your `paper_source.md` — paper-style argument.
- `LBTCoupling.lean` (the whole file is ~1100 lines; pay attention to the
  helper lemmas around your sorry: `sel_exp_inequality`, `sel_amplification_bound`,
  `one_sub_pow_le_exp_neg_mul`, `parent_mut_measure`, `coea_measure`).
- `MeanRankingLemma.lean`, `Hoeffding.lean` — already-proved examples of the
  style and tactic repertoire you should match.

## Definition of done

```
grep -c '^\s*sorry' attempt.lean            -> 0
grep -c '^axiom\|^private axiom' attempt.lean -> 0  (no placeholder axioms remaining)
lake build 2>&1 | grep -c 'error:'          -> 0
status.md says: state: done
LBTCoupling.lean has the proof body in place of the original sorry.
```
