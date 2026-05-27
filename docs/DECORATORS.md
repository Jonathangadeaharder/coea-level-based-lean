# MathProver decorator format

Decorators live in Lean docstrings `/-- ... -/` immediately preceding a
declaration (`theorem`, `lemma`, `def`, `structure`, `axiom`, …).

`scripts/build_graph.py` parses them and emits `.mathprover/graph.json`.

## Theorem / lemma / axiom

```lean
/--
Free-form description (first non-tag lines).

@paper Lemma 7.5
@paper-id L703_mut_lower
@paper-file appendix.tex
@paper-section App. A.3 — G3 verification
@paper-stmt Under bit-flip rate 1/n, ℙ[hammingDist ≤ 1] ≥ 1/(2e).
@uses-defs def_BitString, def_mutationKernel, def_hammingDist
@depends-on lbt_axiom
@importance 0.8
@difficulty medium
@confidence 0.6
-/
theorem mutation_prob_lower_bound (n : ℕ) (hn : 1 ≤ n) (x : BitString n) :
    mutationKernel x {y | hammingDist x y ≤ 1} ≥ 1 / (2 * Real.exp 1) := by
  sorry
```

Tags:

| Tag             | Purpose                                              | Default                              |
|-----------------|------------------------------------------------------|--------------------------------------|
| `@paper`        | Paper label (e.g. "Lemma 7.5", "Thm 5.4")            | Lean name                            |
| `@paper-id`     | Node id used by the graph                            | `L<line>_<name>` if sorry, else name |
| `@paper-file`   | Relative paper file (e.g. `appendix.tex`)            | empty                                |
| `@paper-section`| Section / appendix label                             | empty                                |
| `@paper-stmt`   | Human-readable statement for the Detail panel        | none                                 |
| `@uses-defs`    | Comma-separated definition ids the statement needs   | `[]`                                 |
| `@depends-on`   | Comma-separated upstream node ids                    | `[]`                                 |
| `@importance`   | 0..1 weight for frontier ranking                     | 0.8 thm / 0.6 lemma / 0.95 axiom     |
| `@difficulty`   | `easy` / `medium` / `hard`                           | `medium`                             |
| `@confidence`   | 0..1 — agent's current self-assessment               | 1.0 if no sorry else 0.5             |
| `@capstone`     | Flag (no value) — marks the top of the DAG           | false                                |
| `@status`       | Override status: `PROVEN`/`SORRIES`/`BLOCKED`/…      | inferred from sorry / axiom          |
| `@implies`      | What this sorry unlocks (description text)           | empty                                |

Status auto-inference: `axiom` → PROVEN, body contains `sorry` → SORRIES,
otherwise PROVEN. Override with `@status BLOCKED` etc.

## Definition (`def`, `structure`, `inductive`, `abbrev`, `instance`, `class`)

```lean
/--
A two-player game whose value depends only on the first player's strategy.
The offset property holds exactly.

@def-id def_SeparableGame
@kind structure
@paper Def 2.1
@paper-section §2.1
@paper-file preliminaries.tex
@depends-on def_PopulationProcess
-/
structure SeparableGame (α β : Type _) where
  f : α → ℝ
  evalAgainst : β → α → ℝ
  h_separable : ∀ y x, evalAgainst y x = f x
```

Tags:

| Tag             | Purpose                                  | Default                            |
|-----------------|------------------------------------------|------------------------------------|
| `@def-id`       | Definition id used by the graph          | `def_<name>`                       |
| `@kind`         | `structure` / `def` / `inductive` / …    | inferred from the Lean keyword     |
| `@paper`        | Paper label (e.g. "Def 2.1")             | none                               |
| `@paper-section`| Section reference                        | none                               |
| `@paper-file`   | Relative paper file                      | none                               |
| `@depends-on`   | Other definition ids                     | `[]`                               |
| `@signature`    | Override displayed signature             | extracted from the next 4–6 lines  |
| `@name`         | Human-readable name (defaults to Lean)   | Lean name                          |

## Manual overlay — `.mathprover/meta.json`

Project metadata, foundations decomposition, paperBlocks / leanBlocks for the
Paper⇄Lean viewer, recents list, and the `terms` lookup live here. The
indexer merges this overlay with the auto-extracted nodes + definitions:

```json
{
  "project": { "name": "...", "paper": "...", "venue": "FOGA 2027", ... },
  "recents": [ ... ],
  "foundations": [ ... ],
  "paperBlocks": [ ... ],
  "leanBlocks":  [ ... ],
  "terms":       { ... },
  "failures":    [ ... ]
}
```

`nodes` and `definitions` from `meta.json` are **ignored** — they're always
re-derived from source. If you want to override fields on a generated node,
add the matching tags in the Lean docstring.

## Run

```bash
python3 "$MATHPROVER_HOME/scripts/build_graph.py" --root .
# emits .mathprover/graph.json

python3 "$MATHPROVER_HOME/scripts/build_graph.py" --root . --strict
# exits non-zero on validation errors (broken depends_on / uses_defs refs)
```

Wire into the dashboard:

```bash
bash proofs/scripts/dashboard.sh && python3 "$MATHPROVER_HOME/scripts/build_graph.py" --root . --strict
```

Or pre-commit / CI: fail the build if generated graph diverges from committed
graph (`git diff --exit-code .mathprover/graph.json`).
