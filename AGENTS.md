# AGENTS.md

This project uses [OpenSpec](https://github.com/Fission-AI/OpenSpec) for spec-driven development.

## Quick commands (Cursor)

| Command | Purpose |
|---------|---------|
| `/opsx:propose "<idea>"` | Create a new change with proposal, design, specs, tasks |
| `/opsx:apply` | Implement tasks from the active change |
| `/opsx:archive` | Archive completed change, update main specs |
| `/opsx:explore` | Explore codebase against specs |

## Active work

**Change:** `close-six-sorries` — close remaining LBTCoupling sorries (L661, L669, L693, L715, L1012).

See `openspec/changes/close-six-sorries/tasks.md` for checklist.

## Baseline specs

| Spec | Scope |
|------|-------|
| `openspec/specs/lean-proof-closure/` | Six-sorry DAG, worker contract, merge rules |

## Related repos

| Repo | Role |
|------|------|
| [VidiomTM/mathprover](https://github.com/VidiomTM/mathprover) | SvelteKit UI, agent dispatch, graph indexing (dev tool) |
| [VidiomTM/PPSN_FOGA_GECCO](https://github.com/VidiomTM/PPSN_FOGA_GECCO) | Paper drafts and empirical scripts |

## Project conventions

- **Proof work:** Read `proofs/<folder>/paper_source.md` first; translate, don't invent.
- **No new sorry** in main Lean tree; split into `subproofs/` instead.
- **Verify:** `lake build LBTCoupling` after every merge.
- **MathProver dispatch:** clone [mathprover](https://github.com/VidiomTM/mathprover), set `MATHPROVER_HOME`, then `python agents/dispatch.py --root . --node <folder> --prover auto`
- **MathProver UI:** `MATHPROVER_PROJECT_PATH=$(pwd) pnpm dev` from `mathprover/mathprover-ui`
- **Graph bootstrap:** `python3 scripts/bootstrap_graph.py` (project-specific DAG seed)

## Config

Project context and artifact rules: `openspec/config.yaml`

Run `openspec update` after upgrading the global CLI.
