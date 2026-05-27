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
| `openspec/specs/mathprover-workbench/` | SvelteKit UI, graph.json, dispatch API |
| `openspec/specs/agent-dispatch/` | Goedel/Aristotle routing, run artifacts |

## Project conventions

- **Proof work:** Read `proofs/<folder>/paper_source.md` first; translate, don't invent.
- **No new sorry** in main Lean tree; split into `subproofs/` instead.
- **Verify:** `lake build LBTCoupling` after every merge.
- **Dispatch:** `python agents/dispatch.py --node <folder> --prover auto`
- **UI:** `cd mathprover-ui && npm run dev` → `/workspace`
- **Graph reindex:** `python3 scripts/bootstrap_graph.py`

## Config

Project context and artifact rules: `openspec/config.yaml`

Run `openspec update` after upgrading the global CLI.
