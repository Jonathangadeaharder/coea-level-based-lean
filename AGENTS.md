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

## Related repos (independent)

| Repo | Role |
|------|------|
| [VidiomTM/mathprover](https://github.com/VidiomTM/mathprover) | SvelteKit UI, agent dispatch, graph indexing |
| [VidiomTM/PPSN_FOGA_GECCO](https://github.com/VidiomTM/PPSN_FOGA_GECCO) | Paper drafts, empirical scripts, lean status table |

## MathProver workflow

Clone [mathprover](https://github.com/VidiomTM/mathprover) as sibling `../mathprover` or set `MATHPROVER_HOME`.

```bash
cp .env.example .env && source .env   # once
make agents-sync && make reindex && make ui
make dispatch NODE=L661_coea_sel_measure_prob
make dashboard
```

Full guide: [docs/mathprover.md](docs/mathprover.md). Decorator syntax: [docs/DECORATORS.md](docs/DECORATORS.md).

## Project conventions

- **Proof work:** Read `proofs/<folder>/paper_source.md` first; translate, don't invent.
- **No new sorry** in main Lean tree; split into `subproofs/` instead.
- **Verify:** `lake build LBTCoupling` after every merge.
- **Makefile:** `make reindex`, `make ui`, `make dispatch NODE=...`, `make dashboard`

## Config

Project context: `openspec/config.yaml`. Run `openspec update` after upgrading the global CLI.
