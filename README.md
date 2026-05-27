# lean-runtime-analysis

Lean 4 mechanization of level-based runtime analysis (Corus et al. 2018).
Active work: closing six measure-theory sorries in `LBTCoupling.lean` via the
`proofs/` worker DAG.

This repo is **Lean-only**. [MathProver](https://github.com/VidiomTM/mathprover)
(UI + agent dispatch) and [PPSN_FOGA_GECCO](https://github.com/VidiomTM/PPSN_FOGA_GECCO)
(papers) are separate repositories.

## Prerequisites

- [Elan](https://github.com/leanprover/elan) + Lean 4.28 (see `lean-toolchain`)
- [MathProver](https://github.com/VidiomTM/mathprover) cloned anywhere on disk
- Optional: Goedel MLX prover for local leaf attempts (`GOEDEL_PROVER_PATH`)

## Build

```bash
lake build
# or target the main coupling file:
lake build LBTCoupling
```

## MathProver setup

1. Clone MathProver next to this repo (recommended) or anywhere:

   ```bash
   git clone git@github.com:VidiomTM/mathprover.git ../mathprover
   ```

2. Copy environment template and edit paths:

   ```bash
   cp .env.example .env
   # set MATHPROVER_HOME, GOEDEL_PROVER_PATH, etc.
   source .env
   ```

3. Install MathProver agents once:

   ```bash
   cd "$MATHPROVER_HOME/agents" && uv sync
   ```

4. Generate the proof graph (local, gitignored):

   ```bash
   python3 scripts/reindex_graph.py
   ```

5. Open the workbench:

   ```bash
   cd "$MATHPROVER_HOME/mathprover-ui" && pnpm install && pnpm dev
   ```

   Visit `http://localhost:5173/workspace?project=$PWD` (from this repo root).

See [docs/mathprover.md](docs/mathprover.md) for dispatch, reindex, and graph conventions.

## Proof workers

| Path | Purpose |
|------|---------|
| `proofs/PLAN.md` | Six-sorry DAG and merge order |
| `proofs/<folder>/` | `signature.lean`, `paper_source.md`, `status.md`, `attempt.lean` |
| `proofs/scripts/dashboard.sh` | Terminal status dashboard |
| `mathprover.toml` | Goedel/Aristotle routing for this project |

Dispatch a leaf (from MathProver repo):

```bash
uv run --directory "$MATHPROVER_HOME/agents" python dispatch.py \
  --root "$(pwd)" \
  --node L661_coea_sel_measure_prob \
  --prover auto
```

## Layout

```
lean-runtime-analysis/
├── lakefile.lean          # Lake package drift_lean
├── LBTCoupling.lean       # Main coupling lemmas (six sorries)
├── proofs/                # Worker scaffolds
├── mathprover.toml        # Prover routing (MathProver reads this)
├── scripts/
│   ├── bootstrap_graph.py # Hand-maintained DAG → graph.json
│   ├── reindex_graph.py   # Bootstrap + merge runs (needs MATHPROVER_HOME)
│   └── mathprover_bridge.py
└── .mathprover/           # gitignored runtime (graph, runs, attempts)
    └── meta.json.example  # optional UI overlay template
```

## Related repos

| Repo | Role |
|------|------|
| [mathprover](https://github.com/VidiomTM/mathprover) | Workbench UI, dispatch, graph indexing |
| [PPSN_FOGA_GECCO](https://github.com/VidiomTM/PPSN_FOGA_GECCO) | Paper drafts, empirical scripts, lean status table |

Agent conventions: `AGENTS.md`. OpenSpec: `openspec/`.
