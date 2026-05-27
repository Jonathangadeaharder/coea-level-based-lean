# MathProver integration

This Lean project consumes [MathProver](https://github.com/VidiomTM/mathprover) as an
**external dev tool**. Nothing from MathProver is vendored here — set `MATHPROVER_HOME`
to your clone.

## Environment

Copy `.env.example` → `.env` and export before using scripts or the UI:

| Variable | Required | Purpose |
|----------|----------|---------|
| `MATHPROVER_HOME` | yes | Path to the mathprover git clone |
| `MATHPROVER_PROJECT_PATH` | for UI default | This repo root |
| `GOEDEL_PROVER_PATH` | for Goedel dispatch | Local MLX runner script |
| `ARISTOTLE_API_KEY` | for Aristotle | Cloud prover API key |

If `MATHPROVER_HOME` is unset, `scripts/mathprover_bridge.py` looks for a sibling
`../mathprover` directory (typical `phd/lean-runtime-analysis` + `phd/mathprover` layout).

## Graph lifecycle

MathProver UI reads `.mathprover/graph.json` (gitignored). Regenerate after proof
status changes or agent runs:

```bash
python3 scripts/reindex_graph.py
```

This runs:

1. `scripts/bootstrap_graph.py` — hand-maintained six-sorry DAG (no Lean decorators yet)
2. MathProver `scripts/index_runs.py --backfill` — run records from attempt logs
3. Merge `attemptsLog` / `activeAgent` into the graph

When Lean files gain `@paper-id` decorators, switch to decorator-driven indexing:

```bash
python3 scripts/reindex_graph.py --decorators
```

See [DECORATORS.md](DECORATORS.md) for tag syntax.

## Optional UI overlay

Copy `.mathprover/meta.json.example` → `.mathprover/meta.json` to supply foundations,
paper blocks, and term hover metadata. Node DAG still comes from bootstrap or
`build_graph.py`.

## Dispatch

```bash
cd "$MATHPROVER_HOME/agents" && uv sync

uv run python dispatch.py \
  --root /path/to/lean-runtime-analysis \
  --node L661_coea_sel_measure_prob \
  --prover auto
```

Node id: proof folder name under `proofs/`, graph id, or Lean theorem name.

## Reindex from MathProver UI

`POST /api/reindex?project=/path/to/this/repo` (MathProver dev server) calls the same
pipeline as `scripts/reindex_graph.py`.

## Independence checklist

- [x] No `agents/` or `mathprover-ui/` in this repo
- [x] `mathprover.toml` stays here (project-specific routing)
- [x] `scripts/bootstrap_graph.py` stays here (project-specific DAG)
- [x] Runtime artifacts under `.mathprover/` (gitignored)
- [x] MathProver resolved via `MATHPROVER_HOME` only
