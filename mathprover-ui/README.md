# MathProver — SvelteKit UI for the PhD project

Lean-backed proof workbench. Graph of paper theorems ⇄ Lean formalizations,
agent dispatch, premise picker, paper⇄Lean synced viewer, and a Foundations
view tracking mechanization progress of external results we depend on (e.g. the
Level-Based Theorem of Corus et al. 2018).

## Run

```bash
pnpm install
pnpm dev          # http://localhost:5173
# or pnpm build && pnpm preview
```

By default the UI loads the project at
`/Users/jonathangadeaharder/projects/phd/lean-runtime-analysis` — i.e. the
`.mathprover/graph.json` next to this `mathprover-ui/` directory.

Override at request time:

```
http://localhost:5173/workspace?project=/abs/path/to/another/project
```

Or at server start:

```bash
MATHPROVER_PROJECT_PATH=/abs/path pnpm dev
```

## The data contract

The UI is **stateless and project-agnostic**. All content (nodes, paper blocks,
Lean blocks, term lookup, foundations, failures) is read from
`<project-root>/.mathprover/graph.json` at request time by
`src/routes/+layout.server.ts` and pushed into the reactive store
(`src/lib/stores.svelte.ts`).

Schema is defined in `src/lib/types.ts` (`ProjectData`). Top-level fields:

| Field          | Type                    | Purpose                                                |
|----------------|-------------------------|--------------------------------------------------------|
| `project`      | `Project`               | name, paper, venue, capstone node id, lastVerified     |
| `recents`      | `RecentProject[]`       | Recent-projects list shown on the picker               |
| `nodes`        | `TheoremNode[]`         | Dependency DAG of paper claims ⇄ Lean theorems         |
| `foundations`  | `Foundation[]`          | External results + their mechanization decomposition   |
| `paperBlocks`  | `PaperBlock[]`          | Ordered content for the Paper⇄Lean viewer (paper side) |
| `leanBlocks`   | `LeanBlock[]`           | Ordered content for the Paper⇄Lean viewer (Lean side)  |
| `terms`        | `Record<name,TermInfo>` | Hover-popover metadata for Lean identifiers            |
| `failures`     | `Failure[]`             | Failure shelf (what didn't work)                       |
| `activeAgent`  | `LiveAgent \| null`     | Currently dispatched agent's live log                  |

Future indexer wiring: implement a `+server.ts` under `src/routes/api/` that
parses `paper/*.tex` `%@lean:` decorators and `lean/**/*.lean` `/-- @paper: -/`
decorators and emits `graph.json`. The UI does not change.

## Routes

- `/` — project picker
- `/workspace` — main workbench. Sidebar tabs:
  - **Graph** — pannable/zoomable DAG of all nodes
  - **Frontier** — ready-to-attempt leaves, ranked by importance × tractability
  - **Paper ⇄ Lean** — synced two-pane viewer (click on either side)
  - **Agent runs** — historic + live log of dispatch
  - **Failure shelf** — counterexample-first cards
  - **Foundations** — external dependencies (LBT, Hoeffding, drift theorems);
    each has a citation, mechanization status (Axiom / Partial / Mechanized /
    Planned), and a decomposition into subgoals with per-subgoal status and
    progress %.

## Connecting to a real backend

1. Replace the static `.mathprover/graph.json` with an indexer-generated one.
2. Implement SSE/WebSocket endpoint streaming agent logs; hook into
   `AgentView.svelte`.
3. Wire `RunAgentButton` → `POST /api/dispatch` with `{ nodeId, model, premises }`
   to your pydantic-ai service.

## Project layout MathProver opens

```
my_project/
├── mathprover.toml           # manifest + capstone (planned)
├── paper/
│   ├── main.tex              # with %@lean: decorators
│   └── sections/*.tex
├── lean/
│   ├── lakefile.toml
│   └── Project/
│       ├── Theorems/*.lean   # /-- @paper: Thm 5.4 -/
│       └── Axioms/*.lean
└── .mathprover/
    ├── graph.json            # what the UI loads
    ├── attempts/             # one git branch per attempt
    └── strategies.jsonl
```

## Status

UI prototype with file-backed data at
`<project-root>/.mathprover/graph.json`. Agent dispatch / mathlib retrieval /
git operations are stubbed; backend wiring is the next step.
