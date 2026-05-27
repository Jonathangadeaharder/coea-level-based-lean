## Context

PhD project formalizing selection/mutation coupling for level-based runtime analysis. `LBTCoupling.lean` has six sorries; proof work happens in isolated `proofs/<folder>/` trees with agent assistance. OpenSpec tracks the closure epic; MathProver UI visualizes the DAG.

Current state (2026-05-27):
- L703: **done** (merged, `lake build` passes)
- L661: **in progress** (Goedel pass@4 running)
- L669, L693, L715, L1012: **todo**

## Goals / Non-Goals

**Goals:**
- Zero sorries in `LBTCoupling.lean` except LBT axiom
- Translate proofs from `paper_source.md`, never invent
- Maximize parallelism: L661 ∥ L669, then L693 ∥ L715, then L1012
- Use Goedel for leaves; Aristotle for L1012 capstone

**Non-Goals:**
- Refactoring unrelated Lean modules
- Changing Mathlib pin without cause

## Decisions

1. **Worker folders over inline sorry** — All attempt work in `proofs/`; merge only when `status.md: done`.
2. **Split not sorry** — Stuck workers create `subproofs/` children; never leave bare sorry in merge candidates.
3. **Goedel first, Aristotle escalate** — Per `mathprover.toml`: 3 failures → Aristotle; capstone always Aristotle.
4. **Paper-id decorators deferred** — `build_graph.py` finds 0 decorated nodes; use `bootstrap_graph.py` until decorators added to LBTCoupling.
5. **OpenSpec as coordinator** — `proofs/PLAN.md` remains worker quick-ref; OpenSpec change `close-six-sorries` is canonical for agents.

## Risks / Trade-offs

| Risk | Mitigation |
|------|------------|
| L1012 blocked by placeholder kernel | Document as trusted sorry; spec allows intentional preservation |
| Goedel long runs (28K tokens) | Streaming heartbeats + UI progress (done) |
| L661/L669 shared infrastructure | Extract shared helpers to `proofs/_shared/` if split |
