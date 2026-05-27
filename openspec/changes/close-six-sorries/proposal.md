## Why

Six `sorry` obligations in `LBTCoupling.lean` block the paper's mechanization claim. L703 (`mutation_prob_lower_bound`) is now proven; the remaining five lemmas form a dependency DAG ending at capstone `r_local_G2` (L1012). Parallel agent dispatch (Goedel for leaves, Aristotle for capstone) is wired — we need a coordinated closure plan with no new sorries in the main tree.

## What Changes

- Close L661, L669 (frontier leaves, parallel Goedel)
- Close L693, L715 (second wave after upstream)
- Close L1012 via Aristotle with full upstream context
- Merge each completed `proofs/<folder>/attempt.lean` into `LBTCoupling.lean`
- Update `.mathprover/graph.json` node status to PROVEN on each merge

## Capabilities

### New Capabilities
<!-- none — tracking existing capability closure -->

### Modified Capabilities
- `lean-proof-closure`: Update status table as lemmas close; enforce merge order

## Impact

- `LBTCoupling.lean` — six sorry replacements
- `proofs/*/` — worker folders, status.md, attempt.lean
- `.mathprover/graph.json` — node status updates
- [VidiomTM/mathprover](https://github.com/VidiomTM/mathprover) — dispatch UI reflects progress (external repo)

## Non-Goals

- Formalizing `level_based_theorem` (stays trusted axiom)
- Implementing the real best-of-λ kernel (L1012 may remain trusted sorry if placeholder kernel blocks proof)
- New paper theorems beyond the six sorries
