## Purpose

Track closure of the six `sorry` obligations in `LBTCoupling.lean` via isolated proof folders, worker contract, and merge ordering.

## Requirements

### Requirement: Six-sorry closure target
The project SHALL close all six `sorry` obligations in `LBTCoupling.lean` while preserving exactly one trusted external axiom (`level_based_theorem`).

#### Scenario: Final verification
- **WHEN** all proof work is complete
- **THEN** `grep sorry LBTCoupling.lean` finds zero matches except the documented LBT axiom block
- **AND** `lake build LBTCoupling` succeeds

### Requirement: No new sorries in main tree
Workers SHALL NOT add new `sorry` to any file outside `proofs/` scratch folders.

#### Scenario: Stuck worker splits instead of sorrying
- **WHEN** a worker cannot complete a proof within the time box
- **THEN** they create `proofs/<folder>/subproofs/<child>/` with the same five-file layout
- **AND** parent `status.md` is set to `split`
- **AND** no bare `sorry` remains in the parent `attempt.lean` intended for merge

### Requirement: Proof folder contract
Each active sorry SHALL have a folder under `proofs/` containing `signature.lean`, `paper_source.md`, `attempt.lean`, and `status.md`.

#### Scenario: Worker picks up a leaf
- **WHEN** a folder has `state: todo` and all dependencies are `done`
- **THEN** it is eligible for agent dispatch
- **AND** `paper_source.md` contains the human proof to translate (not invent)

### Requirement: Merge order respects DAG
Proofs SHALL merge into `LBTCoupling.lean` only after their `depends_on` nodes are proven.

#### Scenario: Second-wave merge blocked
- **WHEN** L693 or L715 is ready but L669 or L703 is not done
- **THEN** merge MUST NOT proceed for the dependent lemma

### Requirement: Dependency DAG
The sorry closure order SHALL follow:

| ID | Lemma | Depends on | Status |
|----|-------|------------|--------|
| L703 | mutation_prob_lower_bound | — | done |
| L661 | coea_sel_measure_prob | — | in progress |
| L669 | coea_sel_measure_cdf | — | todo |
| L693 | sel_monotone_level | L669 | todo |
| L715 | coea_measure_ge_from_count | L703 | todo |
| L1012 | r_local_G2 | L669, L715 | todo (capstone) |

#### Scenario: Frontier identification
- **WHEN** coordinator scans proof folders
- **THEN** L661 and L669 are reported as parallel frontier leaves
- **AND** L1012 is reported as capstone requiring Aristotle after escalation
