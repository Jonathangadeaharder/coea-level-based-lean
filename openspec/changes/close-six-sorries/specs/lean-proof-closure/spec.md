## MODIFIED Requirements

### Requirement: Dependency DAG
The sorry closure order SHALL follow:

| ID | Lemma | Depends on | Status |
|----|-------|------------|--------|
| L703 | mutation_prob_lower_bound | — | **done** |
| L661 | coea_sel_measure_prob | — | **in progress** |
| L669 | coea_sel_measure_cdf | — | todo |
| L693 | sel_monotone_level | L669 | todo |
| L715 | coea_measure_ge_from_count | L703 | todo |
| L1012 | r_local_G2 | L669, L715 | todo (capstone) |

#### Scenario: L703 completed
- **WHEN** L703 merge verified by `lake build`
- **THEN** graph node `L703_mut_lb` status is PROVEN
- **AND** L715 becomes unblocked

#### Scenario: Active Goedel run on L661
- **WHEN** dispatch is running for L661
- **THEN** `status.md` is `in_progress`
- **AND** run record shows phase `generating` with heartbeats
