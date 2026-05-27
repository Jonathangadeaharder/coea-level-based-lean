## 1. Frontier (parallel)

- [x] 1.1 L703 — prove `mutation_prob_lower_bound`, merge to LBTCoupling.lean:935
- [ ] 1.2 L661 — Goedel/Aristotle on `coea_sel_measure_prob`; merge to :648
- [ ] 1.3 L669 — dispatch `coea_sel_measure_cdf`; merge to :661

## 2. Second wave

- [ ] 2.1 L715 — prove `coea_measure_ge_from_count` (needs L703 ✓); merge to :935
- [ ] 2.2 L693 — prove `sel_monotone_level` (needs L669); merge to :685

## 3. Capstone

- [ ] 3.1 L1012 — Aristotle dispatch on `r_local_G2` with L669 + L715 + `sel_amplification_bound` in context
- [ ] 3.2 Merge capstone or document trusted-sorry if kernel placeholder blocks

## 4. Verification

- [ ] 4.1 `lake build LBTCoupling` clean after each merge
- [ ] 4.2 `grep -rn 'sorry' LBTCoupling.lean` — only LBT axiom remains
- [ ] 4.3 Reindex graph: `python3 scripts/bootstrap_graph.py`
- [ ] 4.4 Archive change: `/opsx:archive close-six-sorries`
