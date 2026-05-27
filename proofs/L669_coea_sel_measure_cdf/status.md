state: todo
owner: (unassigned)
depends_on: (shares infrastructure with L661 — coordinate via proofs/_shared/)
estimated_lines: 200–300
estimated_hours: 12–24

# Decomposition hints
Children likely overlap with L661:
- `subproofs/level_cardinality/`
- `subproofs/group_sum_by_weight/`
- `subproofs/sel_cdf_top/`            (sel_cdf(n+1) = 1)
- `subproofs/A_ge_partition/`         (A_ge(k) = ⊔_{w≥k} A_lvl(w))

If both L661 and L669 split out the cardinality and group-sum helpers, lift
them to `proofs/_shared/`.
