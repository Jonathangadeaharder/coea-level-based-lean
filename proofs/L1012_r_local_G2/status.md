state: blocked
owner: (unassigned)
depends_on: L669_coea_sel_measure_cdf, L715_coea_measure_ge_from_count (transitively L703)
estimated_lines: 100–200
estimated_hours: 6–10

# Decomposition hints
- `subproofs/z_j_specialization/`     — case split `j < n` vs `j = n`.
- `subproofs/amplification_inequality/` — adapt `sel_amplification_bound`'s inequality chain
  to parameterized `z_j` instead of fixed `1/n`.
