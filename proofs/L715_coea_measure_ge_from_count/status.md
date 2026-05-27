state: blocked
owner: (unassigned)
depends_on: L703_mutation_prob_lower_bound
estimated_lines: 80–150
estimated_hours: 4–8

# Decomposition hints
- `subproofs/restrict_sum_to_subset/`  — `Σ_{i ∈ univ} f i ≥ Σ_{i ∈ S} f i` for ENNReal sums.
- `subproofs/avg_lower_bound/`         — `λ^{-1} · (λ/4) · c = c/4` arithmetic.
