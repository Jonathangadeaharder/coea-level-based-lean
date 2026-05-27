state: in_progress
owner: goedel
depends_on: (none — independent leaf, but shares infrastructure with L669)
estimated_lines: 150–250
estimated_hours: 8–16

# Decomposition hints (if worker needs to split)

Potential children:
- `subproofs/level_cardinality/`     — `card {x : BitString n // hw(x) = w} = C(n, w)`.
- `subproofs/group_sum_by_weight/`   — `Σ_x f(hw(x)) · g(x) = Σ_w (Σ_{hw(x)=w} g(x)) · f(w)` for ENNReal.
- `subproofs/sel_cdf_top/`           — `sel_cdf(n+1) = 1`.
- `subproofs/sel_cdf_bot/`           — `sel_cdf(0) = 0` (for `lambda_pop ≥ 1`).
- `subproofs/cdf_telescope/`         — generic telescoping sum over `Fin (n+1)`.

# Coordination with L669
Both lemmas share the level-cardinality and group-sum-by-weight infrastructure.
If splitting, place those shared helpers in `proofs/_shared/` so the L669
worker can reuse them rather than re-deriving.

- [2026-05-27 16:00 UTC] goedel: failed — log `.mathprover/attempts/L661_coea_sel_measure_prob/20260527T160042Z.log` (ModuleNotFoundError: lean_pipeline — fixed in 5b1f11f)
- [2026-05-27 16:01 UTC] goedel: running — pass@4, 28K initial + 2×8K correction rounds; log `.mathprover/attempts/L661_coea_sel_measure_prob/20260527T160125Z.log`
