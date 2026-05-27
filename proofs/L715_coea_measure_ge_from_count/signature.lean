-- LBTCoupling.lean:709-715
lemma coea_measure_ge_from_count {n : ℕ} (hn : n ≥ 2) (lambda_pop : ℕ) (hl : lambda_pop > 0)
    (P : Population (BitString n) lambda_pop) (j : ℕ) (hj : j < n)
    (h_count : (Nat.card {i // P i ∈ A_ge (A_lvl n) j} : ℝ) ≥ (1 / 4 : ℝ) * lambda_pop) :
    (coea_measure lambda_pop P (A_ge (A_lvl n) (j + 1))).toReal ≥
    1 / (4 * Real.exp 1 * n) := by
  dsimp [coea_measure]
  sorry
