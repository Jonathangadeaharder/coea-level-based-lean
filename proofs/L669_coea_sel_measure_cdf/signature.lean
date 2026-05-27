-- LBTCoupling.lean:665-669
lemma coea_sel_measure_cdf {n : ℕ} (lambda_pop : ℕ)
    (P : Population (BitString n) lambda_pop) (k : ℕ) :
    coea_sel_measure lambda_pop P (A_ge (A_lvl n) k) =
    1 - (1 - coea_measure lambda_pop P (A_ge (A_lvl n) k)) ^ lambda_pop := by
  sorry
