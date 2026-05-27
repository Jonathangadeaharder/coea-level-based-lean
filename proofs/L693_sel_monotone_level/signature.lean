-- LBTCoupling.lean:689-693
lemma sel_monotone_level {n : ℕ} (lambda_pop : ℕ) (hl : lambda_pop ≠ 0)
    (P : Population (BitString n) lambda_pop) (j : ℕ) :
    (coea_sel_measure lambda_pop P (A_ge (A_lvl n) j)).toReal ≥
    (coea_measure lambda_pop P (A_ge (A_lvl n) j)).toReal := by
  sorry
