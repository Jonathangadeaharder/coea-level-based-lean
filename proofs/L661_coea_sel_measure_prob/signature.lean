-- LBTCoupling.lean:644-661
-- The selection measure is a probability measure: it integrates to 1.

lemma coea_sel_measure_prob {n : ℕ} (lambda_pop : ℕ)
    (P : Population (BitString n) lambda_pop) :
    coea_sel_measure lambda_pop P Set.univ = 1 := by
  dsimp [coea_sel_measure]
  split_ifs with h
  · simp [Measure.dirac_apply_of_mem (Set.mem_univ _)]
  · sorry
