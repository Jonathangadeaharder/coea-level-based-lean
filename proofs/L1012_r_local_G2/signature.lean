-- LBTCoupling.lean:998-1012 (with full preconditions)
lemma r_local_G2 {β : Type _} (n r : ℕ) (hn : n ≥ 2) (hr : r ≥ 1)
    (epsilon B C : ℝ) (h_eps : epsilon < 1 / (r : ℝ)) (hB : B > 0) (hC : C > 0) (K lambda_pop : ℕ)
    (hK : (K : ℝ) ≥ C * B^2 * (n : ℝ)^2 * ((1 - (r : ℝ) * epsilon)^2)⁻¹ * (Real.log (lambda_pop : ℝ) + Real.log (n : ℝ)))
    (G : RLocalGame (BitString n) β) :
    ConditionG2 (by omega : n + 1 > 0) lambda_pop (A_lvl n) (coea_sel_kernel G K lambda_pop) (1/4 : ℝ) (r_local_z n) := by
  intro j P c hc_pos hc_le
  sorry
