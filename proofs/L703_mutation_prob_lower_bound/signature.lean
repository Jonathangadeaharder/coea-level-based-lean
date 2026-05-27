-- File: LBTCoupling.lean, lines 700-703.
-- Signature copied verbatim. The proof body (replacing `sorry`) is the
-- worker deliverable.

lemma mutation_prob_lower_bound {n : ℕ} (hn : n ≥ 2) (x : BitString n) (j : ℕ) (hj : j < n)
    (hx : x ∈ A_ge (A_lvl n) j) :
    (parent_mut_measure x (A_ge (A_lvl n) (j + 1))).toReal ≥ 1 / (Real.exp 1 * n) := by
  sorry
