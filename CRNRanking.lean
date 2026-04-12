import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CRNRanking

/-!
# Common Random Numbers (CRN) Ranking Theorems
-/

-- ============================================================
-- PART 1: Separable Game CRN (Theorem 4)
-- ============================================================

structure SeparableGameCRN (α β : Type _) where
  f : α → ℝ
  h : β → ℝ

noncomputable def crnEstimator {α β : Type _} (G : SeparableGameCRN α β)
    (x : α) (ys : Fin K → β) : ℝ :=
  G.f x + (∑ i : Fin K, G.h (ys i)) / K

theorem crn_exact_ranking_separable {α β : Type _}
    (G : SeparableGameCRN α β)
    (x x' : α)
    {K : ℕ} (hK : K > 0)
    (ys : Fin K → β) :
    crnEstimator G x' ys - crnEstimator G x ys = G.f x' - G.f x := by
  unfold crnEstimator
  ring

-- ============================================================
-- PART 2: ε-Separable Game CRN (Theorem 5)
-- ============================================================

structure EpsSeparableGameCRN (α β : Type _) where
  f : α → ℝ
  h : β → ℝ
  R : α → β → ℝ
  epsilon : ℝ
  h_eps_nonneg : epsilon ≥ 0
  h_residual_bound : ∀ x y, |R x y| ≤ epsilon

noncomputable def epsCrnEstimator {α β : Type _} (G : EpsSeparableGameCRN α β)
    (x : α) (ys : Fin K → β) : ℝ :=
  G.f x + (∑ i : Fin K, G.h (ys i)) / K + (∑ i : Fin K, G.R x (ys i)) / K

theorem crn_eps_separable_ranking {α β : Type _}
    (G : EpsSeparableGameCRN α β)
    (x x' : α)
    {n K : ℕ} (hK : K > 0)
    (delta epsilon : ℝ)
    (h_gap : G.f x' - G.f x ≥ delta)
    (h_delta : delta = 2 / (n : ℝ))
    (h_eps : epsilon < 1 / (n : ℝ))
    (h_res_bound : ∀ x y, |G.R x y| ≤ epsilon)
    (ys : Fin K → β) :
    epsCrnEstimator G x' ys - epsCrnEstimator G x ys ≥ 2 * (1 - (n : ℝ) * epsilon) / (n : ℝ) := by
  have hn_pos : (n : ℝ) ≠ 0 := by
    intro h
    have he : epsilon < 0 := by
      calc epsilon < 1 / (n : ℝ) := h_eps
        _ = 1 / 0 := by rw [h]
        _ = 0 := div_zero 1
    have hy : β := ys ⟨0, hK⟩
    have h_abs := h_res_bound x hy
    have h_abs_nonneg : 0 ≤ |G.R x hy| := abs_nonneg (G.R x hy)
    linarith
  have h_rhs : 2 / (n : ℝ) - 2 * epsilon = 2 * (1 - (n : ℝ) * epsilon) / (n : ℝ) := by
    calc 2 / (n : ℝ) - 2 * epsilon
      _ = 2 / (n : ℝ) - (2 * epsilon * (n : ℝ)) / (n : ℝ) := by rw [mul_div_cancel_right₀ (2 * epsilon) hn_pos]
      _ = (2 - 2 * epsilon * (n : ℝ)) / (n : ℝ) := by rw [← sub_div]
      _ = 2 * (1 - (n : ℝ) * epsilon) / (n : ℝ) := by ring
  have h_res_diff : ∀ i : Fin K,
      G.R x' (ys i) - G.R x (ys i) ≥ -2 * epsilon := by
    intro i
    have h1 := h_res_bound x' (ys i)
    have h2 := h_res_bound x (ys i)
    linarith [abs_le.mp h1, abs_le.mp h2]
  have h_sum_res : (∑ i : Fin K, G.R x' (ys i)) / K - (∑ i : Fin K, G.R x (ys i)) / K ≥ -2 * epsilon := by
    have h_sum : (∑ i : Fin K, (G.R x' (ys i) - G.R x (ys i))) / K ≥ -2 * epsilon := by
      calc (∑ i : Fin K, (G.R x' (ys i) - G.R x (ys i))) / K
        _ ≥ (∑ i : Fin K, (-2 * epsilon)) / K := by
          apply div_le_div_of_nonneg_right
          · exact Finset.sum_le_sum (fun i _ => h_res_diff i)
          · positivity
        _ = -2 * epsilon := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hK_neq : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
          calc (↑K * (-2 * epsilon)) / ↑K
            _ = (↑K / ↑K) * (-2 * epsilon) := by ring
            _ = 1 * (-2 * epsilon) := by rw [div_self hK_neq]
            _ = -2 * epsilon := by ring
    have hd : (∑ i : Fin K, (G.R x' (ys i) - G.R x (ys i))) / K = (∑ i : Fin K, G.R x' (ys i)) / K - (∑ i : Fin K, G.R x (ys i)) / K := by
      rw [Finset.sum_sub_distrib]
      ring
    rwa [hd] at h_sum
  have hd2 : epsCrnEstimator G x' ys - epsCrnEstimator G x ys = (G.f x' - G.f x) + ((∑ i : Fin K, G.R x' (ys i)) / K - (∑ i : Fin K, G.R x (ys i)) / K) := by
    unfold epsCrnEstimator
    ring
  rw [hd2, ← h_rhs]
  rw [h_delta] at h_gap
  linarith

end CRNRanking