import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Basic
import RLocalGames

open RLocalGames

theorem r_local_offset_bound_proof {α β : Type _} (G : RLocalGame α β)
    (x x' : α) (j : Fin G.n)
    (h_diff : ∀ k, j ∉ G.S k → ∀ y, G.R_k k x' y = G.R_k k x y)
    (K : ℕ) (hK : K > 0) (ys : Fin K → β) :
    |((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
      (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
     (G.f x' - G.f x)| ≤ 2 * G.epsilon * G.r / G.n := by
  have h_cancel : ((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
                   (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
                  (G.f x' - G.f x) =
                  (∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))) / (K : ℝ) := by
    have h1 : ((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
               (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
              (G.f x' - G.f x) = (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ) - (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i)) / (K : ℝ) := by
      generalize (G.f x') = A
      generalize (G.f x) = D
      generalize (∑ i : Fin K, G.h (ys i)) / (K : ℝ) = B
      generalize (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ) = C
      generalize (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i)) / (K : ℝ) = E
      linarith
    have h2 : (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ) - (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i)) / (K : ℝ) =
              ((∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i))) / (K : ℝ) := by rw [← sub_div]
    have h3 : ((∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i))) / (K : ℝ) =
              (∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))) / (K : ℝ) := by
      have h_sub : (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x (ys i)) =
                   (∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))) := by
        rw [← Finset.sum_sub_distrib]
      rw [h_sub]
    rw [h1, h2, h3]
  rw [h_cancel]
  have h_inner : ∀ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i) =
                              ∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i)) := by
    intro i
    have h_sub_sum : (∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i)) = ∑ k : Fin G.n, (G.R_k k x' (ys i) - G.R_k k x (ys i)) := by
      rw [← Finset.sum_sub_distrib]
    rw [h_sub_sum]
    have h_split : (∑ k : Fin G.n, (G.R_k k x' (ys i) - G.R_k k x (ys i))) =
                   (∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i))) +
                   (∑ k ∈ Finset.filter (fun k => j ∉ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i))) := by
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => j ∈ G.S k) _).symm
    rw [h_split]
    have h_zero : (∑ k ∈ Finset.filter (fun k => j ∉ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk2 : j ∉ G.S k := (Finset.mem_filter.mp hk).2
      rw [h_diff k hk2 (ys i)]
      exact sub_self _
    rw [h_zero, add_zero]
  have h_abs_inner : ∀ i : Fin K, |∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i)| ≤ 2 * G.epsilon * G.r / G.n := by
    intro i
    rw [h_inner i]
    have h_tri : |∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i))| ≤
                 ∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, |G.R_k k x' (ys i) - G.R_k k x (ys i)| := Finset.abs_sum_le_sum_abs _ _
    have h_term : ∀ k, |G.R_k k x' (ys i) - G.R_k k x (ys i)| ≤ 2 * G.epsilon / G.n := by
      intro k
      have hb1 := abs_le.mp (G.h_R_bound k x' (ys i))
      have hb2 := abs_le.mp (G.h_R_bound k x (ys i))
      have ht1 : G.R_k k x' (ys i) - G.R_k k x (ys i) ≤ 2 * G.epsilon / G.n := by linarith
      have ht2 : -(G.R_k k x' (ys i) - G.R_k k x (ys i)) ≤ 2 * G.epsilon / G.n := by linarith
      exact abs_le.mpr ⟨by linarith, ht1⟩
    have h_sum_bound : (∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, |G.R_k k x' (ys i) - G.R_k k x (ys i)|) ≤
                       ((Finset.filter (fun k => j ∈ G.S k) Finset.univ).card : ℝ) * (2 * G.epsilon / G.n) := by
      have hs : (∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, |G.R_k k x' (ys i) - G.R_k k x (ys i)|) ≤
                ∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (2 * G.epsilon / G.n) := Finset.sum_le_sum (fun k _ => h_term k)
      have heq : (∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (2 * G.epsilon / G.n)) = ((Finset.filter (fun k => j ∈ G.S k) Finset.univ).card : ℝ) * (2 * G.epsilon / G.n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith
    have h_card_bound : ((Finset.filter (fun k => j ∈ G.S k) Finset.univ).card : ℝ) ≤ (G.r : ℝ) := by
      exact_mod_cast (G.h_S_sparsity j)
    have h_ep_n_pos : 0 ≤ 2 * G.epsilon / G.n := by
      have hk_inst : Fin G.n := ⟨0, by omega⟩
      have hkys : β := ys ⟨0, by omega⟩
      have hb1 : |G.R_k hk_inst x' hkys| ≤ G.epsilon / G.n := G.h_R_bound hk_inst x' hkys
      have hb1_pos : 0 ≤ |G.R_k hk_inst x' hkys| := abs_nonneg _
      have h_fin : 0 ≤ G.epsilon / G.n := le_trans hb1_pos hb1
      linarith
    have h_prod_bound : ((Finset.filter (fun k => j ∈ G.S k) Finset.univ).card : ℝ) * (2 * G.epsilon / G.n) ≤ (G.r : ℝ) * (2 * G.epsilon / G.n) := mul_le_mul_of_nonneg_right h_card_bound h_ep_n_pos
    calc |∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i))|
      _ ≤ (∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, |G.R_k k x' (ys i) - G.R_k k x (ys i)|) := h_tri
      _ ≤ ((Finset.filter (fun k => j ∈ G.S k) Finset.univ).card : ℝ) * (2 * G.epsilon / G.n) := h_sum_bound
      _ ≤ (G.r : ℝ) * (2 * G.epsilon / G.n) := h_prod_bound
      _ = 2 * G.epsilon * G.r / G.n := by ring
  have h_abs_sum : |(∑ i : Fin K, (∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i))) / (K : ℝ)| ≤ 2 * G.epsilon * G.r / G.n := by
    have h_div_le : |(∑ i : Fin K, (∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i))) / (K : ℝ)| ≤ (∑ i : Fin K, |∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i)|) / (K : ℝ) := by
      rw [abs_div, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    have h_sum_le2 : (∑ i : Fin K, |∑ k : Fin G.n, G.R_k k x' (ys i) - ∑ k : Fin G.n, G.R_k k x (ys i)|) / (K : ℝ) ≤ (∑ i : Fin K, 2 * G.epsilon * G.r / G.n) / (K : ℝ) := by
      apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h_abs_inner i)) (by positivity)
    have hc : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
    have h_eq : (∑ i : Fin K, 2 * G.epsilon * ↑G.r / ↑G.n) / (K : ℝ) = 2 * G.epsilon * G.r / G.n := by
      have hs : (∑ i : Fin K, 2 * G.epsilon * ↑G.r / ↑G.n) = ((K : ℝ) * (2 * G.epsilon * ↑G.r / ↑G.n)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        have hns : ((Finset.univ : Finset (Fin K)).card : ℝ) = (K : ℝ) := by simp
        rw [nsmul_eq_mul]
        congr 1
        exact_mod_cast rfl
      rw [hs]
      calc ((K : ℝ) * (2 * G.epsilon * ↑G.r / ↑G.n)) / (K : ℝ)
        _ = (K : ℝ) / (K : ℝ) * (2 * G.epsilon * ↑G.r / ↑G.n) := by ring
        _ = 1 * (2 * G.epsilon * ↑G.r / ↑G.n) := by rw [div_self hc]
        _ = 2 * G.epsilon * ↑G.r / ↑G.n := by ring
    linarith
  exact h_abs_sum
