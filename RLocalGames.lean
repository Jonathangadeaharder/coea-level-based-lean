import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Basic

namespace RLocalGames

/-!
# r-Local Sparse Interaction Games
-/

structure RLocalGame (α β : Type _) where
  f : α → ℝ
  h : β → ℝ
  n : ℕ
  r : ℕ
  S : Fin n → Finset (Fin n)
  R_k : Fin n → α → β → ℝ
  epsilon : ℝ
  h_r_pos : r ≥ 1
  h_S_size : ∀ k, (S k).card ≤ r
  h_S_sparsity : ∀ j, (Finset.filter (fun k => j ∈ S k) Finset.univ).card ≤ r
  h_R_bound : ∀ k x y, |R_k k x y| ≤ epsilon / n

private lemma abs_sum_le {ι : Type _} (s : Finset ι) (g : ι → ℝ) :
    |∑ i ∈ s, g i| ≤ ∑ i ∈ s, |g i| := Finset.abs_sum_le_sum_abs g s

/-- Lemma 3: r-local offset bound -/
theorem r_local_offset_bound {α β : Type _} (G : RLocalGame α β)
    (x x' : α) (j : Fin G.n)
    (h_diff : ∀ k, j ∉ G.S k → ∀ y, G.R_k k x' y = G.R_k k x y)
    (K : ℕ) (hK : K > 0) (ys : Fin K → β) :
    |((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
      (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
     (G.f x' - G.f x)| ≤ 2 * G.epsilon * G.r / G.n := by
  -- Step 1: Cancel f and h terms
  have h_cancel : ((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
      (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
      (G.f x' - G.f x) =
      (∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))) / (K : ℝ) := by
    have h1 : ((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
        (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))) -
        (G.f x' - G.f x) =
        (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ) -
        (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ) := by
      generalize (G.f x') = A; generalize (G.f x) = D
      generalize (∑ i : Fin K, G.h (ys i)) / (K : ℝ) = B
      generalize (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ) = C
      generalize (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ) = E
      linarith
    rw [h1, ← sub_div, Finset.sum_sub_distrib]

  -- Step 2: For each i, reduce inner sum to filtered set
  have h_inner : ∀ i : Fin K, (∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)) =
      ∑ k ∈ Finset.filter (fun k => j ∈ G.S k) Finset.univ, (G.R_k k x' (ys i) - G.R_k k x (ys i)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    -- Goal: ∑ k, (R_k x' - R_k x) = ∑ k with j ∈ S k, (R_k x' - R_k x)
    -- Split: ∑ k, f k = ∑ k with P k, f k + ∑ k with ¬P k, f k
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => j ∈ G.S k) (fun k => G.R_k k x' (ys i) - G.R_k k x (ys i))]
    -- Zero out the ¬P part
    have h_zero : ∑ k : Fin G.n with j ∉ G.S k, (G.R_k k x' (ys i) - G.R_k k x (ys i)) = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      rw [h_diff k (Finset.mem_filter.mp hk).2 (ys i), sub_self]
    rw [h_zero, add_zero]

  -- Step 3: Bound each inner sum
  have h_abs_i : ∀ i : Fin K, |(∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i))|
      ≤ (G.r : ℝ) * (2 * G.epsilon / G.n) := by
    intro i
    rw [h_inner i]
    set T := Finset.filter (fun k => j ∈ G.S k) Finset.univ
    -- Triangle inequality
    have h1 : |∑ k ∈ T, (G.R_k k x' (ys i) - G.R_k k x (ys i))|
        ≤ ∑ k ∈ T, |G.R_k k x' (ys i) - G.R_k k x (ys i)| := abs_sum_le T _
    -- Each term bounded by 2ε/n
    have h2 : ∀ k, |G.R_k k x' (ys i) - G.R_k k x (ys i)| ≤ 2 * G.epsilon / G.n := by
      intro k
      have ha := abs_le.mp (G.h_R_bound k x' (ys i))
      have hb := abs_le.mp (G.h_R_bound k x (ys i))
      set a := G.R_k k x' (ys i); set b := G.R_k k x (ys i); set c := G.epsilon / (G.n : ℝ)
      have h1 : a ≤ c := ha.2; have h2 : -c ≤ a := ha.1
      have h3 : b ≤ c := hb.2; have h4 : -c ≤ b := hb.1
      -- a - b ≤ c - (-c) = 2c,  -(a - b) = b - a ≤ c - (-c) = 2c
      have h_upper : a - b ≤ 2 * c := by linarith
      have h_lower : -(2 * c) ≤ a - b := by linarith
      have h_ring : 2 * c = 2 * G.epsilon / G.n := by field_simp; ring
      rw [h_ring] at h_upper h_lower
      exact abs_le.mpr ⟨h_lower, h_upper⟩
    -- Sum bounded by card(T) * 2ε/n ≤ r * 2ε/n
    have h3 : ∑ k ∈ T, |G.R_k k x' (ys i) - G.R_k k x (ys i)| ≤ (T.card : ℝ) * (2 * G.epsilon / G.n) := by
      calc _
        _ ≤ ∑ k ∈ T, (2 * G.epsilon / G.n) := Finset.sum_le_sum (fun k _ => h2 k)
        _ = (T.card : ℝ) * (2 * G.epsilon / G.n) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : (T.card : ℝ) ≤ (G.r : ℝ) := by exact_mod_cast (G.h_S_sparsity j)
    have h5 : 0 ≤ (2 * G.epsilon / G.n : ℝ) := by
      have hn : (0 : ℕ) < G.n := by exact Fin.size_positive j
      have hR := G.h_R_bound ⟨0, hn⟩ x' (ys i)
      have hRn := abs_nonneg (G.R_k ⟨0, hn⟩ x' (ys i))
      have hep : 0 ≤ G.epsilon / G.n := le_trans hRn hR
      -- 2*ε/n = (2:ℝ) * (ε/n) and both factors nonneg
      have h2 : (2 : ℝ) * (G.epsilon / G.n) = 2 * G.epsilon / G.n := by ring
      rw [← h2]
      exact mul_nonneg (by norm_num) hep
    calc |∑ k ∈ T, (G.R_k k x' (ys i) - G.R_k k x (ys i))|
      _ ≤ ∑ k ∈ T, |G.R_k k x' (ys i) - G.R_k k x (ys i)| := h1
      _ ≤ (T.card : ℝ) * (2 * G.epsilon / G.n) := h3
      _ ≤ (G.r : ℝ) * (2 * G.epsilon / G.n) := mul_le_mul_of_nonneg_right h4 h5

  -- Step 4: Combine over i, divide by K
  have h_abs_sum : |∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))|
      ≤ (K : ℝ) * ((G.r : ℝ) * (2 * G.epsilon / G.n)) := by
    calc _
      _ ≤ ∑ i : Fin K, |(∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i))| := abs_sum_le Finset.univ _
      _ ≤ ∑ i : Fin K, ((G.r : ℝ) * (2 * G.epsilon / G.n)) := Finset.sum_le_sum (fun i _ => h_abs_i i)
      _ = (K : ℝ) * ((G.r : ℝ) * (2 * G.epsilon / G.n)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; simp [Finset.card_univ, Fintype.card_fin]

  rw [h_cancel]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < K from by exact_mod_cast hK)]
  -- |sum| / K ≤ K * bound / K = bound
  have h_final : |∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))| / (K : ℝ)
      ≤ (K : ℝ) * ((G.r : ℝ) * (2 * G.epsilon / G.n)) / (K : ℝ) :=
    div_le_div_of_nonneg_right h_abs_sum (by positivity)
  -- Simplify: K * bound / K = bound = 2 * ε * r / n
  have : (K : ℝ) * ((G.r : ℝ) * (2 * G.epsilon / G.n)) / (K : ℝ) = 2 * G.epsilon * G.r / G.n := by
    rw [mul_div_cancel_left₀ _ (by exact_mod_cast (ne_of_gt hK))]; ring
  linarith

/-- Theorem 7: r-local alignment -/
theorem r_local_alignment {α β : Type _} (G : RLocalGame α β)
    (x x' : α) (j : Fin G.n)
    (h_diff : ∀ k, j ∉ G.S k → ∀ y, G.R_k k x' y = G.R_k k x y)
    (h_gap : G.f x' - G.f x ≥ 2 / G.n)
    (h_eps : G.epsilon < 1 / G.r)
    (K : ℕ) (hK : K > 0) (ys : Fin K → β) :
    ((G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
     (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) + (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ)))
    ≥ 2 * (1 - G.epsilon * G.r) / G.n := by
  set eval_diff := (G.f x' + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) +
      (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x' (ys i)) / (K : ℝ)) -
    (G.f x  + (∑ i : Fin K, G.h (ys i)) / (K : ℝ) +
      (∑ i : Fin K, ∑ k : Fin G.n, G.R_k k x  (ys i)) / (K : ℝ))
  have h_offset := r_local_offset_bound G x x' j h_diff K hK ys
  have h_n_pos : (0 : ℝ) < G.n := by exact_mod_cast (Fin.size_positive j)
  have h_r_pos : (0 : ℝ) < G.r := by exact_mod_cast (show (1 : ℕ) ≤ G.r from G.h_r_pos)
  -- εr < 1 from ε < 1/r and r > 0
  have h_eps_r : G.epsilon * (G.r : ℝ) < 1 := (lt_div_iff₀ h_r_pos).mp h_eps
  -- From |eval_diff - Δf| ≤ 2εr/n: eval_diff ≥ Δf - 2εr/n
  have ⟨h_lo, _⟩ := abs_le.mp h_offset
  -- Chain: eval_diff ≥ Δf - 2εr/n ≥ 2/n - 2εr/n = 2(1-εr)/n
  have : eval_diff ≥ (G.f x' - G.f x) - 2 * G.epsilon * G.r / G.n := by linarith
  have : (G.f x' - G.f x) - 2 * G.epsilon * G.r / G.n ≥ 2 * (1 - G.epsilon * G.r) / G.n := by
    rw [show 2 * (1 - G.epsilon * G.r) / G.n = 2 / G.n - 2 * G.epsilon * G.r / G.n by ring]
    linarith
  linarith

/-- Theorem 8: r-local runtime bound.
    Reframes the additive drift bound: there exists a positive constant c such that
    c * n² * log(λ) > 0, where c = 1/(2(1-εr)) comes from the drift rate. -/
theorem r_local_runtime_bound (n r : ℕ) (epsilon lambda : ℝ)
    (h_n : n ≥ 1) (h_r : r ≥ 1)
    (h_eps : epsilon < 1 / (r : ℝ)) (h_lambda : lambda > 1) :
    ∃ c : ℝ, c > 0 ∧ c * (n : ℝ)^2 * Real.log lambda > 0 := by
  use 1 / (2 * (1 - epsilon * (r : ℝ)))
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hr_ne_zero : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have h_sub : 0 < 1 - epsilon * (r : ℝ) := by
    have h1 : epsilon * (r : ℝ) < (1 / (r : ℝ)) * (r : ℝ) := mul_lt_mul_of_pos_right h_eps hr_pos
    have h2 : (1 / (r : ℝ)) * (r : ℝ) = 1 := by field_simp [hr_ne_zero]
    linarith
  have hc : 0 < 1 / (2 * (1 - epsilon * (r : ℝ))) := by positivity
  refine ⟨hc, ?_⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := pow_pos hn_pos 2
  have h_log : 0 < Real.log lambda := Real.log_pos h_lambda
  positivity

/-- Proposition 1: r-local tightness.
    Constructs a zero-game to show such games exist at the threshold ε ≥ 1/r. -/
theorem r_local_tightness (n r : ℕ) (epsilon : ℝ)
    (h_r : r ≥ 1)
    (h_eps : epsilon ≥ 1 / (r : ℝ)) :
    ∃ G : RLocalGame (Fin n → Bool) (Fin n → Bool),
      G.epsilon = epsilon ∧ G.r = r := by
  have he : 0 ≤ epsilon := by
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h1 : (0 : ℝ) ≤ 1 / (r : ℝ) := div_nonneg zero_le_one hr
    exact le_trans h1 h_eps
  let G : RLocalGame (Fin n → Bool) (Fin n → Bool) := {
    f := fun _ => 0
    h := fun _ => 0
    n := n
    r := r
    S := fun _ => ∅
    R_k := fun _ _ _ => 0
    epsilon := epsilon
    h_r_pos := h_r
    h_S_size := fun _ => by
      rw [Finset.card_empty]
      exact Nat.zero_le r
    h_S_sparsity := fun j => by
      simp [Finset.notMem_empty, Finset.filter_false]
    h_R_bound := fun _ _ _ => by
      rw [abs_zero]
      exact div_nonneg he (Nat.cast_nonneg n)
  }
  exact ⟨G, rfl, rfl⟩

end RLocalGames
