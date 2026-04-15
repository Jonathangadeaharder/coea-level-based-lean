import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic

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
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => j ∈ G.S k) (fun k => G.R_k k x' (ys i) - G.R_k k x (ys i))]
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
    have h1 : |∑ k ∈ T, (G.R_k k x' (ys i) - G.R_k k x (ys i))|
        ≤ ∑ k ∈ T, |G.R_k k x' (ys i) - G.R_k k x (ys i)| := abs_sum_le T _
    have h2 : ∀ k, |G.R_k k x' (ys i) - G.R_k k x (ys i)| ≤ 2 * G.epsilon / G.n := by
      intro k
      have ha := abs_le.mp (G.h_R_bound k x' (ys i))
      have hb := abs_le.mp (G.h_R_bound k x (ys i))
      set a := G.R_k k x' (ys i); set b := G.R_k k x (ys i); set c := G.epsilon / (G.n : ℝ)
      have h1 : a ≤ c := ha.2; have h2 : -c ≤ a := ha.1
      have h3 : b ≤ c := hb.2; have h4 : -c ≤ b := hb.1
      have h_upper : a - b ≤ 2 * c := by linarith
      have h_lower : -(2 * c) ≤ a - b := by linarith
      have h_ring : 2 * c = 2 * G.epsilon / G.n := by field_simp; ring
      rw [h_ring] at h_upper h_lower
      exact abs_le.mpr ⟨h_lower, h_upper⟩
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
  have h_final : |∑ i : Fin K, ((∑ k : Fin G.n, G.R_k k x' (ys i)) - (∑ k : Fin G.n, G.R_k k x (ys i)))| / (K : ℝ)
      ≤ (K : ℝ) * ((G.r : ℝ) * (2 * G.epsilon / G.n)) / (K : ℝ) :=
    div_le_div_of_nonneg_right h_abs_sum (by positivity)
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
  have h_eps_r : G.epsilon * (G.r : ℝ) < 1 := (lt_div_iff₀ h_r_pos).mp h_eps
  have ⟨h_lo, _⟩ := abs_le.mp h_offset
  have : eval_diff ≥ (G.f x' - G.f x) - 2 * G.epsilon * G.r / G.n := by linarith
  have : (G.f x' - G.f x) - 2 * G.epsilon * G.r / G.n ≥ 2 * (1 - G.epsilon * G.r) / G.n := by
    rw [show 2 * (1 - G.epsilon * G.r) / G.n = 2 / G.n - 2 * G.epsilon * G.r / G.n by ring]
    linarith
  linarith

/-- **[PRECONDITION ONLY]** Theorem 8 (precondition): r-local drift constant positivity.
    Proves the core algebraic fact that the drift constant c = 1/(2(1-εr)) > 0.
    The full runtime bound E[T_X] = O(n log n) requires coupling with the
    Level-Based Theorem (Corus et al. 2018), which is not formalized here. -/
theorem r_local_drift_constant_positivity (n r : ℕ) (epsilon lambda : ℝ)
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

/-- Proposition 1 (existence part): an r-local game exists at any ε ≥ 1/r.
    The full cyclic adversarial trap is proved in `r_local_tightness_all_pairs_misranked`. -/
theorem r_local_game_exists_at_threshold (n r : ℕ) (epsilon : ℝ)
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

/-! ## Proposition 1: Cyclic adversarial trap (full mechanization)

At ε = c/r with c > 1, a cyclic r-local game exists that misranks
all n progression pairs from 0^n under the batch-mean evaluator.
-/

/-- Cyclic index set S_k = {k, k+1 mod n, ..., k+r-1 mod n}.
    Uses Fin.castLE to embed Fin r → Fin n (replacing the former `widen`). -/
private def cyclicSet (n r : ℕ) (k : Fin n) (hr : r ≤ n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin r)).image fun m => k + Fin.castLE hr m

/-- Key lemma: k + a ≡ k + b (mod n) → a = b for a, b < n.
    Uses the additive cancellation property of Fin n. -/
private lemma mod_add_right_cancel {a b k n : ℕ} (hk : k < n) (ha : a < n) (hb : b < n)
    (h : (k + a) % n = (k + b) % n) : a = b := by
  have h1 : (⟨k, hk⟩ + ⟨a, ha⟩ : Fin n) = (⟨k, hk⟩ + ⟨b, hb⟩ : Fin n) := Fin.ext h
  exact Fin.ext_iff.mp (add_left_cancel h1)

private theorem cyclicSet_card (n r : ℕ) (k : Fin n) (hr : r ≤ n) :
    (cyclicSet n r k hr).card = r := by
  have h_inj : Function.Injective fun m : Fin r => k + Fin.castLE hr m := by
    intro a b hab
    have h := congr_arg Fin.val hab
    simp only [Fin.val_add, Fin.castLE] at h
    exact Fin.ext (mod_add_right_cancel k.2
      (Nat.lt_of_lt_of_le a.2 hr) (Nat.lt_of_lt_of_le b.2 hr) h)
  unfold cyclicSet
  rw [Finset.card_image_of_injective Finset.univ h_inj]
  simp [Finset.card_univ, Fintype.card_fin]

private theorem cyclicSet_mem_iff (n r : ℕ) (k j : Fin n) (hr : r ≤ n) :
    j ∈ cyclicSet n r k hr ↔ ∃ m : Fin r, j = k + Fin.castLE hr m := by
  unfold cyclicSet; simp [Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

/-- Each j belongs to exactly r cyclic sets (sparsity with equality).
    Proved by showing {k : j ∈ S_k} equals the backward image {j - castLE m | m < r}. -/
private theorem cyclicSet_sparsity_count (n r : ℕ) (j : Fin n) (hr : r ≤ n) :
    (Finset.univ.filter (fun k => j ∈ cyclicSet n r k hr)).card = r := by
  -- Build the backward image: {j - Fin.castLE hr m | m ∈ Fin r}
  let f_back := fun m : Fin r => j - Fin.castLE hr m
  have h_back_inj : Function.Injective f_back := by
    intro a b hab
    have h := congr_arg Fin.val hab
    simp only [f_back, Fin.val_sub, Fin.castLE] at h
    -- (n - a + j) % n = (n - b + j) % n
    have ha_mod : (n - (a : ℕ) + j) % n = if n ≤ n - a + j then n - a + j - n else n - a + j := by
      split_ifs with ha_sub
      · rw [Nat.mod_eq_sub_mod ha_sub, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    have hb_mod : (n - (b : ℕ) + j) % n = if n ≤ n - b + j then n - b + j - n else n - b + j := by
      split_ifs with hb_sub
      · rw [Nat.mod_eq_sub_mod hb_sub, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    rw [ha_mod, hb_mod] at h
    split_ifs at h <;> omega
  -- Backward image has size r (by injectivity)
  have h_back_card : (Finset.univ.image f_back).card = r := by
    rw [Finset.card_image_of_injective Finset.univ h_back_inj]
    simp [Finset.card_univ, Fintype.card_fin]
  have h_back_eq : Finset.univ.image f_back = Finset.univ.filter (fun k => j ∈ cyclicSet n r k hr) := by
    ext k_var
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
               cyclicSet_mem_iff]
    constructor
    · rintro ⟨m, hm⟩
      use m
      show j = k_var + Fin.castLE hr m
      rw [← hm]
      exact Fin.ext_iff.mpr (by
        simp only [Fin.val_add, Fin.val_sub, Fin.castLE]
        show (j : ℕ) = ((n - (m : ℕ) + (j : ℕ)) % n + (m : ℕ)) % n
        have hm_val : (m : ℕ) < n := Nat.lt_of_lt_of_le m.2 hr
        have hj_lt : (j : ℕ) < n := j.2
        by_cases h_overflow : (n - (m : ℕ) + (j : ℕ)) < n
        · have h_mod : (n - (m : ℕ) + (j : ℕ)) % n = n - (m : ℕ) + (j : ℕ) := Nat.mod_eq_of_lt h_overflow
          rw [h_mod]
          have h_add : n - (m : ℕ) + (j : ℕ) + (m : ℕ) = n + (j : ℕ) := by omega
          rw [h_add]
          have h_n_le : n ≤ n + (j : ℕ) := by omega
          have h_mod2 : (n + (j : ℕ)) % n = (n + (j : ℕ) - n) % n := Nat.mod_eq_sub_mod h_n_le
          rw [h_mod2]
          have h_sub : n + (j : ℕ) - n = (j : ℕ) := by omega
          rw [h_sub, Nat.mod_eq_of_lt hj_lt]
        · have h_n_le : n ≤ n - (m : ℕ) + (j : ℕ) := by omega
          have h_mod : (n - (m : ℕ) + (j : ℕ)) % n = (n - (m : ℕ) + (j : ℕ) - n) % n := Nat.mod_eq_sub_mod h_n_le
          rw [h_mod]
          have h_lt : n - (m : ℕ) + (j : ℕ) - n < n := by omega
          have h_mod2 : (n - (m : ℕ) + (j : ℕ) - n) % n = n - (m : ℕ) + (j : ℕ) - n := Nat.mod_eq_of_lt h_lt
          rw [h_mod2]
          have h_add : n - (m : ℕ) + (j : ℕ) - n + (m : ℕ) = (j : ℕ) := by omega
          rw [h_add, Nat.mod_eq_of_lt hj_lt])
    · rintro ⟨m, hm'⟩
      use m
      show f_back m = k_var
      simp only [f_back]
      exact Fin.ext_iff.mpr (by
        simp only [Fin.val_sub, Fin.castLE]
        show (n - (m : ℕ) + (j : ℕ)) % n = (k_var : ℕ)
        have hm_val : (m : ℕ) < n := Nat.lt_of_lt_of_le m.2 hr
        have hk_lt : (k_var : ℕ) < n := k_var.2
        have hj_val : (j : ℕ) = ((k_var : ℕ) + (m : ℕ)) % n := by
          rw [Fin.ext_iff, Fin.val_add, Fin.castLE] at hm'; exact hm'
        by_cases h_add : (k_var : ℕ) + (m : ℕ) < n
        · have h_mod : ((k_var : ℕ) + (m : ℕ)) % n = (k_var : ℕ) + (m : ℕ) := Nat.mod_eq_of_lt h_add
          have hj_eq : (j : ℕ) = (k_var : ℕ) + (m : ℕ) := by
            rw [hj_val, h_mod]
          rw [hj_eq]
          have h_inner : n - (m : ℕ) + ((k_var : ℕ) + (m : ℕ)) = n + (k_var : ℕ) := by omega
          rw [h_inner]
          have h_n_le : n ≤ n + (k_var : ℕ) := by omega
          have h_mod2 : (n + (k_var : ℕ)) % n = (n + (k_var : ℕ) - n) % n := Nat.mod_eq_sub_mod h_n_le
          rw [h_mod2]
          have h_sub : n + (k_var : ℕ) - n = (k_var : ℕ) := by omega
          rw [h_sub, Nat.mod_eq_of_lt hk_lt]
        · have h_n_le : n ≤ (k_var : ℕ) + (m : ℕ) := by omega
          have h_mod : ((k_var : ℕ) + (m : ℕ)) % n = ((k_var : ℕ) + (m : ℕ) - n) % n := Nat.mod_eq_sub_mod h_n_le
          have h_lt : (k_var : ℕ) + (m : ℕ) - n < n := by omega
          have h_mod2 : ((k_var : ℕ) + (m : ℕ) - n) % n = (k_var : ℕ) + (m : ℕ) - n := Nat.mod_eq_of_lt h_lt
          have hj_eq : (j : ℕ) = (k_var : ℕ) + (m : ℕ) - n := by
            rw [hj_val, h_mod, h_mod2]
          rw [hj_eq]
          have h_inner : n - (m : ℕ) + ((k_var : ℕ) + (m : ℕ) - n) = (k_var : ℕ) := by omega
          rw [h_inner, Nat.mod_eq_of_lt hk_lt])
  rw [← h_back_eq, h_back_card]

/-- All-zeros indicator: φ_k(x) = +1 if x is all-false on S_k, -1 otherwise. -/
private def phi (n r : ℕ) (k : Fin n) (x : Fin n → Bool) (hr : r ≤ n) : ℝ :=
  if (∀ j' ∈ cyclicSet n r k hr, x j' = false) then 1 else -1

private theorem phi_all_zeros (n r : ℕ) (k : Fin n) (hr : r ≤ n) :
    phi n r k (fun _ => false) hr = 1 := by
  simp [phi]

private theorem phi_single_one (n r : ℕ) (k j : Fin n) (hr : r ≤ n) :
    phi n r k (fun i => if i = j then true else false) hr =
      if j ∈ cyclicSet n r k hr then (-1 : ℝ) else 1 := by
  unfold phi
  by_cases h_cond : ∀ j' ∈ cyclicSet n r k hr, (fun i => if i = j then true else false) j' = false
  · -- h_cond: ∀ j' ∈ S_k, ... = false
    rw [if_pos h_cond]
    have hj_notin : j ∉ cyclicSet n r k hr := by
      intro hj
      have h_eval := h_cond j hj
      have h_true : (if j = j then true else false) = true := if_pos rfl
      change (if j = j then true else false) = false at h_eval
      rw [h_true] at h_eval
      contradiction
    rw [if_neg hj_notin]
  · -- ¬h_cond
    rw [if_neg h_cond]
    have hj_in : j ∈ cyclicSet n r k hr := by
      by_contra hj
      have h_all : ∀ j' ∈ cyclicSet n r k hr, (fun i => if i = j then true else false) j' = false := by
        intro j' hj'
        have h_neq : j' ≠ j := by
          intro h_eq
          rw [h_eq] at hj'
          exact hj hj'
        change (if j' = j then true else false) = false
        exact if_neg h_neq
      exact h_cond h_all
    rw [if_pos hj_in]

/-- Sum of phi over all k for x = e_j: equals n - 2r. -/
private theorem phi_sum_single_one (n r : ℕ) (j : Fin n) (hr : r ≤ n) :
    (∑ k : Fin n, phi n r k (fun i => if i = j then true else false) hr) =
      (n : ℝ) - 2 * r := by
  have h_count := cyclicSet_sparsity_count n r j hr
  -- Rewrite sum using phi_single_one
  rw [Finset.sum_congr rfl (fun k _ => phi_single_one n r k j hr)]
  -- Split into in-set and out-of-set contributions
  let p := fun k => j ∈ cyclicSet n r k hr
  have h_sum_split : ∑ k : Fin n, (if p k then (-1 : ℝ) else 1) =
      (∑ k ∈ Finset.filter p Finset.univ, (-1 : ℝ)) +
      (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℝ)) := by
    calc ∑ k : Fin n, (if p k then (-1 : ℝ) else 1)
      _ = (∑ k ∈ Finset.filter p Finset.univ, (if p k then (-1 : ℝ) else (1 : ℝ))) +
          (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (if p k then (-1 : ℝ) else (1 : ℝ))) :=
            (Finset.sum_filter_add_sum_filter_not Finset.univ p _).symm
      _ = (∑ k ∈ Finset.filter p Finset.univ, (-1 : ℝ)) +
          (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℝ)) := by
        have h1 : (∑ k ∈ Finset.filter p Finset.univ, (if p k then (-1 : ℝ) else (1 : ℝ))) = ∑ k ∈ Finset.filter p Finset.univ, (-1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rw [if_pos hx]
        have h2 : (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (if p k then (-1 : ℝ) else (1 : ℝ))) = ∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rw [if_neg hx]
        rw [h1, h2]
  rw [h_sum_split]
  -- Now the goal is (∑ k ∈ filter p, -1) + (∑ k ∈ filter ¬p, 1) = n - 2r
  have h_sum_in : ∑ k ∈ Finset.filter p Finset.univ, (-1 : ℝ) = - (r : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change ((Finset.filter (fun k => j ∈ cyclicSet n r k hr) Finset.univ).card : ℝ) * (-1 : ℝ) = - (r : ℝ)
    rw [h_count, mul_neg_one]
  have h_sum_out : ∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℝ) = (n : ℝ) - r := by
    have h_card_not : (Finset.filter (fun k => ¬p k) Finset.univ).card = n - r := by
      have h_sum_ones : (∑ k : Fin n, (1 : ℕ)) =
          (∑ k ∈ Finset.filter p Finset.univ, (1 : ℕ)) + (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℕ)) :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ p _).symm
      have h_left : (∑ k : Fin n, (1 : ℕ)) = n := by simp
      have h_right1 : (∑ k ∈ Finset.filter p Finset.univ, (1 : ℕ)) = r := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        change (Finset.filter (fun k => j ∈ cyclicSet n r k hr) Finset.univ).card = r
        exact h_count
      have h_right2 : (∑ k ∈ Finset.filter (fun k => ¬p k) Finset.univ, (1 : ℕ)) = (Finset.filter (fun k => ¬p k) Finset.univ).card := by
        simp [Finset.sum_const, nsmul_eq_mul]
      omega
    rw [Finset.sum_const, nsmul_eq_mul]
    change ((Finset.filter (fun k => ¬p k) Finset.univ).card : ℝ) * (1 : ℝ) = (n : ℝ) - r
    rw [h_card_not, mul_one]
    exact Nat.cast_sub hr
  rw [h_sum_in, h_sum_out]
  ring

/-- Proposition 1: At ε = c/r with c > 1, a cyclic r-local game exists that misranks
    all n progression pairs from 0^n under the batch-mean evaluator.
    Construction: cyclic index sets, all-zeros indicator φ_k, scaled OneMax fitness. -/
theorem r_local_tightness_all_pairs_misranked (n r : ℕ) (c : ℝ)
    (h_n : 1 ≤ n) (h_r : 1 ≤ r) (h_r_le_n : r ≤ n) (h_c : c > 1) :
    ∃ G : RLocalGame (Fin n → Bool) (Fin n → Bool),
      G.n = n ∧ G.r = r ∧ G.epsilon = c / (r : ℝ) ∧
      ∀ j : Fin n, ∀ K (hK : 0 < K),
        (G.f (fun i => if i = j then true else false) +
          (∑ i : Fin K, G.h (fun _ => true)) / (K : ℝ) +
          (∑ i : Fin K, ∑ k : Fin G.n,
              G.R_k k (fun i => if i = j then true else false) (fun _ => true)) / (K : ℝ)) <
        (G.f (fun _ => false) +
          (∑ i : Fin K, G.h (fun _ => true)) / (K : ℝ) +
          (∑ i : Fin K, ∑ k : Fin G.n,
              G.R_k k (fun _ => false) (fun _ => true)) / (K : ℝ)) := by
  let epsilon := c / (r : ℝ)
  have h_eps_pos : (0 : ℝ) < epsilon := by positivity
  let phiFun := fun (k : Fin n) (x : Fin n → Bool) => phi n r k x h_r_le_n
  let f_om := fun x : (Fin n → Bool) =>
    (2 / (n : ℝ)) * (∑ j : Fin n, if x j then (1 : ℝ) else 0)
  let h_opp := fun _ : (Fin n → Bool) => (0 : ℝ)
  let R_k_trap := fun (k : Fin n) (x : Fin n → Bool) (y : Fin n → Bool) =>
    (epsilon / (n : ℝ)) * (if y k then (1 : ℝ) else (0 : ℝ)) * phiFun k x
  have h_phi_le (k : Fin n) (x : Fin n → Bool) : |phiFun k x| ≤ 1 := by
    show |phi n r k x h_r_le_n| ≤ 1; unfold phi; split_ifs <;> norm_num
  have h_R_bound : ∀ k x y, |R_k_trap k x y| ≤ epsilon / n := by
    intro k x y
    simp only [R_k_trap, phiFun]
    split_ifs with h_y
    · -- y k = true
      simp only [mul_one]
      rw [abs_mul]
      have h1 : |epsilon / (n : ℝ)| = epsilon / n := abs_of_nonneg (by positivity)
      rw [h1]
      have : |phiFun k x| ≤ 1 := h_phi_le k x
      calc (epsilon / n) * |phiFun k x|
        _ ≤ (epsilon / n) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = epsilon / n := by ring
    · -- y k = false
      have h_zero : (epsilon / (n : ℝ)) * 0 * phiFun k x = 0 := by ring
      rw [h_zero, abs_zero]
      positivity
  let G : RLocalGame (Fin n → Bool) (Fin n → Bool) := {
    f := f_om, h := h_opp, n := n, r := r,
    S := fun k => cyclicSet n r k h_r_le_n,
    R_k := R_k_trap, epsilon := epsilon,
    h_r_pos := h_r,
    h_S_size := fun k => le_of_eq (cyclicSet_card n r k h_r_le_n),
    h_S_sparsity := fun j => le_of_eq (cyclicSet_sparsity_count n r j h_r_le_n),
    h_R_bound := h_R_bound
  }
  refine ⟨G, rfl, rfl, rfl, ?_⟩
  -- Prove the misranking
  intro j K hK
  -- Simplify h terms (both zero) and batch averaging (K copies / K = 1)
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin, mul_zero, zero_div, add_zero]
  -- R_k with y = 1^n (all true): y k = true, so R_k = (ε/n) * φ
  have h_Rk_true (k : Fin n) (x : Fin n → Bool) :
      G.R_k k x (fun _ => true) = (G.epsilon / (G.n : ℝ)) * phiFun k x := by
    show R_k_trap k x (fun _ => true) = (epsilon / (n : ℝ)) * phiFun k x
    simp [R_k_trap, phiFun]
  -- Sum of R_k for e_j
  have h_sum_ej : (∑ k : Fin G.n, G.R_k k (fun i => if i = j then true else false) (fun _ => true)) =
      (G.epsilon / (G.n : ℝ)) * ((G.n : ℝ) - 2 * G.r) := by
    rw [Finset.sum_congr rfl (fun k _ => h_Rk_true k _), ← Finset.mul_sum]
    exact congr_arg (fun x => (epsilon / n) * x) (phi_sum_single_one n r j h_r_le_n)
  -- Sum of R_k for 0^n
  have h_sum_zero : (∑ k : Fin G.n, G.R_k k (fun _ => false) (fun _ => true)) = G.epsilon := by
    -- we want to just rw h_Rk_true, then sum phi
    have h_rw : ∀ k : Fin G.n, G.R_k k (fun _ => false) (fun _ => true) = (G.epsilon / (G.n : ℝ)) * phiFun k (fun _ => false) := fun k => h_Rk_true k (fun _ => false)
    rw [Finset.sum_congr rfl (fun k _ => h_rw k), ← Finset.mul_sum]
    have h_sum_phi : ∑ k : Fin n, phi n r k (fun _ => false) h_r_le_n = (n : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, phi_all_zeros,
        Finset.card_univ, Fintype.card_fin]
    -- G.n = n
    have h_Gn : (G.n : ℝ) = (n : ℝ) := rfl
    rw [h_Gn]
    rw [h_sum_phi]
    exact div_mul_cancel₀ G.epsilon (show (n : ℝ) ≠ 0 by positivity)
  -- f values
  have h_f_ej : G.f (fun i => if i = j then true else false) = 2 / (G.n : ℝ) := by
    show (2 / (n : ℝ)) * (∑ j' : Fin n, (if (if j' = j then true else false) = true then (1 : ℝ) else 0)) = 2 / (G.n : ℝ)
    have h_sum : (∑ j' : Fin n, (if (if j' = j then true else false) = true then (1 : ℝ) else 0)) = 1 := by
      have h_eq : (fun j' : Fin n => if (if j' = j then true else false) = true then (1 : ℝ) else 0) =
             (fun j' : Fin n => if j' = j then (1 : ℝ) else 0) := by
        ext j'
        by_cases hj : j' = j
        · simp [hj]
        · simp [hj]
      rw [h_eq]
      have h_sum_eval : (∑ j' : Fin n, if j' = j then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_ite_eq']
        split_ifs
        · rfl
        · exfalso; exact ‹j ∉ Finset.univ› (Finset.mem_univ j)
      rw [h_sum_eval]
    rw [h_sum, mul_one]
  have h_f_zero : G.f (fun _ => false) = 0 := by
    show (2 / (n : ℝ)) * (∑ j' : Fin n, if false = true then (1 : ℝ) else 0) = 0
    simp
  -- Substitute
  simp only [h_sum_ej, h_sum_zero, h_f_ej, h_f_zero]
  -- We also need to evaluate G.h to 0!
  have h_G_h : G.h (fun _ => true) = 0 := rfl
  simp only [h_G_h]
  -- Simplification
  have hK_pos : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hK)
  simp only [mul_zero, zero_div, add_zero, zero_add]
  repeat rw [mul_div_cancel_left₀ _ hK_pos]
  -- Need: 2/n + (ε/n)(n-2r) < ε
  have hr_ne : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have h_eps_r : epsilon * (r : ℝ) = c := by
    calc epsilon * (r : ℝ)
      _ = (c / (r : ℝ)) * (r : ℝ) := rfl
      _ = c := div_mul_cancel₀ c hr_ne
  -- Also replace G.n and G.r with n and r
  have h_Gn : (G.n : ℝ) = (n : ℝ) := rfl
  have h_Gr : (G.r : ℝ) = (r : ℝ) := rfl
  rw [h_Gn, h_Gr]
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  rw [show (epsilon / (n : ℝ)) * ((n : ℝ) - 2 * (r : ℝ)) = epsilon - 2 * (epsilon * (r : ℝ)) / (n : ℝ) by
    calc (epsilon / (n : ℝ)) * ((n : ℝ) - 2 * (r : ℝ))
      _ = (epsilon / (n : ℝ)) * (n : ℝ) - (epsilon / (n : ℝ)) * (2 * (r : ℝ)) := mul_sub _ _ _
      _ = epsilon - (epsilon / (n : ℝ)) * (2 * (r : ℝ)) := by rw [div_mul_cancel₀ _ hn_ne]
      _ = epsilon - 2 * (epsilon * (r : ℝ)) / (n : ℝ) := by ring]
  rw [h_eps_r]
  have : (0 : ℝ) < n := by positivity
  have : 2 / (n : ℝ) - 2 * c / n < 0 := by
    have h1 : 2 - 2 * c < 0 := by linarith
    have h2 : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have h3 : (2 - 2 * c) * (n : ℝ)⁻¹ < 0 := mul_neg_of_neg_of_pos h1 h2
    calc 2 / (n : ℝ) - 2 * c / n
      _ = (2 - 2 * c) / n := by rw [← sub_div]
      _ = (2 - 2 * c) * (n : ℝ)⁻¹ := by rw [div_eq_mul_one_div, one_div]
      _ < 0 := h3
  linarith

end RLocalGames
