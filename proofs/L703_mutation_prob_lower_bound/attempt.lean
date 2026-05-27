-- WORKER SCRATCHPAD for L703 mutation_prob_lower_bound.
import LBTCoupling
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Real

namespace L703Attempt

lemma hamming_weight_le_n {n : ℕ} (x : BitString n) : hamming_weight x ≤ n := by
  unfold hamming_weight
  rw [Nat.card_eq_fintype_card]
  convert Fintype.card_subtype_le (p := fun i : Fin n => x i = true) using 1
  exact (Fintype.card_fin n).symm

lemma hamming_weight_eq_filter_card {n : ℕ} (x : BitString n) :
    hamming_weight x = (Finset.univ.filter (fun i : Fin n => x i = true)).card := by
  unfold hamming_weight
  rw [Nat.subtype_card (s := Finset.univ.filter (fun i : Fin n => x i = true)) (fun i => by simp)]

lemma hamming_weight_all_true {n : ℕ} (x : BitString n) (h : ∀ k, x k = true) :
    hamming_weight x = n := by
  rw [hamming_weight_eq_filter_card]
  have heq : Finset.univ.filter (fun i : Fin n => x i = true) = Finset.univ := by
    ext i
    simp [h i]
  rw [heq, Finset.card_univ, Fintype.card_fin]

lemma exists_false_bit {n : ℕ} (x : BitString n) (hlt : hamming_weight x < n) :
    ∃ k : Fin n, x k = false := by
  by_contra hall
  push_neg at hall
  have hall' : ∀ k, x k = true := by
    intro k
    cases hk : x k with
    | true => rfl
    | false => exact (hall k hk).elim
  exact absurd hlt (by rw [hamming_weight_all_true x hall']; exact Nat.lt_irrefl n)

lemma hamming_weight_update_true {n : ℕ} (x : BitString n) (k : Fin n) (hk : x k = false) :
    hamming_weight (Function.update x k true) = hamming_weight x + 1 := by
  rw [hamming_weight_eq_filter_card, hamming_weight_eq_filter_card]
  have heq :
      Finset.univ.filter (fun i : Fin n => (Function.update x k true) i = true) =
        insert k (Finset.univ.filter (fun i : Fin n => x i = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
    by_cases hik : i = k
    · subst hik
      simp [Function.update_self, hk]
    · simp [Function.update, hik, hk]
  have hk_not : k ∉ Finset.univ.filter (fun i : Fin n => x i = true) := by
    simp [hk]
  rw [heq, Finset.card_insert_of_notMem hk_not]

lemma mem_A_ge_A_lvl_iff {n j : ℕ} (x : BitString n) :
    x ∈ A_ge (A_lvl n) j ↔ j ≤ hamming_weight x := by
  simp only [A_ge, A_lvl, Set.mem_iUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk_ge, hk_mem⟩
    dsimp [A_lvl] at hk_mem
    exact le_trans hk_ge (Nat.le_of_eq hk_mem.symm)
  · intro hhw
    refine ⟨⟨hamming_weight x, Nat.lt_succ_of_le (hamming_weight_le_n x)⟩, hhw, rfl⟩

noncomputable def one_minus_p_mut (n : ℕ) : ENNReal := 1 - p_mut n

lemma mutation_prob_self {n : ℕ} (hn : n ≠ 0) (x : BitString n) :
    mutation_prob x x = (one_minus_p_mut n) ^ n := by
  have hterm (k : Fin n) : bit_prob n (x k) (x k) = one_minus_p_mut n := by
    simp [bit_prob, if_neg hn, beq_self_eq_true, one_minus_p_mut, p_mut]
  unfold mutation_prob
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_const]
  simp [Finset.card_univ, Fintype.card_fin, p_mut, if_neg hn]

lemma mutation_prob_single_flip {n : ℕ} (hn : n ≠ 0) (x : BitString n) (k : Fin n)
    (hk : x k = false) :
    mutation_prob x (Function.update x k true) =
      p_mut n * (one_minus_p_mut n) ^ (n - 1) := by
  unfold mutation_prob
  have hk_bit : bit_prob n (x k) (Function.update x k true k) = p_mut n := by
    simp [bit_prob, hk, Function.update_self]
  have hprod :
      ∏ i ∈ Finset.univ.erase k, bit_prob n (x i) (Function.update x k true i) =
        (one_minus_p_mut n) ^ (n - 1) := by
    have hcard : (Finset.univ.erase k : Finset (Fin n)).card = n - 1 := by
      simp [Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_congr rfl fun i hi => ?_]
    · rw [Finset.prod_const, hcard]
    · unfold bit_prob one_minus_p_mut p_mut
      have hne := Finset.ne_of_mem_erase hi
      simp [Function.update, hne, beq_self_eq_true]
  rw [← Finset.mul_prod_erase (s := Finset.univ)
    (f := fun i : Fin n => bit_prob n (x i) (Function.update x k true i))
    (a := k) (h := Finset.mem_univ k), hk_bit, hprod]

lemma one_sub_inv_pow_ge_one_div_exp {n : ℕ} (hn : n ≥ 2) :
    (1 - (n : ℝ)⁻¹) ^ (n - 1) ≥ (Real.exp 1)⁻¹ := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hbase : 0 < 1 - (n : ℝ)⁻¹ := by
    have : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast hn
    linarith
  have hlog := one_sub_inv_le_log_of_pos hbase
  have hmul : ((n : ℝ) - 1) * Real.log (1 - (n : ℝ)⁻¹) ≥ -1 := by
    have hn1_pos : 0 < (n : ℝ) - 1 := by linarith
    calc
      ((n : ℝ) - 1) * Real.log (1 - (n : ℝ)⁻¹)
          ≥ ((n : ℝ) - 1) * (-((n : ℝ) - 1)⁻¹) := by gcongr; field_simp at hlog ⊢; linarith
      _ = -1 := by field_simp
  have hrpow : (1 - (n : ℝ)⁻¹) ^ (n - 1) ≥ Real.exp (-1) := by
    have hpos : 0 < (1 - (n : ℝ)⁻¹) ^ (n - 1) := pow_pos hbase (n - 1)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hnat : ((n - 1 : ℕ) : ℝ) * Real.log (1 - (n : ℝ)⁻¹) ≥ -1 := by
      rw [hcast]
      exact hmul
    exact (Real.le_log_iff_exp_le hpos).mp (by rw [Real.log_pow]; exact hnat.le)
  simpa [Real.exp_neg, div_eq_mul_inv, mul_comm] using hrpow

lemma one_sub_pow_ge_one_div_two_exp {n : ℕ} (hn : n ≥ 2) :
    (1 - (n : ℝ)⁻¹) ^ n ≥ (1 / (2 * Real.exp 1) : ℝ) := by
  have hpow :
      (1 - (n : ℝ)⁻¹) ^ n =
        (1 - (n : ℝ)⁻¹) ^ (n - 1) * (1 - (n : ℝ)⁻¹) := by
    calc (1 - (n : ℝ)⁻¹) ^ n
        = (1 - (n : ℝ)⁻¹) ^ ((n - 1) + 1) := by congr 1; omega
      _ = (1 - (n : ℝ)⁻¹) ^ (n - 1) * (1 - (n : ℝ)⁻¹) := by rw [pow_add, pow_one]
  have hleft := one_sub_inv_pow_ge_one_div_exp hn
  have hright : (1 - (n : ℝ)⁻¹) ≥ (1 / 2 : ℝ) := by
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
    have : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast hn
    linarith
  rw [hpow]
  calc
    (1 - (n : ℝ)⁻¹) ^ (n - 1) * (1 - (n : ℝ)⁻¹)
        ≥ (Real.exp 1)⁻¹ * (1 - (n : ℝ)⁻¹) := by gcongr
    _ ≥ (Real.exp 1)⁻¹ * (1 / 2 : ℝ) := by gcongr
    _ = 1 / (2 * Real.exp 1) := by field_simp

lemma p_mut_toReal {n : ℕ} (hn : n ≠ 0) : (p_mut n).toReal = (n : ℝ)⁻¹ := by
  dsimp [p_mut]
  simp only [if_neg hn, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma one_sub_p_mut_toReal {n : ℕ} (hn : n ≠ 0) :
    (one_minus_p_mut n).toReal = 1 - (n : ℝ)⁻¹ := by
  unfold one_minus_p_mut
  rw [ENNReal.toReal_sub_of_le (p_mut_le_one n) ENNReal.one_ne_top, ENNReal.toReal_one, p_mut_toReal hn]

lemma mutation_prob_le_one {n : ℕ} (x y : BitString n) : mutation_prob x y ≤ 1 := by
  rw [← sum_mutation_prob x]
  exact Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ y)

lemma mutation_prob_toReal_single_flip {n : ℕ} (hn : n ≠ 0) (x : BitString n) (k : Fin n)
    (hk : x k = false) :
    (mutation_prob x (Function.update x k true)).toReal =
      (n : ℝ)⁻¹ * (1 - (n : ℝ)⁻¹) ^ (n - 1) := by
  rw [mutation_prob_single_flip hn x k hk, ENNReal.toReal_mul, ENNReal.toReal_pow,
    p_mut_toReal hn, one_sub_p_mut_toReal hn, mul_comm]

lemma mutation_prob_self_toReal {n : ℕ} (hn : n ≠ 0) (x : BitString n) :
    (mutation_prob x x).toReal = (1 - (n : ℝ)⁻¹) ^ n := by
  rw [mutation_prob_self hn x, ENNReal.toReal_pow, one_sub_p_mut_toReal hn]

lemma parent_mut_measure_ge_point {n : ℕ} (x y : BitString n) (s : Set (BitString n))
    (hy : y ∈ s) :
    parent_mut_measure x s ≥ mutation_prob x y := by
  unfold parent_mut_measure
  calc
    (∑ z : BitString n, mutation_prob x z • Measure.dirac z) s
        = ∑ z : BitString n, (mutation_prob x z • Measure.dirac z) s := measure_sum_apply ..
    _ ≥ (mutation_prob x y • Measure.dirac y) s := by
      apply Finset.single_le_sum (fun z _ => zero_le _) (Finset.mem_univ y)
    _ = mutation_prob x y := by
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem hy]
      simp

lemma parent_mut_measure_ge_point_toReal {n : ℕ} (x y : BitString n) (s : Set (BitString n))
    (hy : y ∈ s) :
    (parent_mut_measure x s).toReal ≥ (mutation_prob x y).toReal := by
  have h := parent_mut_measure_ge_point x y s hy
  have hs_le : parent_mut_measure x s ≤ 1 := by
    calc
      parent_mut_measure x s ≤ parent_mut_measure x Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := parent_mut_measure_univ x
  have hy_le : mutation_prob x y ≤ 1 := mutation_prob_le_one x y
  have hle : mutation_prob x y ≤ parent_mut_measure x s := h.le
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hy_le)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hs_le)).2 hle

-- Main goal: merge into LBTCoupling.lean once complete.
lemma mutation_prob_lower_bound {n : ℕ} (hn : n ≥ 2) (x : BitString n) (j : ℕ) (hj : j < n)
    (hx : x ∈ A_ge (A_lvl n) j) :
    (parent_mut_measure x (A_ge (A_lvl n) (j + 1))).toReal ≥ 1 / (Real.exp 1 * n) := by
  have hn' : n ≠ 0 := (Nat.zero_lt_of_lt hj).ne'
  have hhw : j ≤ hamming_weight x := (mem_A_ge_A_lvl_iff x).1 hx
  by_cases hlt : hamming_weight x < n
  · rcases exists_false_bit x hlt with ⟨k, hk⟩
    set y := Function.update x k true
    have hy_mem : y ∈ A_ge (A_lvl n) (j + 1) := by
      rw [mem_A_ge_A_lvl_iff]
      have hwy : hamming_weight y = hamming_weight x + 1 :=
        hamming_weight_update_true x k hk
      exact (by rw [hwy]; exact Nat.succ_le_succ hhw)
    have hge :=
      parent_mut_measure_ge_point_toReal x y (A_ge (A_lvl n) (j + 1)) hy_mem
    have hprob :
        (mutation_prob x y).toReal =
          (n : ℝ)⁻¹ * (1 - (n : ℝ)⁻¹) ^ (n - 1) :=
      mutation_prob_toReal_single_flip hn' x k hk
    have hbound :
        (n : ℝ)⁻¹ * (1 - (n : ℝ)⁻¹) ^ (n - 1) ≥ (Real.exp 1)⁻¹ * (n : ℝ)⁻¹ := by
      have := one_sub_inv_pow_ge_one_div_exp hn
      nlinarith [show 0 < (n : ℝ)⁻¹ from inv_pos.mpr (by positivity : 0 < (n : ℝ))]
    have htarget :
        (Real.exp 1)⁻¹ * (n : ℝ)⁻¹ = 1 / (Real.exp 1 * n) := by
      field_simp
    linarith [hge, hprob, hbound, htarget]
  · have hw_eq : hamming_weight x = n :=
      Nat.le_antisymm (hamming_weight_le_n x) (Nat.le_of_not_gt hlt)
    have hx_self : x ∈ A_ge (A_lvl n) (j + 1) := by
      rw [mem_A_ge_A_lvl_iff]
      exact le_trans (Nat.succ_le_of_lt hj) (by rw [hw_eq])
    have hge := parent_mut_measure_ge_point_toReal x x (A_ge (A_lvl n) (j + 1)) hx_self
    have hprob : (mutation_prob x x).toReal = (1 - (n : ℝ)⁻¹) ^ n :=
      mutation_prob_self_toReal hn' x
    have hbound : (1 - (n : ℝ)⁻¹) ^ n ≥ 1 / (Real.exp 1 * n) := by
      have hmain := one_sub_pow_ge_one_div_two_exp hn
      have hn_pos : 0 < (n : ℝ) := by positivity
      have hweak : 1 / (Real.exp 1 * (n : ℝ)) ≤ 1 / (2 * Real.exp 1) := by
        rw [mul_comm (2 : ℝ) (Real.exp 1)]
        rw [one_div_le_one_div (mul_pos (Real.exp_pos 1) hn_pos)
          (mul_pos (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2))]
        field_simp
        nlinarith [show (2 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn]
      exact le_trans hweak hmain
    linarith [hge, hprob, hbound]

end L703Attempt
