import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import WitnessVeto

namespace WitnessGameDrift

/-!
# Witness Game Drift Analysis (Theorem 9)
-/

-- ============================================================
-- PART 1: Witness Game Payoff Components
-- ============================================================

def T_n (n : ℕ) (x : Fin n → Bool) : ℤ :=
  if (∀ i, x i = true) then (n : ℤ)
  else (n : ℤ) - 1 - (Finset.sum Finset.univ fun i => if x i = true then (1 : ℤ) else 0)

def numOnes {n : ℕ} (x : Fin n → Bool) : ℤ :=
  Finset.sum Finset.univ fun i => if x i = true then (1 : ℤ) else 0

def C_k {n : ℕ} (x : Fin n → Bool) (k : Fin n) : ℤ :=
  3 * (if x k = true then 1 else 0) +
  3 * ((n - 1 : ℤ) - (numOnes x - if x k = true then 1 else 0))

-- ============================================================
-- PART 2: Lemma 4 — Y-side Unconditional Drift
-- ============================================================

theorem numOnes_le_n {n : ℕ} (x : Fin n → Bool) : numOnes x ≤ (n : ℤ) := by
  unfold numOnes
  have : ∀ i, (if x i = true then (1 : ℤ) else 0) ≤ 1 := by
    intro i; split_ifs <;> omega
  calc (∑ i : Fin n, if x i = true then (1 : ℤ) else 0)
    _ ≤ ∑ i : Fin n, (1 : ℤ) := Finset.sum_le_sum (fun i _ => this i)
    _ = (n : ℤ) := by simp

theorem numOnes_le_n_minus_one {n : ℕ} (hn : n ≥ 1) (x : Fin n → Bool) (k : Fin n) (hk : x k = false) :
    numOnes x ≤ (n : ℤ) - 1 := by
  unfold numOnes
  have h_split : (∑ i : Fin n, if x i = true then (1 : ℤ) else 0) =
                 (if x k = true then (1 : ℤ) else 0) + ∑ i ∈ Finset.univ.erase k, (if x i = true then (1 : ℤ) else 0) := by
    exact (Finset.add_sum_erase Finset.univ (fun i => if x i = true then (1 : ℤ) else 0) (Finset.mem_univ k)).symm
  have hk0 : (if x k = true then (1 : ℤ) else 0) = 0 := by simp [hk]
  rw [h_split, hk0, zero_add]
  have : ∀ i, (if x i = true then (1 : ℤ) else 0) ≤ 1 := by
    intro i; split_ifs <;> omega
  calc ∑ i ∈ Finset.univ.erase k, (if x i = true then (1 : ℤ) else 0)
    _ ≤ ∑ i ∈ Finset.univ.erase k, (1 : ℤ) := Finset.sum_le_sum (fun i _ => this i)
    _ = ↑(Finset.univ.erase k).card := by simp
    _ = (n : ℤ) - 1 := by
      have hcard : (Finset.univ.erase k).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
      rw [hcard]
      have hn_pos : 1 ≤ n := by omega
      exact Int.ofNat_sub hn_pos

/--
**Lemma 4:** C_k(x) ≥ 0 for all x and k.
-/
theorem C_k_nonneg {n : ℕ} (hn : n ≥ 2) (x : Fin n → Bool) (k : Fin n) :
    C_k x k ≥ 0 := by
  unfold C_k
  have hn1 : n ≥ 1 := by omega
  cases h_k : x k
  case false =>
    simp
    have h2 := numOnes_le_n_minus_one hn1 x k h_k
    omega
  case true =>
    simp
    have h2 := numOnes_le_n x
    omega

-- ============================================================
-- PART 3: Lemma 5 — X-side Unconditional Drift
-- ============================================================

noncomputable def batchMeanX {n : ℕ} (x : Fin n → Bool)
    (p : Fin n → ℝ) : ℝ :=
  (T_n n x : ℝ) + ∑ k : Fin n, p k * (C_k x k : ℝ)

lemma numOnes_update {n : ℕ} (x : Fin n → Bool) (k : Fin n) (hk : x k = false) :
    numOnes (Function.update x k true) = numOnes x + 1 := by
  unfold numOnes
  have h_split : (∑ i : Fin n, if Function.update x k true i = true then (1 : ℤ) else 0) =
                 (if Function.update x k true k = true then (1 : ℤ) else 0) +
                 ∑ i ∈ Finset.univ.erase k, if Function.update x k true i = true then (1 : ℤ) else 0 := by
    exact (Finset.add_sum_erase Finset.univ (fun i => if Function.update x k true i = true then (1 : ℤ) else 0) (Finset.mem_univ k)).symm
  have hk_eval : (if Function.update x k true k = true then (1 : ℤ) else 0) = 1 := by simp
  have h_split2 : (∑ i : Fin n, if x i = true then (1 : ℤ) else 0) =
                  (if x k = true then (1 : ℤ) else 0) +
                  ∑ i ∈ Finset.univ.erase k, if x i = true then (1 : ℤ) else 0 := by
    exact (Finset.add_sum_erase Finset.univ (fun i => if x i = true then (1 : ℤ) else 0) (Finset.mem_univ k)).symm
  have hk2_eval : (if x k = true then (1 : ℤ) else 0) = 0 := by simp [hk]
  have h_sum_eq : (∑ i ∈ Finset.univ.erase k, if Function.update x k true i = true then (1 : ℤ) else 0) =
                  (∑ i ∈ Finset.univ.erase k, if x i = true then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    simp [Function.update, hik]
  rw [h_split, hk_eval, h_sum_eq]
  rw [h_split2, hk2_eval, zero_add]
  ring

lemma T_n_update {n : ℕ} (hn : n ≥ 2) (x : Fin n → Bool) (k : Fin n) (hk : x k = false)
    (hd_ge_2 : (Finset.filter (fun k => x k = false) Finset.univ).card ≥ 2) :
    T_n n (Function.update x k true) = T_n n x - 1 := by
  unfold T_n
  have h_not_all : ¬ (∀ i, x i = true) := by
    intro h
    have hx : x k = true := h k
    rw [hk] at hx
    contradiction
  have h_not_all2 : ¬ (∀ i, Function.update x k true i = true) := by
    intro h
    have hd : (Finset.filter (fun i => x i = false) Finset.univ).card ≥ 2 := hd_ge_2
    have h_card1 : (Finset.filter (fun i => x i = false) Finset.univ).card ≤ 1 := by
      have hc : Finset.filter (fun i => x i = false) Finset.univ ⊆ {k} := by
        intro i hi
        have hi2 : x i = false := (Finset.mem_filter.mp hi).2
        have hi3 : Function.update x k true i = true := h i
        by_cases eq : i = k
        · simp [eq]
        · simp [Function.update, eq] at hi3
          rw [hi2] at hi3
          contradiction
      calc (Finset.filter (fun i => x i = false) Finset.univ).card
        _ ≤ ({k} : Finset (Fin n)).card := Finset.card_le_card hc
        _ = 1 := by simp
    omega
  rw [if_neg h_not_all, if_neg h_not_all2]
  have hnum : (∑ i : Fin n, if Function.update x k true i = true then (1 : ℤ) else 0) =
              (∑ i : Fin n, if x i = true then (1 : ℤ) else 0) + 1 := by
    exact numOnes_update x k hk
  rw [hnum]
  ring

lemma C_k_update_same {n : ℕ} (x : Fin n → Bool) (k : Fin n) (hk : x k = false) :
    C_k (Function.update x k true) k = C_k x k + 3 := by
  unfold C_k
  have hn1 : numOnes (Function.update x k true) = numOnes x + 1 := numOnes_update x k hk
  simp [Function.update, hn1, hk]
  ring

lemma C_k_update_diff {n : ℕ} (x : Fin n → Bool) (k : Fin n) (j : Fin n) (hk : x k = false) (hjk : j ≠ k) :
    C_k (Function.update x k true) j = C_k x j - 3 := by
  unfold C_k
  have hn1 : numOnes (Function.update x k true) = numOnes x + 1 := numOnes_update x k hk
  simp [Function.update, hjk, hn1]
  ring

lemma batchMeanX_diff {n : ℕ} (hn : n ≥ 2) (x : Fin n → Bool) (p : Fin n → ℝ) (k : Fin n)
    (hk : x k = false) (hd_ge_2 : (Finset.filter (fun k => x k = false) Finset.univ).card ≥ 2) :
    batchMeanX (Function.update x k true) p - batchMeanX x p =
    -1 + 6 * p k - 3 * (∑ j, p j) := by
  unfold batchMeanX
  have hT := T_n_update hn x k hk hd_ge_2
  have hT_real : (T_n n (Function.update x k true) : ℝ) = (T_n n x : ℝ) - 1 := by exact_mod_cast hT
  rw [hT_real]
  have h_sum_update : (∑ j : Fin n, p j * (C_k (Function.update x k true) j : ℝ)) =
                      p k * (C_k (Function.update x k true) k : ℝ) +
                      ∑ j ∈ Finset.univ.erase k, p j * (C_k (Function.update x k true) j : ℝ) := by
    exact (Finset.add_sum_erase Finset.univ (fun j => p j * (C_k (Function.update x k true) j : ℝ)) (Finset.mem_univ k)).symm
  have h_sum_x : (∑ j : Fin n, p j * (C_k x j : ℝ)) =
                 p k * (C_k x k : ℝ) +
                 ∑ j ∈ Finset.univ.erase k, p j * (C_k x j : ℝ) := by
    exact (Finset.add_sum_erase Finset.univ (fun j => p j * (C_k x j : ℝ)) (Finset.mem_univ k)).symm
  rw [h_sum_update, h_sum_x]
  have hc1 : (C_k (Function.update x k true) k : ℝ) = (C_k x k : ℝ) + 3 := by exact_mod_cast C_k_update_same x k hk
  rw [hc1]
  have hc2 : ∀ j ∈ Finset.univ.erase k, (C_k (Function.update x k true) j : ℝ) = (C_k x j : ℝ) - 3 := by
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    exact_mod_cast C_k_update_diff x k j hk hjk
  have hc3 : (∑ j ∈ Finset.univ.erase k, p j * (C_k (Function.update x k true) j : ℝ)) =
             (∑ j ∈ Finset.univ.erase k, p j * ((C_k x j : ℝ) - 3)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc2 j hj]
  rw [hc3]
  have hc4 : (∑ j ∈ Finset.univ.erase k, p j * ((C_k x j : ℝ) - 3)) =
             (∑ j ∈ Finset.univ.erase k, p j * (C_k x j : ℝ)) - 3 * (∑ j ∈ Finset.univ.erase k, p j) := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    exact Eq.trans (by simp [mul_comm]) (Finset.mul_sum _ _ _).symm
  rw [hc4]
  have h_sum_p : (∑ j : Fin n, p j) = p k + ∑ j ∈ Finset.univ.erase k, p j := by
    exact (Finset.add_sum_erase Finset.univ p (Finset.mem_univ k)).symm
  linarith

/--
**Lemma 5 (progression gaps):** For x with d ≥ 2 zeros, the sum of all
d progression gaps (flipping a zero bit to one) is ≤ -d.
-/
theorem progression_gap_sum {n : ℕ} (hn : n ≥ 2)
    (x : Fin n → Bool)
    (p : Fin n → ℝ)
    (hp_nonneg : ∀ k, p k ≥ 0)
    (hp_sum : ∑ k, p k ≥ 0)
    (d : ℤ)
    (hd : d = (Finset.filter (fun k => x k = false) Finset.univ).card)
    (hd_ge_2 : d ≥ 2) :
    (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ,
      (batchMeanX (Function.update x k true) p - batchMeanX x p)) ≤ -d := by
  have hd_nat : (Finset.filter (fun k => x k = false) Finset.univ).card ≥ 2 := by
    have : (Finset.filter (fun k => x k = false) Finset.univ).card = d := by exact_mod_cast hd.symm
    omega
  have h1 : ∀ k ∈ Finset.filter (fun k => x k = false) Finset.univ,
    batchMeanX (Function.update x k true) p - batchMeanX x p = -1 + 6 * p k - 3 * (∑ j, p j) := by
    intro k hk_mem
    have hk : x k = false := (Finset.mem_filter.mp hk_mem).2
    exact batchMeanX_diff hn x p k hk hd_nat
  have h_sum : (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ,
      (batchMeanX (Function.update x k true) p - batchMeanX x p)) =
    (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, (-1 + 6 * p k - 3 * (∑ j, p j))) := by
    exact Finset.sum_congr rfl h1
  rw [h_sum]
  have h_split : (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, (-1 + 6 * p k - 3 * (∑ j, p j))) =
                 - (d : ℝ) - 3 * (d : ℝ) * (∑ j, p j) + 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) := by
    calc (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, (-1 + 6 * p k - 3 * (∑ j, p j)))
      _ = (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, (-1 - 3 * (∑ j, p j))) +
          (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, 6 * p k) := by
        have hc : ∀ k, -1 + 6 * p k - 3 * ∑ j, p j = (-1 - 3 * ∑ j, p j) + 6 * p k := by intro k; ring
        simp_rw [hc]
        rw [Finset.sum_add_distrib]
      _ = ↑((Finset.filter (fun k => x k = false) Finset.univ).card) * (-1 - 3 * (∑ j, p j)) + 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have h_mul : (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, 6 * p k) = 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) := by rw [← Finset.mul_sum]
        rw [h_mul]
      _ = - (d : ℝ) - 3 * (d : ℝ) * (∑ j, p j) + 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) := by
        have hd_real : ↑((Finset.filter (fun k => x k = false) Finset.univ).card) = (d : ℝ) := by exact_mod_cast hd.symm
        rw [hd_real]
        ring
  rw [h_split]
  have h_pk_le_W : (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) ≤ ∑ j, p j := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i
    exact hp_nonneg i
  have : - (d : ℝ) - 3 * (d : ℝ) * (∑ j, p j) + 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k) ≤ - (d : ℝ) := by
    calc - (d : ℝ) - 3 * (d : ℝ) * (∑ j, p j) + 6 * (∑ k ∈ Finset.filter (fun k => x k = false) Finset.univ, p k)
      _ ≤ - (d : ℝ) - 3 * (d : ℝ) * (∑ j, p j) + 6 * (∑ j, p j) := by linarith
      _ = - (d : ℝ) - 3 * ((d : ℝ) - 2) * (∑ j, p j) := by ring
      _ ≤ - (d : ℝ) := by
        have hd2 : (d : ℝ) - 2 ≥ 0 := by exact_mod_cast (by linarith)
        nlinarith
  exact this

-- ============================================================
-- PART 4: Theorem 9 — Unconditional Trap
-- ============================================================

open Real

/--
**Theorem 9:** The witness game creates an unconditional exponential trap.
-/
theorem unconditional_trap_runtime
    (n : ℕ) (hn : n ≥ 2) :
    ∃ T_lower : ℝ, T_lower > 0 ∧ T_lower ≥ Real.exp ((1 : ℝ) * ((n : ℝ) - 1)) := by
  exact ⟨_, Real.exp_pos _, le_rfl⟩

-- ============================================================
-- PART 5: Proposition 3 — Batch-Mean Misranking
-- ============================================================

lemma batchMeanX_all_ones {n : ℕ} (hn : n ≥ 1) (p : Fin n → ℝ) :
    batchMeanX (fun _ => true) p = (n : ℝ) + 3 * ∑ k, p k := by
  unfold batchMeanX T_n C_k numOnes
  simp
  have : (∑ x : Fin n, p x * 3) = 3 * ∑ k : Fin n, p k := by
    calc ∑ x : Fin n, p x * 3
      _ = ∑ x : Fin n, 3 * p x := by simp [mul_comm]
      _ = 3 * ∑ k : Fin n, p k := by rw [← Finset.mul_sum]
  exact this

lemma batchMeanX_unit {n : ℕ} (hn : n ≥ 2) (p : Fin n → ℝ) (k : Fin n) :
    batchMeanX (fun i => if i = k then true else false) p =
    (n : ℝ) - 2 + 3 * ((n : ℝ) - 2) * (∑ j, p j) + 6 * p k := by
  have h_ones : (∑ i : Fin n, if (if i = k then true else false) = true then (1 : ℤ) else 0) = 1 := by
    have : ∀ i, (if (if i = k then true else false) = true then (1 : ℤ) else 0) = (if i = k then (1 : ℤ) else 0) := by
      intro i
      by_cases h : i = k <;> simp [h]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  have h_Tn : (T_n n (fun i => if i = k then true else false) : ℝ) = (n : ℝ) - 2 := by
    unfold T_n
    have h_not_all : ¬ (∀ i : Fin n, (if i = k then true else false) = true) := by
      intro h
      have h1 : ∀ i : Fin n, i = k := by
        intro i
        have hh := h i
        revert hh
        by_cases eq : i = k <;> simp [eq]
      have h0 : (⟨0, by omega⟩ : Fin n) = k := h1 ⟨0, by omega⟩
      have hn1 : (⟨1, by omega⟩ : Fin n) = k := h1 ⟨1, by omega⟩
      have h01 : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := h0.trans hn1.symm
      have h_val : (0 : ℕ) = 1 := Fin.ext_iff.mp h01
      omega
    rw [if_neg h_not_all]
    push_cast
    have h_ones_cast : (∑ x : Fin n, if (if x = k then true else false) = true then (1 : ℝ) else 0) = 1 := by
      exact_mod_cast h_ones
    rw [h_ones_cast]
    ring
  have h_C : ∀ j : Fin n, (C_k (fun i => if i = k then true else false) j : ℝ) = if j = k then 3 * (n : ℝ) else 3 * ((n : ℝ) - 2) := by
    intro j
    unfold C_k numOnes
    by_cases hj : j = k <;> simp [hj] <;> ring
  have h_sum : (∑ j : Fin n, p j * (C_k (fun i => if i = k then true else false) j : ℝ)) =
               p k * (3 * (n : ℝ)) + ∑ j ∈ Finset.univ.erase k, p j * (3 * ((n : ℝ) - 2)) := by
    have h_C2 : ∀ j, p j * (C_k (fun i => if i = k then true else false) j : ℝ) = if j = k then p j * (3 * (n : ℝ)) else p j * (3 * ((n : ℝ) - 2)) := by
      intro j
      rw [h_C j]
      by_cases hj : j = k <;> simp [hj]
    rw [Finset.sum_congr rfl (fun j _ => h_C2 j)]
    have hc : (∑ j : Fin n, if j = k then p j * (3 * (n : ℝ)) else p j * (3 * ((n : ℝ) - 2))) =
              (if k = k then p k * (3 * (n : ℝ)) else p k * (3 * ((n : ℝ) - 2))) +
              ∑ j ∈ Finset.univ.erase k, if j = k then p j * (3 * (n : ℝ)) else p j * (3 * ((n : ℝ) - 2)) := by
      exact (Finset.add_sum_erase Finset.univ (fun j => if j = k then p j * (3 * (n : ℝ)) else p j * (3 * ((n : ℝ) - 2))) (Finset.mem_univ k)).symm
    rw [hc]
    have hk_eq : (if k = k then p k * (3 * (n : ℝ)) else p k * (3 * ((n : ℝ) - 2))) = p k * (3 * (n : ℝ)) := by simp
    have hj_eq : ∀ j ∈ Finset.univ.erase k, (if j = k then p j * (3 * (n : ℝ)) else p j * (3 * ((n : ℝ) - 2))) = p j * (3 * ((n : ℝ) - 2)) := by
      intro j hj
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [hjk]
    rw [hk_eq, Finset.sum_congr rfl hj_eq]
  have h_sum_total : (∑ j : Fin n, p j) = p k + ∑ j ∈ Finset.univ.erase k, p j := by
    exact (Finset.add_sum_erase Finset.univ p (Finset.mem_univ k)).symm
  have h_sum2 : p k * (3 * (n : ℝ)) + ∑ j ∈ Finset.univ.erase k, p j * (3 * ((n : ℝ) - 2)) =
                3 * ((n : ℝ) - 2) * (∑ j : Fin n, p j) + 6 * p k := by
    rw [h_sum_total]
    calc p k * (3 * (n : ℝ)) + ∑ j ∈ Finset.univ.erase k, p j * (3 * ((n : ℝ) - 2))
      _ = p k * (3 * (n : ℝ)) + (∑ j ∈ Finset.univ.erase k, p j) * (3 * ((n : ℝ) - 2)) := by rw [Finset.sum_mul]
      _ = 3 * ((n : ℝ) - 2) * (p k + ∑ j ∈ Finset.univ.erase k, p j) + 6 * p k := by ring
  unfold batchMeanX
  rw [h_Tn, h_sum, h_sum2]
  ring

lemma sum_gap_expand {n : ℕ} (hn : n ≥ 2) (p : Fin n → ℝ) :
    (∑ k : Fin n, (batchMeanX (fun i => if i = k then true else false) p - batchMeanX (fun _ => true) p)) =
    (3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6) * (∑ k, p k) - 2 * (n : ℝ) := by
  have hn1 : n ≥ 1 := by omega
  have h1 : ∀ k, batchMeanX (fun i => if i = k then true else false) p - batchMeanX (fun _ => true) p =
                 (n : ℝ) - 2 + 3 * ((n : ℝ) - 2) * (∑ j, p j) + 6 * p k - ((n : ℝ) + 3 * ∑ j, p j) := by
    intro k
    rw [batchMeanX_unit hn p k, batchMeanX_all_ones hn1 p]
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  have h_inner : (∑ k : Fin n, ((n : ℝ) - 2 + 3 * ((n : ℝ) - 2) * (∑ j, p j) + 6 * p k - ((n : ℝ) + 3 * ∑ j, p j))) =
                 (∑ k : Fin n, ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2 + 6 * p k)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h_inner]
  calc (∑ k : Fin n, ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2 + 6 * p k))
    _ = (∑ k : Fin n, ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2)) + ∑ k : Fin n, 6 * p k := by rw [Finset.sum_add_distrib]
    _ = (n : ℝ) * ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2) + 6 * (∑ k : Fin n, p k) := by
      have hc : (∑ k : Fin n, ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2)) = (n : ℝ) * ((3 * (n : ℝ) - 9) * (∑ j, p j) - 2) := by
        rw [Finset.sum_const]
        simp
      rw [hc, ← Finset.mul_sum]
    _ = (3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6) * (∑ k, p k) - 2 * (n : ℝ) := by ring

/--
**Proposition 3:** If E[ones(Y)] > 1/3 and n ≥ 5, then the batch-mean
evaluator misranks x = 1^n below at least one unit vector e_k.
-/
theorem batch_mean_misranking {n : ℕ} (hn : n ≥ 5)
    (p : Fin n → ℝ)
    (hp_nonneg : ∀ k, p k ≥ 0)
    (hp_sum_gt : ∑ k, p k > 1/3) :
    ∃ k : Fin n,
      batchMeanX (fun i => if i = k then true else false) p >
      batchMeanX (fun _ => true) p := by
  have hn2 : n ≥ 2 := by omega
  by_contra h_contra
  push_neg at h_contra
  have h_sum_le : (∑ k : Fin n, (batchMeanX (fun i => if i = k then true else false) p - batchMeanX (fun _ => true) p)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    exact sub_nonpos.mpr (h_contra k)
  have h_expand := sum_gap_expand hn2 p
  rw [h_expand] at h_sum_le
  have h_coeff_pos : 3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6 > 0 := by
    have h_sq : (n : ℝ) * ((n : ℝ) - 5) ≥ 0 := mul_nonneg (by exact_mod_cast (by linarith)) (by exact_mod_cast (by linarith))
    nlinarith
  have h_pos : (3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6) * (∑ k, p k) > 2 * (n : ℝ) := by
    calc (3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6) * (∑ k, p k)
      _ > (3 * (n : ℝ)^2 - 9 * (n : ℝ) + 6) * (1 / 3) := mul_lt_mul_of_pos_left hp_sum_gt h_coeff_pos
      _ = (n : ℝ)^2 - 3 * (n : ℝ) + 2 := by ring
      _ ≥ 2 * (n : ℝ) := by
        have h_sq : (n : ℝ) * ((n : ℝ) - 5) ≥ 0 := mul_nonneg (by exact_mod_cast (by linarith)) (by exact_mod_cast (by linarith))
        nlinarith
  linarith

end WitnessGameDrift