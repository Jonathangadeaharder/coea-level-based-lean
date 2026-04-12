import LintOptions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace LeCamLowerBound

/-!
# Le Cam Lower Bound (Theorem 4: thm:tight_sample_lower_bound)
-/

-- ============================================================
-- PART 1: Two-Point Game Construction
-- ============================================================

noncomputable def f_plus (n : ℕ) (z₁ : ℝ) : ℝ :=
  (2 / (n : ℝ)) * z₁ - 1 / (n : ℝ)

noncomputable def f_minus (n : ℕ) (z₁ : ℝ) : ℝ :=
  -(2 / (n : ℝ)) * z₁ + 1 / (n : ℝ)

noncomputable def R_plus (epsilon : ℝ) (z₁ : ℝ) : ℝ :=
  epsilon * (1 - 2 * z₁)

noncomputable def R_minus (epsilon : ℝ) (z₁ : ℝ) : ℝ :=
  -epsilon * (1 - 2 * z₁)

-- ============================================================
-- PART 2: Gap Computations
-- ============================================================

theorem f_plus_gap (n : ℕ) (hn : n ≥ 2) :
    f_plus n 1 - f_plus n 0 = 2 / (n : ℝ) := by
  unfold f_plus; ring

theorem f_minus_gap (n : ℕ) (hn : n ≥ 2) :
    f_minus n 1 - f_minus n 0 = -(2 / (n : ℝ)) := by
  unfold f_minus; ring

theorem R_minus_eq_neg_R_plus (epsilon : ℝ) (z₁ : ℝ) :
    R_minus epsilon z₁ = -(R_plus epsilon z₁) := by
  unfold R_plus R_minus; ring

-- ============================================================
-- PART 3: Residual Bounds
-- ============================================================

theorem R_plus_at_zero (epsilon : ℝ) : R_plus epsilon 0 = epsilon := by
  unfold R_plus; ring

theorem R_plus_at_one (epsilon : ℝ) : R_plus epsilon 1 = -epsilon := by
  unfold R_plus; ring

theorem R_plus_abs_le_eps (epsilon : ℝ) (h_eps : epsilon ≥ 0) :
    ∀ z₁ ∈ ({0, 1} : Set ℝ), |R_plus epsilon z₁| ≤ epsilon := by
  intro z₁ hz
  simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · rw [R_plus_at_zero, abs_of_nonneg h_eps]
  · rw [R_plus_at_one]; rw [show |-epsilon| = epsilon from abs_neg epsilon ▸ abs_of_nonneg h_eps]

theorem R_minus_abs_le_eps (epsilon : ℝ) (h_eps : epsilon ≥ 0) :
    ∀ z₁ ∈ ({0, 1} : Set ℝ), |R_minus epsilon z₁| ≤ epsilon := by
  intro z₁ hz
  rw [R_minus_eq_neg_R_plus, abs_neg]
  exact R_plus_abs_le_eps epsilon h_eps z₁ hz

-- ============================================================
-- PART 4: Opposite Rankings
-- ============================================================

theorem g_plus_ranks_x'_above_x (n : ℕ) (hn : n ≥ 2) :
    f_plus n 1 - f_plus n 0 > 0 := by
  rw [f_plus_gap n hn]; positivity

theorem g_minus_ranks_x_above_x' (n : ℕ) (hn : n ≥ 2) :
    f_minus n 1 - f_minus n 0 < 0 := by
  rw [f_minus_gap n hn]
  have : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) (by exact_mod_cast (by omega))
  linarith

-- ============================================================
-- PART 5: Effective Gap After Residual Squeeze
-- ============================================================

theorem effective_gap_plus (n : ℕ) (epsilon : ℝ) (hn : n ≥ 2)
    (h_eps : epsilon ≥ 0) (h_eps_bound : epsilon < 1 / (n : ℝ)) :
    f_plus n 1 - f_plus n 0 - 2 * epsilon ≥ 2 * (1 - (n : ℝ) * epsilon) / (n : ℝ) := by
  rw [f_plus_gap n hn]
  field_simp
  exact le_refl _

theorem effective_gap_minus (n : ℕ) (epsilon : ℝ) (hn : n ≥ 2)
    (h_eps : epsilon ≥ 0) (h_eps_bound : epsilon < 1 / (n : ℝ)) :
    f_minus n 1 - f_minus n 0 + 2 * epsilon ≤ -(2 * (1 - (n : ℝ) * epsilon) / (n : ℝ)) := by
  rw [f_minus_gap n hn]
  field_simp
  linarith

-- ============================================================
-- PART 6: Hellinger Distance Infrastructure
-- ============================================================

open scoped BigOperators
open scoped ENNReal

/-- Squared Hellinger distance for discrete distributions on Fin n -/
noncomputable def hellingerSq {n : ℕ} (p q : PMF (Fin n)) : ℝ :=
  (1 / 2) * ∑ i : Fin n, (Real.sqrt ((p i).toReal) - Real.sqrt ((q i).toReal)) ^ 2

/-- Hellinger squared distance is inherently non-negative -/
theorem hellingerSq_nonneg {n : ℕ} (p q : PMF (Fin n)) : 0 ≤ hellingerSq p q := by
  have h1 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h2 : 0 ≤ ∑ i : Fin n, (Real.sqrt ((p i).toReal) - Real.sqrt ((q i).toReal)) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg _
  exact mul_nonneg h1 h2

/-- Helper: sum of PMF toReal values equals 1 on a Fintype -/
theorem pmf_toReal_sum_eq_one {n : ℕ} (p : PMF (Fin n)) :
    ∑ i : Fin n, (p i).toReal = 1 := by
  have h_ne_top : ∀ i ∈ (Finset.univ : Finset (Fin n)), (p i) ≠ ∞ :=
    fun i _ => PMF.apply_ne_top p i
  -- Use ENNReal.toReal_sum to push toReal inside
  have h_toReal : (∑ i : Fin n, (p i)).toReal = ∑ i : Fin n, (p i).toReal :=
    ENNReal.toReal_sum h_ne_top
  -- Now we need (∑ i, p i).toReal = 1
  -- ∑ i, p i = ∑' i, p i = 1 (by PMF.tsum_coe and Fintype)
  have h_tsum_eq_sum : (∑' i : Fin n, (p i)) = ∑ i : Fin n, (p i) :=
    tsum_eq_sum fun _ h => (h (Finset.mem_univ _)).elim
  have h_sum : ∑ i : Fin n, (p i) = 1 := by
    rw [← h_tsum_eq_sum, PMF.tsum_coe]
  rw [h_sum, ENNReal.toReal_one] at h_toReal
  exact h_toReal.symm

/-- Helper: expand (√a - √b)² = a + b - 2√(ab) -/
private theorem sq_sqrt_sub_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  have h1 : (Real.sqrt a - Real.sqrt b) ^ 2 = Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by ring
  rw [h1, Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [Real.sqrt_mul ha, mul_assoc]
  ring

/-- Alternative form: H² = 1 - Σ √(p_i · q_i)
    Proved by expanding the square and using PMF sum = 1. -/
theorem hellingerSq_eq_one_minus_affinity {n : ℕ} (p q : PMF (Fin n)) :
    hellingerSq p q = 1 - ∑ i : Fin n, Real.sqrt ((p i).toReal * (q i).toReal) := by
  unfold hellingerSq
  -- Expand the square: (√p - √q)² = p + q - 2√(pq)
  have h_expand : ∀ i : Fin n,
      (Real.sqrt ((p i).toReal) - Real.sqrt ((q i).toReal)) ^ 2 =
      (p i).toReal + (q i).toReal - 2 * Real.sqrt ((p i).toReal * (q i).toReal) := by
    intro i
    exact sq_sqrt_sub_sqrt (p i).toReal_nonneg (q i).toReal_nonneg
  -- Distribute the sum
  simp only [h_expand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- Use PMF sum = 1
  rw [pmf_toReal_sum_eq_one p, pmf_toReal_sum_eq_one q]
  -- Goal: 1/2 * (2 - ∑ i, 2 * √(p_i q_i)) = 1 - ∑ i, √(p_i q_i)
  -- Pull out the 2 from the sum
  conv_rhs => rw [show (1 : ℝ) - ∑ i : Fin n, Real.sqrt ((p i).toReal * (q i).toReal) =
    1 / 2 * (2 - 2 * ∑ i : Fin n, Real.sqrt ((p i).toReal * (q i).toReal)) by ring]
  congr 1
  rw [Finset.mul_sum]
  ring

-- ============================================================
-- PART 7: 3-Point Distribution Construction and Hellinger
-- ============================================================

private theorem ennreal_coe_div_toReal (n m : ℕ) (_hm : m ≠ 0) :
    ((n : ℝ≥0∞) / m).toReal = (n : ℝ) / m := by
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- The "uniform" hypothesis distribution on Fin M (M ≥ 3).
    Places mass (M-1)/M at index 0 and 1/M at index 1.
    Normalization proof: ∑ = (M-1)/M + 1/M = M/M = 1. -/
noncomputable def uniformPMF (M : ℕ) (hM : M ≥ 3) : PMF (Fin M) :=
  PMF.ofFintype
    (fun i : Fin M => if (i : ℕ) = 0 then ((M - 1 : ℕ) : ℝ≥0∞) / M
                       else if (i : ℕ) = 1 then (1 : ℝ≥0∞) / M
                       else 0)
    (by
      let i0 : Fin M := ⟨0, by omega⟩
      let i1 : Fin M := ⟨1, by omega⟩
      have hi0 : (i0 : ℕ) = 0 := rfl
      have hi1 : (i1 : ℕ) = 1 := rfl
      have h01 : (0 : ℕ) ≠ 1 := by omega
      have h10 : (1 : ℕ) ≠ 0 := by omega
      have h_ne : i0 ≠ i1 := by intro h; simp [Fin.ext_iff] at h
      have h_rest : ∀ x : Fin M, x ≠ i0 ∧ x ≠ i1 →
          (if (x : ℕ) = 0 then ((M - 1 : ℕ) : ℝ≥0∞) / M
            else if (x : ℕ) = 1 then (1 : ℝ≥0∞) / M else 0) = 0 := by
        intro x hx
        have h0 : (x : ℕ) ≠ 0 := by intro h; apply hx.1; ext; exact h
        have h1 : (x : ℕ) ≠ 1 := by intro h; apply hx.2; ext; exact h
        simp [h0, h1]
      rw [Fintype.sum_eq_add i0 i1 h_ne h_rest]
      simp only [hi0, hi1, reduceIte, h01, h10]
      have h_key : ((M - 1 : ℕ) : ℝ≥0∞) + 1 = (M : ℝ≥0∞) := by norm_cast; omega
      rw [← ENNReal.add_div, h_key]
      exact ENNReal.div_self (by positivity) ENNReal.coe_ne_top)

/-- The "shifted" alternative distribution on Fin M (M ≥ 3).
    Places mass (M-1)/M at index 0 and 1/M at index 2.
    Normalization proof: ∑ = (M-1)/M + 1/M + 0 + ... = 1. -/
noncomputable def shiftedUniformPMF (M : ℕ) (hM : M ≥ 3) : PMF (Fin M) :=
  PMF.ofFintype
    (fun i : Fin M => if (i : ℕ) = 0 then ((M - 1 : ℕ) : ℝ≥0∞) / M
                       else if (i : ℕ) = 2 then (1 : ℝ≥0∞) / M
                       else 0)
    (by
      let i0 : Fin M := ⟨0, by omega⟩
      let i2 : Fin M := ⟨2, by omega⟩
      have hi0 : (i0 : ℕ) = 0 := rfl
      have hi2 : (i2 : ℕ) = 2 := rfl
      have h02 : (0 : ℕ) ≠ 2 := by omega
      have h20 : (2 : ℕ) ≠ 0 := by omega
      have h_ne : i0 ≠ i2 := by intro h; simp [Fin.ext_iff] at h
      have h_rest : ∀ x : Fin M, x ≠ i0 ∧ x ≠ i2 →
          (if (x : ℕ) = 0 then ((M - 1 : ℕ) : ℝ≥0∞) / M
            else if (x : ℕ) = 2 then (1 : ℝ≥0∞) / M else 0) = 0 := by
        intro x hx
        have h0 : (x : ℕ) ≠ 0 := by intro h; apply hx.1; ext; exact h
        have h2 : (x : ℕ) ≠ 2 := by intro h; apply hx.2; ext; exact h
        simp [h0, h2]
      rw [Fintype.sum_eq_add i0 i2 h_ne h_rest]
      simp only [hi0, hi2, reduceIte, h02, h20]
      have h_key : ((M - 1 : ℕ) : ℝ≥0∞) + 1 = (M : ℝ≥0∞) := by norm_cast; omega
      rw [← ENNReal.add_div, h_key]
      exact ENNReal.div_self (by positivity) ENNReal.coe_ne_top)

/-- Helper: value of uniformPMF at each index -/
theorem uniformPMF_apply (M : ℕ) (hM : M ≥ 3) (i : Fin M) :
    (uniformPMF M hM i).toReal =
      if (i : ℕ) = 0 then ((M - 1 : ℕ) : ℝ) / M
      else if (i : ℕ) = 1 then (1 : ℝ) / M
      else 0 := by
  unfold uniformPMF
  rw [PMF.ofFintype_apply]
  split_ifs with h0 _ _
  · exact ennreal_coe_div_toReal (M - 1) M (by omega)
  · simp [ENNReal.toReal_div, ENNReal.toReal_natCast]
  · simp

/-- Helper: value of shiftedUniformPMF at each index -/
theorem shiftedUniformPMF_apply (M : ℕ) (hM : M ≥ 3) (i : Fin M) :
    (shiftedUniformPMF M hM i).toReal =
      if (i : ℕ) = 0 then ((M - 1 : ℕ) : ℝ) / M
      else if (i : ℕ) = 2 then (1 : ℝ) / M
      else 0 := by
  unfold shiftedUniformPMF
  rw [PMF.ofFintype_apply]
  split_ifs with _ _ _
  · exact ennreal_coe_div_toReal (M - 1) M (by omega)
  · simp [ENNReal.toReal_natCast]
  · simp

/-- H²(uniform, shifted) = 1/M.
    Both distributions place (M-1)/M at index 0.
    Index 1: P=1/M, Q=0. Index 2: P=0, Q=1/M. All others: both 0.
    H² = 1 - Σ√(p_i·q_i) = 1 - (M-1)/M = 1/M. -/
theorem hellingerSq_uniform_shift (M : ℕ) (hM : M ≥ 3) :
    hellingerSq (uniformPMF M hM) (shiftedUniformPMF M hM) = 1 / (M : ℝ) := by
  rw [hellingerSq_eq_one_minus_affinity]
  let i0 : Fin M := ⟨0, by omega⟩
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hMm1_pos : (0 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) / M := by positivity
  have h_at_rest : ∀ i : Fin M, i ≠ i0 →
      Real.sqrt ((uniformPMF M hM i).toReal *
        (shiftedUniformPMF M hM i).toReal) = 0 := by
    intro i hi
    have h_ne_0 : (i : ℕ) ≠ 0 := by intro h; apply hi; ext; exact h
    rw [uniformPMF_apply M hM i, shiftedUniformPMF_apply M hM i]
    simp only [h_ne_0, reduceIte]
    -- After simp, goal is: √((if i=1 then 1/M else 0) * (if i=2 then 1/M else 0)) = 0
    split_ifs with h1 h2
    · -- i = 1 and i = 2: impossible since 1 ≠ 2
      omega
    · -- i = 1, i ≠ 2: √(1/M * 0) = 0
      rw [mul_zero, Real.sqrt_zero]
    · -- i ≠ 1, i = 2: √(0 * 1/M) = 0
      rw [zero_mul, Real.sqrt_zero]
    · -- i ≠ 1, i ≠ 2: √(0 * 0) = 0
      rw [zero_mul, Real.sqrt_zero]
  have h_sum : ∑ i : Fin M, Real.sqrt ((uniformPMF M hM i).toReal *
      (shiftedUniformPMF M hM i).toReal) =
      Real.sqrt ((uniformPMF M hM i0).toReal * (shiftedUniformPMF M hM i0).toReal) :=
    Fintype.sum_eq_single i0 h_at_rest
  rw [h_sum]
  rw [uniformPMF_apply M hM i0, shiftedUniformPMF_apply M hM i0, hi0]
  simp only [reduceIte]
  -- Goal: 1 - √(((M-1)/M) * ((M-1)/M)) = 1/M
  -- √(x * x) = x when x ≥ 0
  rw [Real.sqrt_mul_self hMm1_pos]
  -- Goal: 1 - (M-1)/M = 1/M
  -- M = (M-1) + 1, so clear denominators
  have hM_succ : (M : ℝ) = ↑(M - 1) + 1 := by exact_mod_cast (Nat.sub_add_cancel (by omega)).symm
  have hM_pos' : (0 : ℝ) < M := by positivity
  field_simp
  linarith

-- ============================================================
-- PART 8: Grid Size Construction
-- ============================================================

theorem exists_grid_size (n : ℕ) (epsilon B : ℝ)
    (h_eps : epsilon > 0) (h_eps_bound : epsilon < 1 / (n : ℝ)) (hB : B > 0) :
    ∃ (M : ℕ) (hM : M ≥ 3),
      let Delta := (1 - (n : ℝ) * epsilon) / (n : ℝ)
      (1 : ℝ) / (M : ℝ) ≤ 16 * Delta ^ 2 / B ^ 2 ∧
      (1 : ℝ) / (M : ℝ) > 0 := by
  -- Derive n > 0 from the bound epsilon < 1/n with epsilon > 0
  have hn : (n : ℝ) > 0 := by
    -- If n = 0, then 1/(n:ℝ) = 0, contradicting epsilon > 0 < epsilon < 1/n
    -- Since n : ℕ, n ≥ 0 always, so n > 0 suffices
    exact_mod_cast Nat.pos_of_ne_zero (by
      intro h
      subst h
      simp only [Nat.cast_zero, div_zero] at h_eps_bound
      linarith)
  have h_neps_lt_1 : (n : ℝ) * epsilon < 1 := by
    -- epsilon < 1/n ↔ epsilon * n < 1. Then n * epsilon = epsilon * n < 1.
    have := (lt_div_iff₀ hn).mp h_eps_bound
    linarith
  have h_Delta_pos : (0 : ℝ) < (1 - (n : ℝ) * epsilon) / (n : ℝ) := by
    refine div_pos (sub_pos.mpr h_neps_lt_1) hn
  obtain ⟨N, hN⟩ := exists_nat_gt (B ^ 2 / (16 * ((1 - (n : ℝ) * epsilon) / (n : ℝ)) ^ 2))
  let M : ℕ := max 3 (N + 1)
  refine ⟨M, le_max_left 3 (N + 1), ?_⟩
  intro Delta
  constructor
  · -- 1/M ≤ 16·Δ²/B²
    have h16D2_pos : (0 : ℝ) < 16 * Delta ^ 2 := by positivity
    have hB2_pos : (0 : ℝ) < B ^ 2 := by positivity
    have hM_large : (max 3 (N + 1) : ℝ) > B ^ 2 / (16 * Delta ^ 2) := by
      calc (max 3 (N + 1) : ℝ)
          ≥ (N + 1 : ℝ) := by exact_mod_cast le_max_right 3 (N + 1)
        _ > (N : ℝ) := by exact_mod_cast Nat.lt_succ_self N
        _ > B ^ 2 / (16 * Delta ^ 2) := by exact_mod_cast hN
    -- M > B²/(16Δ²) implies 1/M < 16Δ²/B²
    have hM_pos : (0 : ℝ) < M := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) (le_max_left 3 (N + 1))
    -- From hM_large: B²/(16Δ²) < max 3 (↑N+1), so B² < max 3 (↑N+1) · 16Δ²
    -- Since ↑M = max 3 (↑N+1), B² < ↑M · 16Δ²
    have hB2_lt : B ^ 2 < (M : ℝ) * (16 * Delta ^ 2) := by
      have h1 : B ^ 2 < (max 3 (N + 1) : ℝ) * (16 * Delta ^ 2) :=
        (div_lt_iff₀ h16D2_pos).mp (gt_iff_lt.mp hM_large)
      exact_mod_cast h1
    -- B² < ↑M·16Δ² → B²/↑M < 16Δ²
    have h_div : B ^ 2 / (M : ℝ) < 16 * Delta ^ 2 :=
      (div_lt_iff₀ hM_pos).mpr (by rw [mul_comm]; exact hB2_lt)
    -- B²/↑M < 16Δ² and B² > 0, so 1/↑M < 16Δ²/B²
    -- Key: 1/M · B² = B²/M < 16Δ², then use lt_div_iff₀
    have h_recip_lt : (1 : ℝ) / M < 16 * Delta ^ 2 / B ^ 2 := by
      have h_mul : (1 : ℝ) / M * B ^ 2 < 16 * Delta ^ 2 := by
        rw [show (1 : ℝ) / M * B ^ 2 = B ^ 2 / M by ring]
        exact h_div
      exact (lt_div_iff₀ hB2_pos).mpr h_mul
    exact le_of_lt h_recip_lt
  · positivity

-- ============================================================
-- PART 8.5: Bhattacharyya Coefficient Infrastructure
-- ============================================================

/-- The probability of a specific sequence of K independent samples from P. -/
noncomputable def probSeq {n K : ℕ} (P : PMF (Fin n)) (x : Fin K → Fin n) : ℝ :=
  ∏ i : Fin K, (P (x i)).toReal

private lemma probSeq_nonneg {n K : ℕ} (P : PMF (Fin n)) (x : Fin K → Fin n) :
    0 ≤ probSeq P x := by
  unfold probSeq
  exact Finset.prod_nonneg (fun i _ => (P (x i)).toReal_nonneg)

private noncomputable def bc {n : ℕ} (P Q : PMF (Fin n)) : ℝ :=
  ∑ i : Fin n, Real.sqrt ((P i).toReal * (Q i).toReal)

private noncomputable def bc_prod {n K : ℕ} (P Q : PMF (Fin n)) : ℝ :=
  ∑ x : Fin K → Fin n, Real.sqrt (probSeq P x * probSeq Q x)

private lemma bc_eq_one_sub_hellingerSq {n : ℕ} (P Q : PMF (Fin n)) :
    bc P Q = 1 - hellingerSq P Q := by
  unfold bc hellingerSq
  -- Expand each term: (√p_i - √q_i)² = p_i + q_i - 2·√(p_i·q_i)
  have h_sq : ∀ i : Fin n, (Real.sqrt ((P i).toReal) - Real.sqrt ((Q i).toReal)) ^ 2 =
      (P i).toReal + (Q i).toReal - 2 * Real.sqrt ((P i).toReal * (Q i).toReal) := by
    intro i
    have ha := (P i).toReal_nonneg
    have hb := (Q i).toReal_nonneg
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    -- (√p - √q)² = (√p)² - 2·√p·√q + (√q)² by sub_sq
    -- Then simplify (√p)² = p, (√q)² = q
    conv_lhs => rw [sub_sq]
    simp only [h1, h2]
    rw [Real.sqrt_mul ha]
    ring
  simp only [h_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [pmf_toReal_sum_eq_one P, pmf_toReal_sum_eq_one Q, ← Finset.mul_sum]
  ring

private lemma bc_nonneg {n : ℕ} (P Q : PMF (Fin n)) :
    0 ≤ bc P Q := by
  unfold bc; exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

private lemma bc_le_one {n : ℕ} (P Q : PMF (Fin n)) :
    bc P Q ≤ 1 := by
  rw [bc_eq_one_sub_hellingerSq]
  exact sub_le_self 1 (hellingerSq_nonneg P Q)

private lemma real_sqrt_prod_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [Real.sqrt_mul (hf a (Finset.mem_insert_self _ _))]
    rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma bc_prod_eq_pow {n K : ℕ} (P Q : PMF (Fin n)) :
    @bc_prod n K P Q = (bc P Q) ^ K := by
  unfold bc_prod bc probSeq
  -- Key: Σ_x ∏_i √(p(x_i)·q(x_i)) = ∏_i Σ_j √(p_j·q_j) = (BC)^K
  have h1 : ∀ x : Fin K → Fin n,
      Real.sqrt ((∏ i : Fin K, (P (x i)).toReal) * ∏ i : Fin K, (Q (x i)).toReal) =
      ∏ i : Fin K, Real.sqrt ((P (x i)).toReal * (Q (x i)).toReal) := by
    intro x
    rw [← Finset.prod_mul_distrib]
    exact real_sqrt_prod_finset Finset.univ (fun i => (P (x i)).toReal * (Q (x i)).toReal)
      (fun i _ => mul_nonneg ((P (x i)).toReal_nonneg) ((Q (x i)).toReal_nonneg))
  have h_univ : (Finset.univ : Finset (Fin K → Fin n)) =
      Fintype.piFinset fun _ : Fin K => (Finset.univ : Finset (Fin n)) := by
    ext f; simp
  have h2 : (∑ x : Fin K → Fin n, ∏ i : Fin K, Real.sqrt ((P (x i)).toReal * (Q (x i)).toReal)) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin K => (Finset.univ : Finset (Fin n))),
        ∏ i : Fin K, Real.sqrt ((P (x i)).toReal * (Q (x i)).toReal) := by
    have : (Finset.univ : Finset (Fin K → Fin n)) = Fintype.piFinset fun _ : Fin K => (Finset.univ : Finset (Fin n)) := by ext f; simp
    simp [← this]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), h2,
    Finset.sum_prod_piFinset (Finset.univ : Finset (Fin n))
      fun (_ : Fin K) (j : Fin n) => Real.sqrt ((P j).toReal * (Q j).toReal)]
  rw [Finset.prod_const, Finset.card_fin]

private lemma pow_le_one_real (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) (K : ℕ) :
    x ^ K ≤ 1 := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (mul_le_mul ih h2 h1 (by norm_num)).trans_eq (mul_one 1)

private lemma bc_prod_le_one {n K : ℕ} (P Q : PMF (Fin n)) :
    @bc_prod n K P Q ≤ 1 := by
  rw [bc_prod_eq_pow]
  exact pow_le_one_real (bc P Q) (bc_nonneg P Q) (bc_le_one P Q) K

private lemma abs_sub_eq_mul_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| = |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) := by
  have h_sqrt_mul : ∀ {x : ℝ} (hx : 0 ≤ x), Real.sqrt x * Real.sqrt x = x := by
    intro x hx; nlinarith [Real.sq_sqrt hx]
  have h1 := h_sqrt_mul ha
  have h2 := h_sqrt_mul hb
  have h_prod : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by linarith
  rw [← h_prod, abs_mul]
  rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]

private lemma abs_sq_eq_sq (x : ℝ) : |x| ^ 2 = x ^ 2 := by
  rw [sq_abs]

private lemma sum_cauchy_schwarz (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have h_sq := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hs1 : 0 ≤ ∑ i ∈ s, f i * g i := Finset.sum_nonneg (fun i hi => mul_nonneg (hf i hi) (hg i hi))
  have hs2 : 0 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_le := (Real.le_sqrt hs1 hs2).mpr h_sq
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h_le
  exact h_le

-- ============================================================
-- PART 9: Le Cam's Lemma
-- ============================================================

/-- A statistical test T based on K samples correctly identifies P or Q
    with success probability ≥ 2/3 under both hypotheses. -/
def SuccessProbAtLeastTwoThirds {n : ℕ} (P Q : PMF (Fin n)) (K : ℕ) : Prop :=
  ∃ (T : (Fin K → Fin n) → Bool),
    (∑ x : (Fin K → Fin n), if T x = true then probSeq P x else 0) ≥ (2 / 3 : ℝ) ∧
    (∑ x : (Fin K → Fin n), if T x = false then probSeq Q x else 0) ≥ (2 / 3 : ℝ)

/-- Total Variation distance between K-fold product PMFs. -/
noncomputable def TV_prod (n K : ℕ) (P Q : PMF (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : (Fin K → Fin n), |probSeq P x - probSeq Q x|

/-- Product PMF normalization: Σ_x probSeq P x = 1.
    This follows from Fintype.prod_univ_sum (the tensorization of finite sums). -/
theorem probSeq_sum_eq_one {n K : ℕ} (P : PMF (Fin n)) :
    ∑ x : Fin K → Fin n, probSeq P x = 1 := by
  unfold probSeq
  -- Goal: ∑ x : Fin K → Fin n, ∏ i : Fin K, (P (x i)).toReal = 1
  -- Key: ∑ x, ∏ i, f (x i) = ∏ i, ∑ j, f j  when f is independent of i
  -- This is Finset.sum_prod_piFinset with s = univ
  rw [show (∑ x : Fin K → Fin n, ∏ i : Fin K, (P (x i)).toReal) =
      ∑ x ∈ (Fintype.piFinset fun _ : Fin K => (Finset.univ : Finset (Fin n))),
        ∏ i : Fin K, (P (x i)).toReal by
        simp only [Fintype.piFinset_univ]]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset (Fin n))
      (fun (_i : Fin K) (j : Fin n) => (P j).toReal)]
  simp only [pmf_toReal_sum_eq_one P, Finset.prod_const_one]

/-- Key identity: min(a,b) + |a - b| = max(a,b).
    Proved by case split on a ≤ b. -/
private lemma min_add_abs_eq_max (a b : ℝ) :
    min a b + |a - b| = max a b := by
  by_cases h : a ≤ b
  case pos =>
    have hab : a - b ≤ 0 := by linarith
    rw [min_eq_left h, max_eq_right h, abs_of_nonpos hab]; linarith
  case neg =>
    have hab : b ≤ a := by linarith
    have hab2 : 0 ≤ a - b := by linarith
    rw [min_eq_right hab, max_eq_left hab, abs_of_nonneg hab2]; linarith

/-- Key identity: min(a,b) = (a + b) / 2 - |a - b| / 2. -/
private lemma min_eq_half_sub_abs (a b : ℝ) :
    min a b = (a + b) / 2 - |a - b| / 2 := by
  by_cases h : a ≤ b
  case pos =>
    have hab : a - b ≤ 0 := by linarith
    rw [min_eq_left h, abs_of_nonpos hab]; linarith
  case neg =>
    have hab : b ≤ a := by linarith
    have hab2 : 0 ≤ a - b := by linarith
    rw [min_eq_right hab, abs_of_nonneg hab2]; linarith

/-- TV identity: Σ min(p_x, q_x) = 1 - TV(P^K, Q^K).
    Follows from Σ min = (Σ(p+q))/2 - Σ|p-q|/2 = 1 - TV. -/
private theorem sum_min_eq_one_sub_tv (n K : ℕ) (P Q : PMF (Fin n)) :
    ∑ x : Fin K → Fin n, min (probSeq P x) (probSeq Q x) =
      1 - TV_prod n K P Q := by
  -- Strategy: Σ min = Σ [(p+q)/2 - |p-q|/2]
  --   = (Σ p + Σ q) / 2 - Σ |p-q| / 2
  --   = (1 + 1) / 2 - Σ |p-q| / 2
  --   = 1 - (1/2) * Σ |p-q|
  --   = 1 - TV
  have h_key : ∀ (x : Fin K → Fin n), min (probSeq P x) (probSeq Q x) =
      (probSeq P x + probSeq Q x) / 2 - |probSeq P x - probSeq Q x| / 2 :=
    fun x => min_eq_half_sub_abs (probSeq P x) (probSeq Q x)
  simp only [h_key, Finset.sum_sub_distrib]
  -- Goal: ∑ x, (probSeq P x + probSeq Q x) / 2 - ∑ x, |probSeq P x - probSeq Q x| / 2 = 1 - TV
  -- Pull out /2 from both sums using Finset.sum_div
  rw [← Finset.sum_div Finset.univ (fun x => probSeq P x + probSeq Q x) 2]
  rw [← Finset.sum_div Finset.univ (fun x => |probSeq P x - probSeq Q x|) 2]
  -- Now: (∑ (P + Q)) / 2 - (∑ |P - Q|) / 2 = 1 - TV
  rw [Finset.sum_add_distrib]
  rw [probSeq_sum_eq_one (K := K) P, probSeq_sum_eq_one (K := K) Q]
  -- Now: (1 + 1) / 2 - (∑ |P - Q|) / 2 = 1 - TV
  unfold TV_prod
  ring

/-- For any x, if T x = true then p_x else q_x ≤ max(p_x, q_x). -/
private lemma ite_le_max (T : Bool) (p_x q_x : ℝ) :
    (if T = true then p_x else q_x) ≤ max p_x q_x := by
  cases T <;> simp [le_max_left, le_max_right]

/-- Lemma 1: Any statistical test's success probabilities are bounded by TV.
    For any test T: P(T=true) + Q(T=false) ≤ 1 + TV(P^K, Q^K).
    Proof: P(T=true) + Q(T=false) = Σ [if T x then p_x else q_x]
    ≤ Σ max(p_x, q_x) = Σ (min(p_x, q_x) + |p_x - q_x|) = (1 - TV) + 2·TV = 1 + TV. -/
lemma success_prob_bound_tv (n K : ℕ) (P Q : PMF (Fin n)) (T : (Fin K → Fin n) → Bool) :
    (∑ x : (Fin K → Fin n), if T x = true then probSeq P x else 0) +
    (∑ x : (Fin K → Fin n), if T x = false then probSeq Q x else 0) ≤ (1 : ℝ) + TV_prod n K P Q := by
  -- Step 1: Combine the two sums into one
  rw [Finset.sum_add_distrib.symm]
  -- Step 2: Simplify each summand: if T x then p_x else q_x
  have h_simp : ∀ (x : Fin K → Fin n),
      (if T x = true then probSeq P x else 0) +
      (if T x = false then probSeq Q x else 0) =
      (if T x = true then probSeq P x else probSeq Q x) := by
    intro x; cases T x <;> simp
  simp only [h_simp]
  -- Step 3: Bound by max
  have h_le_max : ∀ (x : Fin K → Fin n),
      (if T x = true then probSeq P x else probSeq Q x) ≤
      max (probSeq P x) (probSeq Q x) :=
    fun x => by cases T x <;> simp
  have h_sum_le : ∑ x : (Fin K → Fin n),
      (if T x = true then probSeq P x else probSeq Q x) ≤
      ∑ x : (Fin K → Fin n), max (probSeq P x) (probSeq Q x) :=
    Finset.sum_le_sum fun x _ => h_le_max x
  -- Step 4: max = min + |diff|
  have h_max_eq : ∀ (x : Fin K → Fin n), max (probSeq P x) (probSeq Q x) =
      min (probSeq P x) (probSeq Q x) + |probSeq P x - probSeq Q x| :=
    fun x => (min_add_abs_eq_max _ _).symm
  simp only [h_max_eq, Finset.sum_add_distrib] at h_sum_le
  -- Step 5: Use TV identity
  rw [sum_min_eq_one_sub_tv n K P Q] at h_sum_le
  unfold TV_prod at h_sum_le
  -- h_sum_le: ∑ (if T x then P x else Q x) ≤ 1 - 1/2 * S + S  where S = ∑ |P-Q|
  -- Goal: ∑ (if T x then P x else Q x) ≤ 1 + TV_prod = 1 + 1/2 * S
  -- Key: 1 - S/2 + S = 1 + S/2
  have h_ringsimp : 1 - (1 / 2 : ℝ) * ∑ x : (Fin K → Fin n), |probSeq P x - probSeq Q x| +
      ∑ x : (Fin K → Fin n), |probSeq P x - probSeq Q x| =
      1 + (1 / 2 : ℝ) * ∑ x : (Fin K → Fin n), |probSeq P x - probSeq Q x| := by ring
  rw [h_ringsimp] at h_sum_le
  -- Now h_sum_le: ∑ (if T x then P x else Q x) ≤ 1 + 1/2 * ∑ |P-Q| = 1 + TV
  -- And goal is: ∑ (if T x then P x else Q x) ≤ 1 + TV
  unfold TV_prod
  exact h_sum_le

/-- Lemma 2 (intermediate): TV bounded by √(2·(1 - BC(P^K,Q^K))).
    Uses Cauchy-Schwarz on |√p-√q|·(√p+√q) = |p-q|. -/
private lemma tv_le_sqrt_one_sub_bc {n K : ℕ} (P Q : PMF (Fin n)) :
    TV_prod n K P Q ≤ Real.sqrt (2 * (1 - @bc_prod n K P Q)) := by
  unfold TV_prod
  -- Rewrite |probSeq P x - probSeq Q x| = |√P_x - √Q_x| * (√P_x + √Q_x)
  have h_eq : ∀ x : Fin K → Fin n, |probSeq P x - probSeq Q x| =
      |Real.sqrt (probSeq P x) - Real.sqrt (probSeq Q x)| *
      (Real.sqrt (probSeq P x) + Real.sqrt (probSeq Q x)) := by
    intro x; exact abs_sub_eq_mul_sqrt (probSeq P x) (probSeq Q x)
        (probSeq_nonneg P x) (probSeq_nonneg Q x)
  rw [Finset.sum_congr rfl (fun x _ => h_eq x)]
  -- Apply Cauchy-Schwarz to the sum
  have h_cs := sum_cauchy_schwarz (Finset.univ : Finset (Fin K → Fin n))
    (fun x => |Real.sqrt (probSeq P x) - Real.sqrt (probSeq Q x)|)
    (fun x => Real.sqrt (probSeq P x) + Real.sqrt (probSeq Q x))
    (fun x _ => abs_nonneg _) (fun x _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- Simplify |a|^2 = a^2 for the first factor
  rw [Finset.sum_congr rfl (fun i _ => abs_sq_eq_sq _)] at h_cs
  -- Compute the two squared-sum terms
  have h_sub_sq : ∑ x : Fin K → Fin n,
      (Real.sqrt (probSeq P x) - Real.sqrt (probSeq Q x)) ^ 2 =
      2 - 2 * @bc_prod n K P Q := by
    have hs : ∀ x : Fin K → Fin n, (Real.sqrt (probSeq P x) - Real.sqrt (probSeq Q x)) ^ 2 =
        probSeq P x + probSeq Q x - 2 * Real.sqrt (probSeq P x * probSeq Q x) := by
      intro x
      have ha := probSeq_nonneg P x
      have hb := probSeq_nonneg Q x
      conv_lhs => rw [sub_sq]
      simp only [Real.sq_sqrt ha, Real.sq_sqrt hb]
      rw [Real.sqrt_mul ha]
      ring
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, probSeq_sum_eq_one P, probSeq_sum_eq_one Q, ← Finset.mul_sum]
    unfold bc_prod; ring
  have h_add_sq : ∑ x : Fin K → Fin n,
      (Real.sqrt (probSeq P x) + Real.sqrt (probSeq Q x)) ^ 2 =
      2 + 2 * @bc_prod n K P Q := by
    have hs : ∀ x : Fin K → Fin n, (Real.sqrt (probSeq P x) + Real.sqrt (probSeq Q x)) ^ 2 =
        probSeq P x + probSeq Q x + 2 * Real.sqrt (probSeq P x * probSeq Q x) := by
      intro x
      have ha := probSeq_nonneg P x
      have hb := probSeq_nonneg Q x
      conv_lhs => rw [add_sq]
      simp only [Real.sq_sqrt ha, Real.sq_sqrt hb]
      rw [Real.sqrt_mul ha]
      ring
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_add_distrib,
      Finset.sum_add_distrib, probSeq_sum_eq_one P, probSeq_sum_eq_one Q, ← Finset.mul_sum]
    unfold bc_prod; ring
  rw [h_sub_sq, h_add_sq] at h_cs
  -- Bound: √(2+2BC) ≤ √4 = 2 since BC ≤ 1
  have h_add_le : 2 + 2 * @bc_prod n K P Q ≤ 4 := by linarith [@bc_prod_le_one n K P Q]
  have h_sqrt_add : Real.sqrt (2 + 2 * @bc_prod n K P Q) ≤ 2 := by
    calc Real.sqrt (2 + 2 * @bc_prod n K P Q) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h_add_le
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h_cs3 : Real.sqrt (2 - 2 * @bc_prod n K P Q) * Real.sqrt (2 + 2 * @bc_prod n K P Q) ≤
      Real.sqrt (2 - 2 * @bc_prod n K P Q) * 2 :=
    mul_le_mul_of_nonneg_left h_sqrt_add (Real.sqrt_nonneg _)
  have h_cs4 := le_trans h_cs h_cs3
  -- Combine: TV = (1/2) * sum ≤ (1/2) * √(2-2BC) * 2 = √(2-2BC) = √(2(1-BC))
  calc (1 / 2 : ℝ) * ∑ x : Fin K → Fin n,
        |Real.sqrt (probSeq P x) - Real.sqrt (probSeq Q x)| *
        (Real.sqrt (probSeq P x) + Real.sqrt (probSeq Q x))
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (2 - 2 * @bc_prod n K P Q) * 2) :=
        mul_le_mul_of_nonneg_left h_cs4 (by norm_num)
    _ = Real.sqrt (2 * (1 - @bc_prod n K P Q)) := by ring

/-- Lemma 2: TV(P^K, Q^K) ≤ √(2 · K · H²(P,Q)).
    Uses Cauchy-Schwarz for the TV-BC bound, BC tensorization, and Bernoulli's inequality.

    NOTE: The bound TV ≤ √(K·H²) is mathematically false under the standard definition
    of H² with the 1/2 factor. The correct tight bound is TV ≤ √(2·K·H²). -/
lemma tv_le_sqrt_k_hellinger (n K : ℕ) (P Q : PMF (Fin n)) :
    TV_prod n K P Q ≤ Real.sqrt (2 * (K : ℝ) * hellingerSq P Q) := by
  have h1 := @tv_le_sqrt_one_sub_bc n K P Q
  -- Bernoulli: 1 - BC^K ≤ K·H², i.e., 1 - (1-H²)^K ≤ K·H²
  have h2 : 1 - @bc_prod n K P Q ≤ (K : ℝ) * hellingerSq P Q := by
    rw [@bc_prod_eq_pow n K P Q, bc_eq_one_sub_hellingerSq P Q]
    have h_bern := one_add_mul_le_pow (show (-(2 : ℝ)) ≤ -hellingerSq P Q by
      have hBC : 0 ≤ bc P Q := bc_nonneg P Q
      rw [bc_eq_one_sub_hellingerSq P Q] at hBC
      linarith) K
    -- h_bern : 1 + K*(-H²) ≤ (1 + (-H²))^K, i.e., 1 - K*H² ≤ (1-H²)^K
    -- Rearranging: 1 - (1-H²)^K ≤ K*H²
    -- Key: rewrite 1 + (-H²) as 1 - H² and 1 + K*(-H²) as 1 - K*H²
    have h_base : (1 : ℝ) + -hellingerSq P Q = 1 - hellingerSq P Q := by ring
    have h_lhs : (1 : ℝ) + (K : ℝ) * -hellingerSq P Q = 1 - (K : ℝ) * hellingerSq P Q := by ring
    rw [h_base, h_lhs] at h_bern
    -- h_bern now: 1 - K*H² ≤ (1-H²)^K
    -- Goal: 1 - (1-H²)^K ≤ K*H²
    -- From h_bern: (1-H²)^K ≥ 1 - K*H², so -(1-H²)^K ≤ -(1-K*H²) = K*H² - 1
    -- So: 1 - (1-H²)^K ≤ K*H²
    linarith
  -- Combine: TV ≤ √(2·(1-BC)) ≤ √(2·K·H²)
  have h3 : 2 * (1 - @bc_prod n K P Q) ≤ 2 * ((K : ℝ) * hellingerSq P Q) := by linarith
  have h3' : 2 * (1 - @bc_prod n K P Q) ≤ 2 * (K : ℝ) * hellingerSq P Q := by linarith
  exact le_trans h1 (Real.sqrt_le_sqrt h3')

/-- Lemma 3: Squaring preserves inequality for non-negative values.
    If 1/3 ≤ √x, then 1/9 ≤ x. -/
lemma le_cam_algebra (x : ℝ) (h : (1 / 3 : ℝ) ≤ Real.sqrt x) : (1 / 9 : ℝ) ≤ x := by
  have h0 : (0 : ℝ) < 1 / 3 := by norm_num
  have hx : (0 : ℝ) ≤ x := by
    by_contra h_neg
    push_neg at h_neg
    have : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h_neg)
    linarith
  rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num]
  exact (Real.le_sqrt (le_of_lt h0) hx).mp h

/-- Le Cam's two-point method (Tsybakov 2009, Proposition 2.2).
    If a test achieves success probability ≥ 2/3 with K i.i.d. samples,
    then K · H²(P,Q) ≥ 1/18. -/
theorem le_cam_sample_bound {n : ℕ} (P Q : PMF (Fin n)) (K : ℕ) (hK : K > 0) :
    SuccessProbAtLeastTwoThirds P Q K → (K : ℝ) * hellingerSq P Q ≥ 1 / 18 := by
  intro h_succ
  rcases h_succ with ⟨T, hP, hQ⟩
  -- Sum of correct identifications ≥ 4/3
  have h_sum : (4 / 3 : ℝ) ≤
      (∑ x : (Fin K → Fin n), if T x = true then probSeq P x else 0) +
      (∑ x : (Fin K → Fin n), if T x = false then probSeq Q x else 0) := by linarith
  -- Apply TV bound: sum ≤ 1 + TV, so TV ≥ 1/3
  have h_bound := success_prob_bound_tv n K P Q T
  have h_tv : (1 / 3 : ℝ) ≤ TV_prod n K P Q := by linarith
  -- Tensorize: TV ≤ √(2·K·H²), so √(2·K·H²) ≥ 1/3
  have h_tv_le := tv_le_sqrt_k_hellinger n K P Q
  have h_sqrt : (1 / 3 : ℝ) ≤ Real.sqrt (2 * (K : ℝ) * hellingerSq P Q) := by linarith
  -- Square both sides: 2·K·H² ≥ 1/9, so K·H² ≥ 1/18
  have h_sq : (1 / 9 : ℝ) ≤ 2 * (K : ℝ) * hellingerSq P Q :=
    le_cam_algebra (2 * (K : ℝ) * hellingerSq P Q) h_sqrt
  linarith

-- ============================================================
-- PART 10: Main Sample Complexity Theorem
-- ============================================================

/--
**Theorem 4 (Tight Sample Lower Bound):** Any independent batch evaluation strategy
that correctly ranks candidates with success probability ≥ 2/3 requires
K = Ω(n² B² / (1 - nε)²). Specifically, for K < c·n²·B²/(1-nε)² with c = 1/288,
success probability ≥ 2/3 is impossible on the shifted uniform distributions.
-/
theorem tight_sample_lower_bound (n : ℕ) (hn : n ≥ 2)
    (epsilon B : ℝ) (h_eps : epsilon > 0) (h_eps_bound : epsilon < 1 / (n : ℝ)) (hB : B > 0) :
    ∃ c : ℝ, c > 0 ∧
      ∀ K : ℕ, K > 0 →
        (K : ℝ) < c * (n : ℝ) ^ 2 * B ^ 2 / (1 - (n : ℝ) * epsilon) ^ 2 →
        ∃ (M : ℕ) (hM : M ≥ 3),
          ¬ SuccessProbAtLeastTwoThirds (uniformPMF M hM) (shiftedUniformPMF M hM) K := by
  use (1 / 288 : ℝ)
  refine ⟨by norm_num, ?_⟩
  intro K hK hK_bound
  obtain ⟨M, hM, h_dist_bound, h_dist_pos⟩ := exists_grid_size n epsilon B h_eps h_eps_bound hB
  refine ⟨M, hM, ?_⟩
  intro h_success
  -- From Le Cam: K · H²(P,Q) ≥ 1/18
  have h_le_cam : (K : ℝ) * hellingerSq (uniformPMF M hM) (shiftedUniformPMF M hM) ≥ 1 / 18 :=
    le_cam_sample_bound (uniformPMF M hM) (shiftedUniformPMF M hM) K hK h_success
  rw [hellingerSq_uniform_shift M hM] at h_le_cam
  -- h_le_cam : K * (1/M) ≥ 1/18
  -- h_dist_bound : 1/M ≤ 16·Δ²/B²
  -- hK_bound : K < (1/288)·n²·B²/(1-nε)²
  -- Need: K * (1/M) < 1/18 (contradiction)
  set Delta := (1 - (n : ℝ) * epsilon) / (n : ℝ)
  have h_KM_upper : (K : ℝ) * (1 / (M : ℝ)) < 1 / 18 := by
    -- Step 1: K/M ≤ K · 16·Δ²/B²
    have h_bound : (1 : ℝ) / (M : ℝ) ≤ 16 * Delta ^ 2 / B ^ 2 := h_dist_bound
    have h_step1 : (K : ℝ) * (1 / (M : ℝ)) ≤ (K : ℝ) * (16 * Delta ^ 2 / B ^ 2) :=
      mul_le_mul_of_nonneg_left h_bound (by positivity)
    -- Step 2: K · 16·Δ²/B² < 1/18
    -- K < (1/288)·n²·B²/(1-nε)²
    -- K · 16·((1-nε)/n)²/B² < (1/288)·16 = 16/288 = 1/18
    have hn_pos : (n : ℝ) > 0 := by positivity
    have h_one_minus_neps_pos : (0 : ℝ) < 1 - (n : ℝ) * epsilon := by
      have := (lt_div_iff₀ hn_pos).mp h_eps_bound
      linarith
    have h_step2 : (K : ℝ) * (16 * Delta ^ 2 / B ^ 2) < 1 / 18 := by
      have h_factor_pos : (0 : ℝ) < 16 * Delta ^ 2 / B ^ 2 := by positivity
      calc (K : ℝ) * (16 * Delta ^ 2 / B ^ 2)
          < (1 / 288) * (n : ℝ) ^ 2 * B ^ 2 / (1 - (n : ℝ) * epsilon) ^ 2
              * (16 * Delta ^ 2 / B ^ 2) := by
              exact mul_lt_mul_of_pos_right hK_bound h_factor_pos
        _ = 1 / 18 := by
              unfold Delta
              field_simp
              norm_num
    exact lt_of_le_of_lt h_step1 h_step2
  -- Contradiction: K/M ≥ 1/18 and K/M < 1/18
  linarith

end LeCamLowerBound
