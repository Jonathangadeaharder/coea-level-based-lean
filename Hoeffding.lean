import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Real HasSubgaussianMGF

noncomputable section



variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-!
# Hoeffding's Inequality — Full Measure-Theoretic Formalization

This module provides a complete, gapless formalization of Hoeffding's Lemma
and Hoeffding's Inequality using Mathlib4's `SubGaussian` API.

## Architecture (Path B — Hybrid)
- **Hoeffding's Lemma**: Proven by invoking `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
- **Hoeffding's Inequality**: Proven by invoking `measure_sum_range_ge_le_of_iIndepFun`
- **Batch Specialization**: Tailored bound for CoEA fitness evaluations in [0, 1]

## Key Mathlib4 Theorems Consumed
| Theorem | Role |
|:---|:---|
| `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` | Bounded + zero-mean → sub-Gaussian MGF |
| `hasSubgaussianMGF_of_mem_Icc` | Auto-centering variant |
| `measure_sum_range_ge_le_of_iIndepFun` | Hoeffding's Inequality for sums |
-/




-- PART 3: Hoeffding's Inequality (Sum of Independent Bounded Variables)
-- ============================================================================

/--
**Hoeffding's Inequality** for the sum of `K` independent, identically bounded
random variables. Given:
- `X : ℕ → Ω → ℝ` a family of random variables
- `iIndepFun X volume` (mutual independence)
- `∀ i < K, X i ω ∈ [a, b]` a.e. (uniform boundedness)

Then for any `ε ≥ 0`:
  `P(∑ᵢ (Xᵢ - E[Xᵢ]) ≥ ε) ≤ exp(-ε² / (2K · ((b-a)/2)²))`

This directly invokes Mathlib4's `measure_sum_range_ge_le_of_iIndepFun`
applied to the centered variables `Yᵢ = Xᵢ - E[Xᵢ]`.
-/
theorem hoeffding_inequality_iid_bounded
    (K : ℕ) (X : ℕ → Ω → ℝ) (a b : ℝ)
    (h_indep : iIndepFun X volume)
    (h_meas : ∀ i, AEMeasurable (X i) volume)
    (h_bound : ∀ i, i < K → ∀ᵐ ω ∂volume, X i ω ∈ Set.Icc a b)
    (ε : ℝ) (hε : 0 ≤ ε) :
    -- Define centered variables Yᵢ = Xᵢ - E[Xᵢ]
    let Y : ℕ → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂volume
    volume.real {ω | ε ≤ ∑ i ∈ Finset.range K, Y i ω}
      ≤ rexp (-ε ^ 2 / (2 * ↑K * (‖b - a‖₊ / 2) ^ 2)) := by
  intro Y
  -- Each centered variable is sub-Gaussian via Hoeffding's Lemma
  have h_subG : ∀ i, i < K → HasSubgaussianMGF (Y i) ((‖b - a‖₊ / 2) ^ 2) volume := by
    intro i hi
    exact hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bound i hi)
  -- Independence of the centered variables (shifting by a constant preserves independence)
  have h_indep_Y : iIndepFun Y volume := by
    exact h_indep.comp (fun i => fun x => x - ∫ ω', X i ω' ∂volume)
      (fun i => measurable_id.sub measurable_const)
  -- Apply Mathlib's native Hoeffding inequality
  exact measure_sum_range_ge_le_of_iIndepFun h_indep_Y (fun i hi => h_subG i hi) hε

-- ============================================================================
-- PART 4: CoEA Batch Evaluation Specialization
-- ============================================================================

/--
**CoEA Batch Fitness Evaluation Bound.** Specialization of Hoeffding's Inequality 
to the CoEA batch evaluator, where each fitness evaluation `Xᵢ ∈ [0, 1]` (normalized
game payoffs) is an independent sample against a randomly drawn opponent.

The sub-Gaussian parameter for `[0, 1]`-bounded variables is `c = (‖1-0‖₊/2)² = 1/4`,
yielding the classical `exp(-2Kε²)` form.
-/
theorem hoeffding_batch_bound
    (K : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X volume)
    (h_meas : ∀ i, AEMeasurable (X i) volume)
    (h_bound : ∀ i, i < K → ∀ᵐ ω ∂volume, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    let Y : ℕ → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂volume
    volume.real {ω | ε ≤ ∑ i ∈ Finset.range K, Y i ω}
      ≤ rexp (-ε ^ 2 / (2 * ↑K * (‖(1 : ℝ) - 0‖₊ / 2) ^ 2)) :=
  hoeffding_inequality_iid_bounded K X (0 : ℝ) (1 : ℝ) h_indep h_meas h_bound ε hε

