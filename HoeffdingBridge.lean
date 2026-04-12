import LintOptions
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Hoeffding

open MeasureTheory ProbabilityTheory Real

namespace HoeffdingBridge

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-!
# Hoeffding Constant Bridge

This module derives the **exact algebraic constant** `128n²` used in the
batch-evaluation sample complexity bound. It proves that applying Hoeffding's
Inequality to:
- payoff range `[a, b] = [-2, 2]` (diameter 4)
- tolerance `ε = 1/(4n)`

yields the exponent `-K/(128n²)`, connecting the measure-theoretic
`hoeffding_inequality_iid_bounded` in `Hoeffding.lean` to the algebraic
`hoeffding_batch_sample_complexity` in `CoevolutionDeepBounds.lean`.
-/

/--
The core algebraic identity: setting ε = K/(4n) in Hoeffding's exponent
for N=K i.i.d. [-2,2]-bounded payoffs yields the exponent K/(128n²).

Specifically: `(K / 4n)² / (2K · ((b-a)/2)²) = K/(128n²)`
where `a = -2`, `b = 2`.
-/
theorem hoeffding_constant_derivation (n K : ℝ) (hn : n > 0) (hK : K > 0) :
    (K / (4 * n))^2 / (2 * K * ((2 - (-2 : ℝ)) / 2)^2) = K / (128 * n^2) := by
  have hn2 : n^2 > 0 := by positivity
  field_simp
  ring

/--
**Full Bridge Theorem.** For the CoEA batch evaluator where each payoff
lies in [-2, 2], evaluating each offspring against K random opponents, the
Hoeffding failure probability per offspring with average error tolerance 1/(4n)
(i.e. sum error tolerance K/(4n)) is bounded by the algebraic constant `exp(-K/(128n²))`.

This directly invokes `hoeffding_inequality_iid_bounded` and performs
the rewrite using `hoeffding_constant_derivation`.
-/
theorem hoeffding_per_offspring_bound
    (n : ℝ) (hn : n > 0)
    (K : ℕ) (hK : (K:ℝ) > 0)
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X volume)
    (h_meas : ∀ i, AEMeasurable (X i) volume)
    (h_bound : ∀ i, i < K → ∀ᵐ ω ∂volume, X i ω ∈ Set.Icc (-2 : ℝ) 2) :
    let Y : ℕ → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂volume
    volume.real {ω | (K:ℝ) / (4 * n) ≤ ∑ i ∈ Finset.range K, Y i ω}
      ≤ rexp (-(K:ℝ) / (128 * n^2)) := by
  intro Y
  have h_eps : 0 ≤ (K:ℝ) / (4 * n) := le_of_lt (by positivity)
  -- Get the native measure-theoretic bound
  have h_base := hoeffding_inequality_iid_bounded K X (-2 : ℝ) 2 h_indep h_meas h_bound ((K:ℝ) / (4 * n)) h_eps
  
  -- The exponent in h_base contains ↑‖2 - -2‖₊ which is a NNReal coerced to Real.
  -- We simplify it to match our algebraic term.
  have h_norm_simp : (↑‖(2 : ℝ) - -2‖₊ : ℝ) = 2 - (-2 : ℝ) := by norm_num
  rw [h_norm_simp] at h_base
  
  -- The exponent in h_base is now exactly computable to our algebra:
  have h_alg := hoeffding_constant_derivation n (K:ℝ) hn hK
  
  -- The exponent parses as -(A^2)/B, while h_alg negates to -(A^2/B).
  -- We prove they evaluate to the exact same value.
  have h_eq : -((K:ℝ) / (4 * n))^2 / (2 * (K:ℝ) * ((2 - (-2 : ℝ)) / 2)^2) = -((K:ℝ) / (128 * n^2)) := by
    calc -((K:ℝ) / (4 * n))^2 / (2 * (K:ℝ) * ((2 - (-2 : ℝ)) / 2)^2)
      _ = -(((K:ℝ) / (4 * n))^2 / (2 * (K:ℝ) * ((2 - (-2 : ℝ)) / 2)^2)) := by ring
      _ = -((K:ℝ) / (128 * n^2)) := by rw [h_alg]
      _ = -((K:ℝ) / (128 * n^2)) := by ring
    
  -- Now rewrite the RHS of h_base
  rw [h_eq] at h_base
  
  -- h_base now has exponent -(K / 128n^2), but our goal expects -K / 128n^2.
  -- These are algebraically equal but syntactically distinct, so we must rewrite.
  have h_neg_eq : -((K:ℝ) / (128 * n^2)) = -(K:ℝ) / (128 * n^2) := by ring
  rw [h_neg_eq] at h_base
  
  -- The let-binding in h_base's type is definitionally equal to our local Y
  exact h_base

end HoeffdingBridge
