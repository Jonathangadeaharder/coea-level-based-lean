import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DriftTheorems.AdditiveDrift

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace DriftTheorems

variable {Ω : Type*} [m0 : MeasureSpace Ω]
variable {F : Filtration ℕ m0.toMeasurableSpace}

/-- 
  The Multiplicative Drift Theorem (Doerr, Johannsen, Winzen 2012).
  
  If a stochastic process (X_t) adapted to F satisfies a proportional expected 
  decrease whenever X_t ≥ s_min:
      E[X_t - X_{t+1} | F_t] 𝟙_{τ > t} ≥ (δ * X_t) 𝟙_{τ > t}
      
  then the expected hitting time E[τ] satisfies E[τ] ≤ (1 + ln(X_0 / s_min)) / δ.

  Approach 1 Architecture: Native `condexp` representation, integrability checks included.
-/
theorem multiplicative_drift_theorem 
    [IsProbabilityMeasure (m0.volume : Measure Ω)]
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (h_adapted : Adapted F X)
    (h_stop : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n})
    (δ s_min : ℝ) (h_delta : δ > 0) (h_smin : s_min > 0)
    (X0 : ℝ) (hX0 : ∀ ω, X 0 ω = X0)
    (h_positive : ∀ t, ∀ ω, X t ω ≥ s_min)
    (h_integrable_all : ∀ t, Integrable (X t) m0.volume)
    (h_tau_integrable : Integrable (fun ω => (τ ω : ℝ)) m0.volume)
    (h_drift : ∀ t, ∀ᵐ ω ∂m0.volume, τ ω > t → 
      (m0.volume[fun ω' => X t ω' - X (t + 1) ω' | ↑(F t)]) ω ≥ δ * X t ω) :
    ∫ ω, (τ ω : ℝ) ∂m0.volume ≤ (1 + Real.log (X0 / s_min)) / δ := by
  -- Phase 1: Reduction to Additive Drift via Y_t = 1 + ln(X_t / s_min)
  let Y := fun (t : ℕ) (ω : Ω) => 1 + Real.log (X t ω / s_min)
  
  have hXt_pos : ∀ t ω, X t ω > 0 := fun t ω => lt_of_lt_of_le h_smin (h_positive t ω)
  
  have h_positive_Y : ∀ t ω, 0 ≤ Y t ω := by
    intro t ω; dsimp [Y]
    have : 1 ≤ X t ω / s_min := (one_le_div h_smin).mpr (h_positive t ω)
    linarith [Real.log_nonneg this]
    
  have hY0 : ∀ ω, Y 0 ω = 1 + Real.log (X0 / s_min) := by
    intro ω; dsimp [Y]; rw [hX0 ω]

  have h_adapted_Y : Adapted F Y := by
    intro t
    exact Measurable.const_add (Measurable.log (Measurable.div_const (h_adapted t) s_min)) 1
    
  have h_integrable_Y : ∀ t, Integrable (Y t) m0.volume := by
    intro t
    have h_Y_le : ∀ ω, Y t ω ≤ X t ω / s_min := by
      intro ω; dsimp [Y]
      have h_ratio_pos : X t ω / s_min > 0 := div_pos (hXt_pos t ω) h_smin
      linarith [Real.log_le_sub_one_of_pos h_ratio_pos]
    have h_norm : ∀ᵐ ω ∂m0.volume, ‖Y t ω‖ ≤ X t ω / s_min := by
      apply Eventually.of_forall; intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (h_positive_Y t ω)]; exact h_Y_le ω
    have h_meas_m0 : Measurable (Y t) := fun s hs => F.le t _ ((h_adapted_Y t) hs)
    exact Integrable.mono' ((h_integrable_all t).div_const s_min)
      h_meas_m0.aestronglyMeasurable h_norm
    
  -- Core drift transformation via pointwise bound + pull-out.
  -- Pointwise: Y_t - Y_{t+1} = ln(X_t/X_{t+1}) ≥ 1 - X_{t+1}/X_t = (X_t - X_{t+1})/X_t
  -- (by one_sub_inv_le_log_of_pos with x = X_t/X_{t+1})
  -- Then: E[(X_t - X_{t+1})/X_t | F_t] = (1/X_t) · E[X_t - X_{t+1} | F_t] ≥ (1/X_t) · δ·X_t = δ
  have h_drift_Y : ∀ t, ∀ᵐ ω ∂m0.volume, τ ω > t → 
      (m0.volume[fun ω' => Y t ω' - Y (t + 1) ω' | ↑(F t)]) ω ≥ δ := by
    intro t
    -- Step 1: Pointwise bound  Y_t - Y_{t+1} ≥ (X_t - X_{t+1}) * (X_t)⁻¹
    have h_pw : ∀ ω', Y t ω' - Y (t + 1) ω' ≥ (X t ω' - X (t + 1) ω') * (X t ω')⁻¹ := by
      intro ω'
      dsimp [Y]
      have hXt' := hXt_pos t ω'
      have hXt1' := hXt_pos (t + 1) ω'
      have h_simp : (1 + Real.log (X t ω' / s_min)) - (1 + Real.log (X (t + 1) ω' / s_min)) =
          Real.log (X t ω' / s_min) - Real.log (X (t + 1) ω' / s_min) := by ring
      rw [h_simp]
      -- Use log(a/c) - log(b/c) = log(a) - log(b) 
      have h_sub_log : Real.log (X t ω' / s_min) - Real.log (X (t + 1) ω' / s_min) = 
          Real.log (X t ω') - Real.log (X (t + 1) ω') := by
        rw [Real.log_div (ne_of_gt hXt') (ne_of_gt h_smin),
            Real.log_div (ne_of_gt hXt1') (ne_of_gt h_smin)]
        ring
      rw [h_sub_log]
      -- Now: log(X_t) - log(X_{t+1}) ≥ (X_t - X_{t+1}) / X_t
      -- Equivalently: log(X_t / X_{t+1}) ≥ 1 - X_{t+1}/X_t
      rw [← Real.log_div (ne_of_gt hXt') (ne_of_gt hXt1')]
      have h_key := Real.one_sub_inv_le_log_of_pos (div_pos hXt' hXt1')
      rw [inv_div] at h_key
      linarith [show (X t ω' - X (t + 1) ω') * (X t ω')⁻¹ = 1 - X (t + 1) ω' / X t ω' by
        field_simp]
    -- Step 2: Pull-out property for (X_t)⁻¹
    have h_int_diff : Integrable (fun ω' => X t ω' - X (t + 1) ω') m0.volume :=
      (h_integrable_all t).sub (h_integrable_all (t + 1))
    have h_sm_inv : StronglyMeasurable[F t] (fun ω' => (X t ω')⁻¹) :=
      stronglyMeasurable_iff_measurable.mpr (Measurable.inv (h_adapted t))
    have h_bound_inv : ∀ᵐ ω ∂m0.volume, ‖(X t ω)⁻¹‖ ≤ s_min⁻¹ := by
      apply Eventually.of_forall; intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hXt_pos t ω)))]
      exact inv_anti₀ h_smin (h_positive t ω)
    have h_pull : m0.volume[fun ω' => (X t ω')⁻¹ * (X t ω' - X (t + 1) ω') | ↑(F t)] =ᵐ[m0.volume]
        fun ω => (X t ω)⁻¹ * (m0.volume[fun ω' => X t ω' - X (t + 1) ω' | ↑(F t)]) ω :=
      condExp_stronglyMeasurable_mul_of_bound (F.le t) h_sm_inv h_int_diff s_min⁻¹ h_bound_inv
    -- Step 3: condExp_mono + pull-out + drift => goal
    have h_int_Y_diff : Integrable (fun ω' => Y t ω' - Y (t + 1) ω') m0.volume :=
      (h_integrable_Y t).sub (h_integrable_Y (t + 1))
    -- Integrability of (X_t - X_{t+1}) * (X_t)⁻¹ via bounded domination
    have h_int_ratio : Integrable (fun ω' => (X t ω' - X (t + 1) ω') * (X t ω')⁻¹) m0.volume := by
      apply Integrable.mono' (h_int_diff.norm.mul_const s_min⁻¹)
      · have h_m_Xt : Measurable (X t) := fun s hs => F.le t _ ((h_adapted t) hs)
        have h_m_Xt1 : Measurable (X (t + 1)) := 
          fun s hs => F.le (t + 1) _ ((h_adapted (t + 1)) hs)
        exact (h_m_Xt.sub h_m_Xt1).mul h_m_Xt.inv |>.aestronglyMeasurable
      · apply Eventually.of_forall; intro ω
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (by
          rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hXt_pos t ω)))]
          exact inv_anti₀ h_smin (h_positive t ω)) (norm_nonneg _)
    -- Step 4: Chain the bounds
    have h_mono_ae : ∀ᵐ ω ∂m0.volume,
        (m0.volume[fun ω' => (X t ω' - X (t + 1) ω') * (X t ω')⁻¹ | ↑(F t)]) ω ≤
        (m0.volume[fun ω' => Y t ω' - Y (t + 1) ω' | ↑(F t)]) ω :=
      condExp_mono h_int_ratio h_int_Y_diff (Eventually.of_forall (fun ω' => h_pw ω'))
    filter_upwards [h_mono_ae, h_pull, h_drift t] with ω h_le h_eq h_dr h_tau
    have h5 := h_dr h_tau
    have hXt_ne : X t ω ≠ 0 := ne_of_gt (hXt_pos t ω)
    calc (m0.volume[fun ω' => Y t ω' - Y (t + 1) ω' | ↑(F t)]) ω
        ≥ (m0.volume[fun ω' => (X t ω' - X (t + 1) ω') * (X t ω')⁻¹ | ↑(F t)]) ω := h_le
      _ = (m0.volume[fun ω' => (X t ω')⁻¹ * (X t ω' - X (t + 1) ω') | ↑(F t)]) ω := by
          congr 2; ext ω'; ring
      _ = (X t ω)⁻¹ * (m0.volume[fun ω' => X t ω' - X (t + 1) ω' | ↑(F t)]) ω := h_eq
      _ ≥ (X t ω)⁻¹ * (δ * X t ω) := by
          apply mul_le_mul_of_nonneg_left h5
          exact inv_nonneg.mpr (le_of_lt (hXt_pos t ω))
      _ = δ := by rw [mul_comm δ (X t ω), ← mul_assoc, inv_mul_cancel₀ hXt_ne, one_mul]

  exact additive_drift_theorem Y τ h_adapted_Y h_stop δ h_delta
    (1 + Real.log (X0 / s_min)) hY0 h_positive_Y
    h_integrable_Y h_tau_integrable h_drift_Y

end DriftTheorems
