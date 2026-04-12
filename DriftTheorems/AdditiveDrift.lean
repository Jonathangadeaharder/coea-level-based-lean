import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace DriftTheorems

variable {Ω : Type*} [m0 : MeasureSpace Ω]
variable {F : Filtration ℕ m0.toMeasurableSpace}

/-! ## Helper Lemmas for the Additive Drift Theorem -/

set_option linter.unusedSectionVars false in
/-- Telescoping: summing indicator-weighted one-step decreases gives the total decrease. -/
lemma telescoping_sum (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ)
    (ω : Ω) :
    ∑ t ∈ Finset.range N,
      Set.indicator {ω' | t < τ ω'} (fun ω' => X t ω' - X (t + 1) ω') ω =
      X 0 ω - X (min N (τ ω)) ω := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · have hmin1 : min (n + 1) (τ ω) = n + 1 := by omega
      have hmin2 : min n (τ ω) = n := by omega
      rw [hmin1, hmin2]; ring
    · push Not at h
      have h1 : min (n + 1) (τ ω) = τ ω := by omega
      have h2 : min n (τ ω) = τ ω := by omega
      simp [h1, h2]

/-- `min N τ` is the sum of indicators `1_{t < τ}` for `t < N`. -/
lemma min_eq_sum_indicator (τ : Ω → ℕ) (N : ℕ) (ω : Ω) :
    (↑(min N (τ ω)) : ℝ) = ∑ t ∈ Finset.range N,
      Set.indicator {ω' | t < τ ω'} (fun _ => (1 : ℝ)) ω := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · have hmin1 : min (n + 1) (τ ω) = n + 1 := by omega
      have hmin2 : min n (τ ω) = n := by omega
      rw [hmin1, hmin2]
      push_cast; ring
    · push Not at h
      have h1 : min (n + 1) (τ ω) = τ ω := by omega
      have h2 : min n (τ ω) = τ ω := by omega
      rw [h1, h2]
      ring

/-- Measurability helper: {ω | t < τ ω} is measurable with respect to F t -/
lemma measurableSet_F_tau_gt (τ : Ω → ℕ) (t : ℕ)
    (h_stop : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n}) :
    MeasurableSet[F t] {ω : Ω | t < τ ω} := by
  have : {ω : Ω | t < τ ω} = {ω | τ ω ≤ t}ᶜ := by ext ω; simp [not_le]
  rw [this]; exact (h_stop t).compl

/-- Integrability of the stopped process difference via telescoping. -/
lemma integrable_stopped_diff (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ)
    (h_stop : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n})
    (h_integrable : ∀ t, Integrable (X t) ℙ) :
    Integrable (fun ω => X 0 ω - X (min N (τ ω)) ω) ℙ := by
  have heq : (fun ω => X 0 ω - X (min N (τ ω)) ω) =
      fun ω => ∑ t ∈ Finset.range N,
        Set.indicator {ω' | t < τ ω'} (fun ω' => X t ω' - X (t + 1) ω') ω := by
    ext ω; exact (telescoping_sum X τ N ω).symm
  rw [heq]
  apply integrable_finset_sum
  intro t _
  have h_meas_s := F.le t _ (measurableSet_F_tau_gt τ t h_stop)
  exact Integrable.indicator
    ((h_integrable t).sub (h_integrable (t + 1))) h_meas_s

/-- The main theorem: E[τ] ≤ X₀ / δ. -/
theorem additive_drift_theorem
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (_h_adapted : Adapted F X)
    (h_stop : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n})
    (δ : ℝ) (h_delta : δ > 0)
    (X0 : ℝ) (hX0 : ∀ ω, X 0 ω = X0)
    (h_positive : ∀ t ω, 0 ≤ X t ω)
    (h_integrable_all : ∀ t, Integrable (X t) ℙ)
    (h_tau_integrable : Integrable (fun ω => (τ ω : ℝ)) ℙ)
    (h_drift : ∀ t, ∀ᵐ ω ∂(ℙ : Measure Ω), τ ω > t →
      (ℙ[fun ω' => X t ω' - X (t + 1) ω' | ↑(F t)]) ω ≥ δ) :
    ∫ ω, (τ ω : ℝ) ∂(ℙ : Measure Ω) ≤ X0 / δ := by
  -- Strategy: Show ∀ N, E[τ∧N] * δ ≤ X0, then take N → ∞.
  
  -- Helper: cast compatibility
  have hcast : ∀ N : ℕ, ∀ ω : Ω, (↑(min N (τ ω)) : ℝ) = min (↑N : ℝ) (↑(τ ω) : ℝ) := by
    intro N ω; push_cast; rfl

  -- Step 1: The bounded version
  have h_bounded : ∀ N : ℕ, (∫ ω, (↑(min N (τ ω)) : ℝ) ∂(ℙ : Measure Ω)) * δ ≤ X0 := by
    intro N
    -- Step 1a: E[X0 - X_{τ∧N}] ≤ X0
    have hB : ∫ ω, (X 0 ω - X (min N (τ ω)) ω) ∂(ℙ : Measure Ω) ≤ X0 := by
      calc ∫ ω, (X 0 ω - X (min N (τ ω)) ω) ∂(ℙ : Measure Ω)
          ≤ ∫ ω, X 0 ω ∂(ℙ : Measure Ω) := by
            apply integral_mono (integrable_stopped_diff X τ N h_stop h_integrable_all)
              (h_integrable_all 0)
            intro ω; linarith [h_positive (min N (τ ω)) ω]
        _ = ∫ _, X0 ∂(ℙ : Measure Ω) := by congr 1; ext ω; exact hX0 ω
        _ = X0 := by simp [integral_const]
    -- Step 1b: E[τ∧N] * δ ≤ E[X0 - X_{τ∧N}]
    have hA : (∫ ω, (↑(min N (τ ω)) : ℝ) ∂(ℙ : Measure Ω)) * δ ≤
        ∫ ω, (X 0 ω - X (min N (τ ω)) ω) ∂(ℙ : Measure Ω) := by
      have h_meas_s_F := fun t => measurableSet_F_tau_gt τ t h_stop
      have h_meas_s := fun t => F.le t _ (h_meas_s_F t)
      
      have hLHS : (∫ ω, (↑(min N (τ ω)) : ℝ) ∂ℙ) * δ =
          ∑ t ∈ Finset.range N, ∫ ω in {ω' | t < τ ω'}, δ ∂ℙ := by
        have h1 : (fun ω => (↑(min N (τ ω)) : ℝ)) = fun ω => ∑ t ∈ Finset.range N,
            Set.indicator {ω' | t < τ ω'} (fun _ => (1:ℝ)) ω := funext (min_eq_sum_indicator τ N)
        rw [h1, integral_finset_sum]
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          have h_ind : (fun ω => Set.indicator {ω' | t < τ ω'} (fun _ => (1:ℝ)) ω * δ) = Set.indicator {ω' | t < τ ω'} (fun _ => δ) := by
            ext ω; simp only [Set.indicator_apply]; split_ifs <;> simp
          rw [← integral_mul_const δ, h_ind, integral_indicator (h_meas_s t)]
        · intro t _
          exact (integrable_const 1).indicator (h_meas_s t)
      
      have hRHS : ∫ ω, (X 0 ω - X (min N (τ ω)) ω) ∂ℙ =
          ∑ t ∈ Finset.range N, ∫ ω in {ω' | t < τ ω'}, (X t - X (t + 1)) ω ∂ℙ := by
        have heq : (fun ω => X 0 ω - X (min N (τ ω)) ω) = fun ω => ∑ t ∈ Finset.range N,
            Set.indicator {ω' | t < τ ω'} (fun ω' => (X t - X (t + 1)) ω') ω := funext (fun ω => (telescoping_sum X τ N ω).symm)
        rw [heq, integral_finset_sum]
        · congr 1
          ext t
          exact integral_indicator (h_meas_s t)
        · intro t _
          exact Integrable.indicator ((h_integrable_all t).sub (h_integrable_all (t+1))) (h_meas_s t)
      
      rw [hLHS, hRHS]
      apply Finset.sum_le_sum
      intro t _
      have h_cond := setIntegral_condExp (F.le t)
        ((h_integrable_all t).sub (h_integrable_all (t+1))) (h_meas_s_F t)
      -- h_cond: ∫ in {ω | t < τ ω}, ℙ[X t - X (t+1) | F t] = ∫ in {ω | t < τ ω}, X t - X (t+1)
      rw [← h_cond]
      apply setIntegral_mono_on_ae
      · exact (integrable_const δ).integrableOn
      · exact integrable_condExp.integrableOn
      · exact h_meas_s t
      · exact h_drift t
    linarith

  -- Step 2: Pass to the limit
  -- We need: ∫ τ ≤ X0 / δ, given ∀ N, (∫ min(N,τ)) * δ ≤ X0
  have h_bdd2 : ∀ N : ℕ, ∫ ω, (↑(min N (τ ω)) : ℝ) ∂(ℙ : Measure Ω) ≤ X0 / δ := by
    intro N
    exact (le_div_iff₀ h_delta).mpr (h_bounded N)

  have h_tendsto : Filter.Tendsto
      (fun N : ℕ => ∫ ω, (↑(min N (τ ω)) : ℝ) ∂(ℙ : Measure Ω))
      Filter.atTop (nhds (∫ ω, (τ ω : ℝ) ∂(ℙ : Measure Ω))) := by
    apply integral_tendsto_of_tendsto_of_monotone
    · -- Integrability of each f_n = min(n, τ)
      intro n
      have h_cont : Continuous (fun x : ℝ => min (n:ℝ) x) := continuous_const.min continuous_id
      have h_meas : AEStronglyMeasurable (fun ω => min (n:ℝ) (τ ω : ℝ)) ℙ :=
        h_cont.comp_aestronglyMeasurable h_tau_integrable.aestronglyMeasurable
      have heq : (fun ω => (↑(min n (τ ω)) : ℝ)) = fun ω => min (n:ℝ) (τ ω : ℝ) := by
        ext ω; exact hcast n ω
      rw [heq]
      apply Integrable.mono h_tau_integrable h_meas
      filter_upwards with ω
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ min (n:ℝ) (τ ω : ℝ) := by positivity
      have h2 : 0 ≤ (τ ω : ℝ) := by positivity
      rw [abs_of_nonneg h1, abs_of_nonneg h2]
      exact min_le_right _ _
    · exact h_tau_integrable
    · -- Monotonicity
      filter_upwards with ω a b hab
      exact Nat.cast_le.mpr (by omega)
    · -- Pointwise convergence
      filter_upwards with ω
      have heq : (fun N:ℕ => (↑(min N (τ ω)) : ℝ)) =ᶠ[Filter.atTop] (fun N:ℕ => (τ ω : ℝ)) := by
        apply Filter.eventually_atTop.mpr
        use τ ω
        intro n hn
        simp only [Nat.min_eq_right hn]
      exact tendsto_const_nhds.congr' heq.symm
      
  -- Conclude: limit of bounded sequence is bounded
  exact le_of_tendsto h_tendsto (Eventually.of_forall h_bdd2)

end DriftTheorems
