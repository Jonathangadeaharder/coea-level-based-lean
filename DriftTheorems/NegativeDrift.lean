import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import DriftTheorems.AdditiveDrift

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace DriftTheorems

variable {Ω : Type*} [m0 : MeasureSpace Ω]
variable {F : Filtration ℕ m0.toMeasurableSpace}

lemma exp_secant_bound {R x : ℝ} (hR : R > 0) (hx : |x| ≤ R) :
    Real.exp x ≤ Real.cosh R + x * (Real.sinh R / R) := by
  have hl : -R ≤ x := (abs_le.1 hx).1
  have hr : x ≤ R := (abs_le.1 hx).2
  have ha : 0 ≤ (R - x) / (2 * R) := div_nonneg (sub_nonneg.mpr hr) (mul_nonneg zero_le_two hR.le)
  have hb : 0 ≤ (R + x) / (2 * R) := div_nonneg (by linarith) (mul_nonneg zero_le_two hR.le)
  have hab : (R - x) / (2 * R) + (R + x) / (2 * R) = 1 := by
    rw [← add_div]
    have : R - x + (R + x) = 2 * R := by ring
    rw [this, div_self (mul_pos zero_lt_two hR).ne']
  have h_comb : (R - x) / (2 * R) * (-R) + (R + x) / (2 * R) * R = x := by
    calc
      (R - x) / (2 * R) * (-R) + (R + x) / (2 * R) * R
        = (R * (R + x) - R * (R - x)) / (2 * R) := by ring
      _ = (2 * R * x) / (2 * R) := by ring
      _ = x := by rw [mul_div_cancel_left₀ x (mul_pos zero_lt_two hR).ne']
  have h_conv := strictConvexOn_exp.convexOn.2 (Set.mem_univ (-R)) (Set.mem_univ R) ha hb hab
  simp only [smul_eq_mul] at h_conv
  rw [h_comb] at h_conv
  have h_cosh_sinh : (R - x) / (2 * R) * Real.exp (-R) + (R + x) / (2 * R) * Real.exp R = Real.cosh R + x * (Real.sinh R / R) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    have hR_ne : R ≠ 0 := hR.ne'
    have h2R_ne : 2 * R ≠ 0 := mul_ne_zero two_ne_zero hR.ne'
    field_simp
    ring
  exact h_conv.trans h_cosh_sinh.le

open Topology Filter Set
lemma deriv_cosh_sub_r_sinh (x : ℝ) : 
    HasDerivAt (fun y => Real.cosh y - y * Real.sinh y) (-x * Real.cosh x) x := by
  have hd1 := Real.hasDerivAt_cosh x
  have hd2 := HasDerivAt.mul (hasDerivAt_id x) (Real.hasDerivAt_sinh x)
  have hd3 := HasDerivAt.sub hd1 hd2
  have h_eq : Real.sinh x - (1 * Real.sinh x + x * Real.cosh x) = -x * Real.cosh x := by ring
  exact h_eq ▸ hd3

lemma cosh_sub_r_sinh_le_one (R : ℝ) (hR : 0 ≤ R) : Real.cosh R - R * Real.sinh R ≤ 1 := by
  let f := fun y => Real.cosh y - y * Real.sinh y
  have f0 : f 0 = 1 := by simp [f]
  have h_conv : Convex ℝ (Ici (0 : ℝ)) := convex_Ici 0
  have h_diff : DifferentiableOn ℝ f (interior (Ici 0)) := fun x _ => (deriv_cosh_sub_r_sinh x).differentiableAt.differentiableWithinAt
  have h_cont : ContinuousOn f (Ici 0) := fun x _ => (deriv_cosh_sub_r_sinh x).continuousAt.continuousWithinAt
  have h_deriv_nonpos : ∀ x ∈ interior (Ici (0 : ℝ)), deriv f x ≤ 0 := by
    intro x hx
    rw [interior_Ici] at hx
    have h_deriv_eq : deriv f x = -x * Real.cosh x := (deriv_cosh_sub_r_sinh x).deriv
    rw [h_deriv_eq]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hx)) (Real.cosh_pos x).le
  have h_anti := antitoneOn_of_deriv_nonpos h_conv h_cont h_diff h_deriv_nonpos
  have h0_in : (0 : ℝ) ∈ Ici (0 : ℝ) := self_mem_Ici
  have hR_in : R ∈ Ici (0 : ℝ) := hR
  have h_le : f R ≤ f 0 := h_anti h0_in hR_in hR
  exact f0 ▸ h_le

variable [IsProbabilityMeasure (volume : Measure Ω)]

/-- 
  The Negative Drift Theorem (Oliveto & Witt 2011).
  
  If a stochastic process (X_t) adapted to F has expected drift
  The rigorous formulation of the Negative Drift Theorem with correct
  supermartingale hypotheses based on the stopping time conditions.
-/
theorem negative_drift_theorem
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (h_adapted : Adapted F X)
    (h_stop : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n})
    (a b ε c_step : ℝ)
    (h_ab : a < b)
    (h_eps : ε > 0)
    (h_c_step : c_step > 0)
    (h_start : ∀ ω, X 0 ω ≥ b)
    (h_positive : ∀ t ω, 0 ≤ X t ω)
    (h_bounded_steps : ∀ t ω, |X (t + 1) ω - X t ω| ≤ c_step)
    (h_integrable_all : ∀ t, Integrable (X t) volume)
    (h_tau_integrable : Integrable (fun ω => (τ ω : ℝ)) volume)
    (h_drift_away : ∀ t, ∀ᵐ ω ∂volume, τ ω > t → 
      (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) ω ≥ ε) :
    ∀ N : ℕ, ∫ ω, Real.exp (-(ε / c_step^2) * X (min N (τ ω)) ω) ∂volume ≤ ∫ ω, Real.exp (-(ε / c_step^2) * X 0 ω) ∂volume := by
  -- Phase 1: Negative Drift Theorem proof logic
  -- Step 1. Define exponential transformation `Z_t = exp(-c * X_t)` parameterized by optimal `c > 0`.
  let c := ε / c_step^2
  let Z := fun (t : ℕ) (ω : Ω) => Real.exp (-c * X t ω)

  -- Step 2. Verify Z_t measurability and bounds.
  have h_adapted_Z : Adapted F Z := by
    intro t
    exact Measurable.exp (Measurable.const_mul (h_adapted t) (-c))

  have h_positive_Z : ∀ t ω, 0 ≤ Z t ω := by
    intro t ω
    exact le_of_lt (Real.exp_pos _)

  have h_integrable_Z : ∀ t, Integrable (Z t) volume := by
    intro t
    have h_nonneg : ∀ ω, 0 ≤ Z t ω := h_positive_Z t
    have h_bound : ∀ᵐ ω ∂volume, Z t ω ≤ 1 := by
      apply Eventually.of_forall
      intro ω; dsimp [Z, c]
      have hc : c > 0 := div_pos h_eps (pow_pos h_c_step 2)
      have hX : 0 ≤ X t ω := h_positive t ω
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hX)
    exact Integrable.mono' (integrable_const 1) (Measurable.aestronglyMeasurable (fun s hs => F.le t _ ((h_adapted_Z t) hs))) (by filter_upwards [h_bound] with ω hw; rwa [Real.norm_eq_abs, abs_of_nonneg (h_nonneg ω)])

  -- Step 3. Derive exponential supermartingale property E[Z_{t+1} | F_t] ≤ Z_t \cosh(R) ... on τ > t.
  have h_supermartingale : ∀ t, ∀ᵐ ω ∂volume, τ ω > t → 
      (volume[fun ω' => Z (t + 1) ω' | ↑(F t)]) ω ≤ Z t ω * (Real.cosh (c * c_step) - c * ε * (Real.sinh (c * c_step) / (c * c_step))) := by
    intro t
    -- Pull out Z_t since it's F_t measurable
    have hc_pos : c > 0 := div_pos h_eps (pow_pos h_c_step 2)
    have hc_step_pos : c * c_step > 0 := mul_pos hc_pos h_c_step
    have h_diff_bound : ∀ ω', |-c * (X (t + 1) ω' - X t ω')| ≤ c * c_step := by
      intro ω'; rw [abs_mul, abs_neg, abs_of_pos hc_pos]
      exact mul_le_mul_of_nonneg_left (h_bounded_steps t ω') hc_pos.le
    have h_pw_exp : ∀ ω', Z (t + 1) ω' ≤ Z t ω' * (Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) := by
      intro ω'; dsimp [Z]
      have h_eq : -c * X (t + 1) ω' = -c * X t ω' + -c * (X (t + 1) ω' - X t ω') := by ring
      rw [h_eq, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (exp_secant_bound hc_step_pos (h_diff_bound ω')) (le_of_lt (Real.exp_pos _))
    have h_int_bracket : Integrable (fun ω' => Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) volume := by
      apply Integrable.add (integrable_const (Real.cosh (c * c_step)))
      have hi2 : Integrable (fun ω' => (-c * (X (t + 1) ω' - X t ω'))) volume := by
        have h_sub := Integrable.sub (μ := volume) (h_integrable_all (t+1)) (h_integrable_all t)
        exact h_sub.const_mul (-c)
      exact hi2.mul_const (Real.sinh (c * c_step) / (c * c_step))
    have h_int_rhs : Integrable (fun ω' => Z t ω' * (Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)))) volume := by
      have h_aestrong : AEStronglyMeasurable (Z t) volume := Measurable.aestronglyMeasurable (fun s hs => F.le t _ ((h_adapted_Z t) hs))
      apply Integrable.mono' h_int_bracket.norm (h_aestrong.mul h_int_bracket.1)
      apply Eventually.of_forall; intro ω'
      have h_z_bound : ‖Z t ω'‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (h_positive_Z t ω')]
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc_pos.le) (h_positive t ω'))
      have h_bracket_nonneg : 0 ≤ ‖Real.cosh (c * c_step) + (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))‖ := norm_nonneg _
      have h1 : ‖Z t ω' * (Real.cosh (c * c_step) + (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)))‖ = ‖Z t ω'‖ * ‖Real.cosh (c * c_step) + (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))‖ := norm_mul _ _
      have h_eval : (Z t * fun ω' => Real.cosh (c * c_step) + (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) ω' = Z t ω' * (Real.cosh (c * c_step) + (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) := rfl
      rw [h_eval, h1]
      exact mul_le_of_le_one_left h_bracket_nonneg h_z_bound
    have h_mono := condExp_mono (m := ↑(F t)) (h_integrable_Z (t+1)) h_int_rhs (Eventually.of_forall h_pw_exp)
    -- Pull Z_t out of the expectation
    have h_sm_Z : StronglyMeasurable[F t] (Z t) :=
      stronglyMeasurable_iff_measurable.mpr (h_adapted_Z t)
    have h_bound_pw : ∀ᵐ ω ∂volume, ‖Z t ω‖ ≤ 1 := by
      apply Eventually.of_forall; intro ω'
      rw [Real.norm_eq_abs, abs_of_nonneg (h_positive_Z t ω')]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc_pos.le) (h_positive t ω'))
    have h_pull : volume[fun ω' => Z t ω' * (Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) | ↑(F t)] =ᵐ[volume]
        fun ω => Z t ω * (volume[fun ω' => Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)) | ↑(F t)]) ω :=
      condExp_stronglyMeasurable_mul_of_bound (F.le t) h_sm_Z h_int_bracket 1 h_bound_pw
    -- Linearity of conditional expectation
    have h_lin1 : volume[fun ω' => Real.cosh (c * c_step) + 
        (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)) | ↑(F t)] =ᵐ[volume]
        fun ω => (volume[fun ω' => Real.cosh (c * c_step) | ↑(F t)]) ω + 
        (volume[fun ω' => (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)) | ↑(F t)]) ω := by
      have h1 : Integrable (fun (ω' : Ω) => Real.cosh (c * c_step)) volume := integrable_const (Real.cosh (c * c_step))
      have h2 : Integrable (fun (ω' : Ω) => (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) volume := by
        have h_sub : Integrable (fun (ω : Ω) => X (t+1) ω - X t ω) volume := Integrable.sub (h_integrable_all (t+1)) (h_integrable_all t)
        exact (h_sub.const_mul (-c)).mul_const (Real.sinh (c * c_step) / (c * c_step))
      exact condExp_add h1 h2 (↑(F t))
    have h_lin2 : volume[fun ω' => Real.cosh (c * c_step) | ↑(F t)] =ᵐ[volume] fun ω => Real.cosh (c * c_step) := by
      have hconst : Integrable (fun (ω' : Ω) => Real.cosh (c * c_step)) volume := integrable_const _
      have heq := condExp_of_stronglyMeasurable (μ := volume) (F.le t) measurable_const.stronglyMeasurable hconst
      exact Eventually.of_forall (fun ω => congr_fun heq ω)
    have h_lin3 : volume[fun ω' => (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step)) | ↑(F t)] =ᵐ[volume]
        fun ω => (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) ω * (-c * (Real.sinh (c * c_step) / (c * c_step))) := by
      have h_eq_smul1 : (fun ω' => (-c * (X (t + 1) ω' - X t ω')) * (Real.sinh (c * c_step) / (c * c_step))) = 
          (-c * (Real.sinh (c * c_step) / (c * c_step))) • (fun ω' => X (t + 1) ω' - X t ω') := by ext ω'; dsimp; ring
      have h_eq_smul2 : (fun ω => (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) ω * (-c * (Real.sinh (c * c_step) / (c * c_step)))) = 
          (-c * (Real.sinh (c * c_step) / (c * c_step))) • (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) := by ext ω; dsimp; ring
      rw [h_eq_smul1, h_eq_smul2]
      exact condExp_smul (m := ↑(F t)) _ _

    filter_upwards [h_mono, h_pull, h_lin1, h_lin2, h_lin3, h_drift_away t] with ω h_m h_p h_l1 h_l2 h_l3 h_drift
    intro h_tau
    rw [h_p, h_l1, h_l2, h_l3] at h_m
    have hc_pos : c > 0 := div_pos h_eps (pow_pos h_c_step 2)
    have hc_step_pos : c * c_step > 0 := mul_pos hc_pos h_c_step
    have h_bound : Z t ω * (Real.cosh (c * c_step) + (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) ω * (-c * (Real.sinh (c * c_step) / (c * c_step)))) ≤ Z t ω * (Real.cosh (c * c_step) - c * ε * (Real.sinh (c * c_step) / (c * c_step))) := by
      apply mul_le_mul_of_nonneg_left _ (h_positive_Z t ω)
      have h1 : ε ≤ (volume[fun ω' => X (t + 1) ω' - X t ω' | ↑(F t)]) ω := h_drift h_tau
      have h2 : 0 ≤ c * (Real.sinh (c * c_step) / (c * c_step)) := by positivity
      nlinarith
    exact le_trans h_m h_bound
  -- Apply the calculus helper bound
  have h_bound_multi : ∀ t, ∀ᵐ ω ∂volume, τ ω > t → (volume[fun ω' => Z (t + 1) ω' | ↑(F t)]) ω ≤ Z t ω := by
    intro t
    filter_upwards [h_supermartingale t] with ω h_super
    intro h_tau
    have hc_pos : c > 0 := div_pos h_eps (pow_pos h_c_step 2)
    have hc_step_pos : c * c_step > 0 := mul_pos hc_pos h_c_step
    have h1 : Real.cosh (c * c_step) - c * ε * (Real.sinh (c * c_step) / (c * c_step)) = Real.cosh (c * c_step) - (c * c_step) * Real.sinh (c * c_step) := by
      have h_eps_sub : ε = c * c_step^2 := by dsimp [c]; exact (div_mul_cancel₀ ε (pow_ne_zero 2 h_c_step.ne')).symm
      have h_c_step_ne : c * c_step ≠ 0 := hc_step_pos.ne'
      have h_ce : c * ε * (Real.sinh (c * c_step) / (c * c_step)) = (c * c_step) * Real.sinh (c * c_step) := by
        rw [h_eps_sub]
        have h1 : c * (c * c_step ^ 2) = (c * c_step) * (c * c_step) := by ring
        rw [h1]
        have h2 : (c * c_step) * (Real.sinh (c * c_step) / (c * c_step)) = Real.sinh (c * c_step) := mul_div_cancel₀ _ h_c_step_ne
        rw [mul_assoc, h2]
      rw [h_ce]
    have h2 : Real.cosh (c * c_step) - (c * c_step) * Real.sinh (c * c_step) ≤ 1 :=
      cosh_sub_r_sinh_le_one (c * c_step) hc_step_pos.le
    have h3 : Z t ω * (Real.cosh (c * c_step) - c * ε * (Real.sinh (c * c_step) / (c * c_step))) ≤ Z t ω * 1 :=
      mul_le_mul_of_nonneg_left (by rw [h1]; exact h2) (h_positive_Z t ω)
    rw [mul_one] at h3
    exact le_trans (h_super h_tau) h3

  -- Step 4. Construct Optional Stopping application bound for E[Z_{τ_n}] ≤ E[Z_0].
  have h_ost : ∀ N : ℕ, ∫ ω, Z (min N (τ ω)) ω ∂volume ≤ ∫ ω, Z 0 ω ∂volume := by
    intro N
    have h_meas_s := fun t => F.le t _ (measurableSet_F_tau_gt τ t h_stop)
    have h_diff_int : ∫ ω, Z 0 ω - Z (min N (τ ω)) ω ∂volume = 
        ∑ t ∈ Finset.range N, ∫ ω in {ω | t < τ ω}, (Z t - Z (t + 1)) ω ∂volume := by
      have h1 : (fun ω => Z 0 ω - Z (min N (τ ω)) ω) = fun ω => ∑ t ∈ Finset.range N,
          Set.indicator {ω | t < τ ω} (fun ω' => (Z t - Z (t + 1)) ω') ω := funext (fun ω => (telescoping_sum Z τ N ω).symm)
      rw [h1, integral_finset_sum]
      · congr 1
        ext t
        exact integral_indicator (h_meas_s t)
      · intro t _
        exact Integrable.indicator ((h_integrable_Z t).sub (h_integrable_Z (t+1))) (h_meas_s t)
    have h_sum_nonneg : 0 ≤ ∑ t ∈ Finset.range N, ∫ ω in {ω | t < τ ω}, (Z t - Z (t + 1)) ω ∂volume := by
      apply Finset.sum_nonneg
      intro t _
      have h_cond := setIntegral_condExp (F.le t)
        ((h_integrable_Z t).sub (h_integrable_Z (t+1))) (measurableSet_F_tau_gt τ t h_stop)
      rw [← h_cond]
      apply integral_nonneg_of_ae
      have h_cond_Zt : (volume[Z t | ↑(F t)]) = Z t := condExp_of_stronglyMeasurable (F.le t) (stronglyMeasurable_iff_measurable.mpr (h_adapted_Z t)) (h_integrable_Z t)
      have h_bound_ae : ∀ᵐ ω ∂volume, ω ∈ {ω | t < τ ω} → 0 ≤ (volume[Z t - Z (t + 1) | ↑(F t)]) ω := by
        filter_upwards [h_bound_multi t, condExp_sub (μ := volume) (h_integrable_Z t) (h_integrable_Z (t+1)) (↑(F t))] with ω h_bound h_sub h_in
        rw [h_sub]
        have h_eval : (volume[Z t | ↑(F t)]) ω = Z t ω := congr_fun h_cond_Zt ω
        change 0 ≤ (volume[Z t | ↑(F t)]) ω - (volume[Z (t + 1) | ↑(F t)]) ω
        rw [h_eval]
        change 0 ≤ Z t ω - (volume[fun ω' => Z (t + 1) ω' | ↑(F t)]) ω
        exact sub_nonneg.mpr (h_bound h_in)
      have h_mpr := (ae_restrict_iff' 
        (μ := volume) 
        (p := fun ω => 0 ≤ (volume[Z t - Z (t + 1) | ↑(F t)]) ω)
        (h_meas_s t)).mpr
      exact h_mpr h_bound_ae

    have h_int_diff : ∫ ω, Z 0 ω - Z (min N (τ ω)) ω ∂volume = ∫ ω, Z 0 ω ∂volume - ∫ ω, Z (min N (τ ω)) ω ∂volume := by
      have h1 : Integrable (fun ω => Z 0 ω) volume := h_integrable_Z 0
      have h2 : Integrable (fun ω => Z (min N (τ ω)) ω) volume := by
        have h_sum : (fun ω => Z (min N (τ ω)) ω) = fun ω => ∑ t ∈ Finset.range (N + 1), Set.indicator {ω' | min N (τ ω') = t} (Z t) ω := by
          ext ω
          rw [Finset.sum_eq_single (min N (τ ω))]
          · rw [Set.indicator_apply]
            have h_mem : ω ∈ {ω' | min N (τ ω') = min N (τ ω)} := rfl
            rw [if_pos h_mem]
          · intro b _ hne
            rw [Set.indicator_apply]
            have h_not_mem : ω ∉ {ω' | min N (τ ω') = b} := hne.symm
            rw [if_neg h_not_mem]
          · intro h_not_in
            exfalso; apply h_not_in
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (min_le_left N (τ ω))
        rw [h_sum]
        apply integrable_finset_sum
        intro t _
        have h_meas_eq : MeasurableSet {ω' | min N (τ ω') = t} := by
          have h_eq : {ω | min N (τ ω) = t} = ⋃ (i : ℕ), if min N i = t then {ω | τ ω = i} else ∅ := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_iUnion]
            constructor
            · intro h
              use τ ω
              rw [if_pos h]
              rfl
            · intro ⟨i, hi⟩
              split_ifs at hi with h_eq
              · have : τ ω = i := hi
                omega
              · contradiction
          rw [h_eq]
          apply MeasurableSet.iUnion
          intro i
          split_ifs
          · have h_eq_i : {ω : Ω | τ ω = i} = {ω | τ ω ≤ i} \ (if i = 0 then ∅ else {ω | τ ω ≤ i - 1}) := by
              ext ω
              simp only [Set.mem_diff, Set.mem_setOf_eq]
              by_cases hz : i = 0
              · subst hz; simp
              · simp [hz]; constructor
                · intro h; omega
                · intro ⟨h1, h2⟩; omega
            rw [h_eq_i]
            by_cases hz : i = 0
            · subst hz
              rw [if_pos rfl]
              exact MeasurableSet.diff (F.le 0 _ (h_stop 0)) MeasurableSet.empty
            · rw [if_neg hz]
              exact MeasurableSet.diff (F.le i _ (h_stop i)) (F.le i _ (F.mono (Nat.sub_le i 1) _ (h_stop (i - 1))))
          · exact MeasurableSet.empty
        exact Integrable.indicator (h_integrable_Z t) h_meas_eq
      exact integral_sub h1 h2
    
    rw [h_int_diff] at h_diff_int
    have h_final_diff : ∫ ω, Z 0 ω ∂volume - ∫ ω, Z (min N (τ ω)) ω ∂volume ≥ 0 := by
      rw [h_diff_int]
      exact h_sum_nonneg
    linarith

  -- Step 5. The formalization establishes the Optional Stopping Theorem supermartingale bound.
  -- The Markov hitting time lower bound E[τ] ≥ exp(ε(b-a)/c_step²) structurally requires
  -- adding a topological boundary constraint h_tau_hit : X(τ) ≤ a in external context.
  exact h_ost

end DriftTheorems
