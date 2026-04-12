import CoEALevelBased
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace NonseparablePairSkeleton

open CoEALevelBased

abbrev Prob := ℝ

/-!
# Non-Separable Simultaneous-Pair Skeleton

This file maps the probability domains into `ℝ` aligning with the global
formalization topology. It retains its identity as a structure contract proxy
for the eventual non-separable stochastic processes, while being perfectly typed
for mathlib native real analysis.
-/

structure EpochGeometry where
  xWindow : Nat
  yWindow : Nat
  h_xWindow_pos : xWindow > 0
  h_yWindow_pos : yWindow > 0

noncomputable def epochLength (G : EpochGeometry) : ℝ :=
  (G.xWindow : ℝ) + (G.yWindow : ℝ)

structure FrozenCouplingContracts where
  q_frozen_x_hit : Prob
  q_actual_tracks_frozen : Prob
  h_frozen_x_hit : q_frozen_x_hit > 0
  h_actual_tracks_frozen : q_actual_tracks_frozen > 0

noncomputable def xWindowSuccess (C : FrozenCouplingContracts) : Prob :=
  C.q_frozen_x_hit * C.q_actual_tracks_frozen

structure TargetWindowContracts where
  q_reservoir_form : Prob
  q_reservoir_persist : Prob
  q_target_sample_window : Prob
  h_reservoir_form : q_reservoir_form > 0
  h_reservoir_persist : q_reservoir_persist > 0
  h_target_sample_window : q_target_sample_window > 0

noncomputable def targetWindowSuccess (C : TargetWindowContracts) : Prob :=
  C.q_reservoir_form * C.q_reservoir_persist * C.q_target_sample_window

structure NonsepPairContracts where
  geometry : EpochGeometry
  xPhase : FrozenCouplingContracts
  targetWindow : TargetWindowContracts
  q_y_hit_on_target_window : Prob
  h_y_hit_on_target_window : q_y_hit_on_target_window > 0

noncomputable def epochSuccess (C : NonsepPairContracts) : Prob :=
  xWindowSuccess C.xPhase * targetWindowSuccess C.targetWindow * C.q_y_hit_on_target_window

theorem x_window_success_positive
    (C : FrozenCouplingContracts) :
    xWindowSuccess C > 0 := by
  unfold xWindowSuccess
  have h1 := C.h_frozen_x_hit
  have h2 := C.h_actual_tracks_frozen
  positivity

theorem target_window_success_positive
    (C : TargetWindowContracts) :
    targetWindowSuccess C > 0 := by
  unfold targetWindowSuccess
  have h1 := C.h_reservoir_form
  have h2 := C.h_reservoir_persist
  have h3 := C.h_target_sample_window
  positivity

theorem epoch_length_positive
    (G : EpochGeometry) :
    epochLength G > 0 := by
  unfold epochLength
  have ha : (G.xWindow : ℝ) > 0 := by exact_mod_cast G.h_xWindow_pos
  have hb : (G.yWindow : ℝ) > 0 := by exact_mod_cast G.h_yWindow_pos
  positivity

theorem nonsep_pair_epoch_success_positive
    (C : NonsepPairContracts) :
    epochSuccess C > 0 := by
  unfold epochSuccess
  have h1 := x_window_success_positive C.xPhase
  have h2 := target_window_success_positive C.targetWindow
  have h3 := C.h_y_hit_on_target_window
  positivity

theorem nonsep_pair_runtime_surrogate
    (C : NonsepPairContracts) :
    ∃ bound : ℝ, bound > 0 ∧ bound = epochLength C.geometry / epochSuccess C := by
  let bound := epochLength C.geometry / epochSuccess C
  have h1 := epoch_length_positive C.geometry
  have h2 := nonsep_pair_epoch_success_positive C
  have h_pos : bound > 0 := by positivity
  exact ⟨bound, h_pos, rfl⟩

end NonseparablePairSkeleton
