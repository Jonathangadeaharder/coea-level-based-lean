import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.Process.HittingTime

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Classical

/-!
# Level-Based Theorem (LBT) Preconditions
This module formalizes the three generic geometric drift preconditions required by
the Level-Based Theorem (Corus et al. 2018) for population-based search heuristics.
-/

namespace LBT

variable {X : Type} [Fintype X] [Nonempty X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
variable {m : ℕ} (hm : m > 0)
variable (lambda_pop : ℕ) (h_lambda : lambda_pop > 0)

-- We partition the search space X into m distinct levels
variable (A : Fin m → Set X)

-- Upward cumulative sets.
def A_geq (j : Fin m) : Set X :=
  ⋃ (k : Fin m) (_ : k.val ≥ j.val), A k

-- A population is a vector of individuals. By explicitly receiving X, we prevent 
-- metavariable inference failures when constructing kernels.
abbrev Population (X : Type) (lambda_pop : ℕ) := Fin lambda_pop → X

-- Number of individuals in the population belonging to a specific set S.
noncomputable def pop_count (P : Population X lambda_pop) (S : Set X) : ℕ :=
  (Finset.univ.filter (fun i => P i ∈ S)).card

variable (D : Kernel (Population X lambda_pop) X) [IsMarkovKernel D]

/-! ## Precondition G1: Upgrade Probability (Mutation bounds) -/

/--
**Condition G1**: If a minimal fraction `γ₀` of the population resides at or above level `j`,
the probability of sampling an offspring strictly above level `j` is bounded
below by `δ`.
-/
def ConditionG1 (γ₀ δ : ℝ) : Prop :=
  ∀ (j : Fin (m - 1)) (P : Population X lambda_pop),
    (pop_count lambda_pop P (A_geq A ⟨j.val, by omega⟩) : ℝ) ≥ γ₀ * (lambda_pop : ℝ) →
    (D P (A_geq A ⟨j.val + 1, by omega⟩)).toReal ≥ δ

/-! ## Precondition G2: Growth Rate (Selection amplification) -/

/--
**Condition G2**: Selection must amplify the prevalence of level `j` individuals.
The probability of sampling an individual at or above level `j` must exceed
the current population proportion scaled by a growth rate `z j > 1`.
-/
def ConditionG2 (z : Fin m → ℝ) : Prop :=
  ∀ (j : Fin m) (P : Population X lambda_pop),
    (pop_count lambda_pop P (A_geq A j) : ℝ) > 0 →
    (D P (A_geq A j)).toReal ≥ (z j) * (pop_count lambda_pop P (A_geq A j) : ℝ) / (lambda_pop : ℝ)

/-! ## Precondition G3: Selection Concentration (Population size) -/

/--
**Condition G3**: The population size `λ` must be sufficiently large to
guarantee concentration of measure and combat genetic drift.
-/
def ConditionG3 (δ : ℝ) : Prop :=
  ∃ (c_sel : ℝ), c_sel > 0 ∧ (lambda_pop : ℝ) ≥ c_sel * (1 / δ) * (Real.log m)

end LBT
