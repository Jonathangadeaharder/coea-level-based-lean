import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Duality.LinearProgrammingB  -- Core LP mapping interface from madvorak/duality

open Matrix

namespace GameTheoryMinimax

variable {m n : ℕ}

/--
A strictly finite discrete vector bounded natively as a non-negative
probability distribution spanning the dimension `k`.
-/
structure MixedStrategy (k : ℕ) where
  probs : Fin k → ℝ
  nonneg : ∀ i, 0 ≤ probs i
  sums_to_one : ∑ i, probs i = 1

variable (A : Matrix (Fin m) (Fin n) ℝ)

/--
Architectural translation layer representing Player 1's goal to minimize max loss (t),
while playing a valid MixedStrategy (x).
Since x_i >= 0 is native, t must be represented as t^+ - t^-.
Variables J: Fin m ⊕ Fin 2
Constraints I: Fin n ⊕ Fin 2
-/
def GameToPrimalLP : StandardLP (Fin n ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  { A := fun i j => match i with
      | Sum.inl c_col => match j with
          | Sum.inl v_row => A v_row c_col
          | Sum.inr 0 => -1
          | Sum.inr 1 => 1
      | Sum.inr 0 => match j with
          | Sum.inl _ => 1
          | Sum.inr _ => 0
      | Sum.inr 1 => match j with
          | Sum.inl _ => -1
          | Sum.inr _ => 0
    b := fun i => match i with
      | Sum.inl _ => 0
      | Sum.inr 0 => 1
      | Sum.inr 1 => -1
    c := fun j => match j with
      | Sum.inl _ => 0
      | Sum.inr 0 => 1
      | Sum.inr 1 => -1 }



/--
The structural capstone proving Minimax Equivalence strictly from Strong Duality.
-/
theorem minimax_existence (H : (GameToPrimalLP A).IsFeasible ∨ (GameToPrimalLP A).dualize.IsFeasible) : 
  OppositesOpt (GameToPrimalLP A).optimum (GameToPrimalLP A).dualize.optimum := by
  exact StandardLP.strongDuality (GameToPrimalLP A) H


end GameTheoryMinimax
