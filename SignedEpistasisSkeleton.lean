import LintOptions
import Init.Prelude

/-!
# Placeholder for Signed Epistasis Formalization

This file exists to satisfy the package manifest `lakefile.lean` which expects
a module named `SignedEpistasisSkeleton`.

The underlying combinatorial transition properties of Standard Bit Mutation
have already been proven globally in `CoevolutionDeepBounds.lean`.

NOTE: `EpistasisModel` is currently defined as a bare `Nat` placeholder.
This does NOT capture epistatic structure (interaction loci, sign, magnitude).
A proper formalization would define EpistasisModel as a record containing the
interaction graph, signed coefficients, and the bounded-degree constraint.
This placeholder will be replaced when the non-separable proofs are formalized.
-/

namespace SignedEpistasisSkeleton

/-- Placeholder type for the epistasis model. See NOTE above. -/
def EpistasisModel := Nat

end SignedEpistasisSkeleton
