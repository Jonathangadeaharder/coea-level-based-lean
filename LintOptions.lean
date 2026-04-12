/-!
# Global Lint Options for Formal Verification Hardening

These options enforce strict variable tracking and tactic hygiene across
all modules in the CoEA Level-Based formalization. Every `.lean` file
in the project must `import LintOptions` to inherit these constraints.

## Paper Reference
Derived from: "Formally Verified Artificial Intelligence: Exhaustive Protocols
for Detecting and Preventing Heuristic Cheating in Lean 4 Proof Generation"
-/

-- ============================================================
-- STRICT VARIABLE TRACKING
-- ============================================================
-- Forces the compiler to flag any declared variable that fails
-- to structurally propagate through the proof body.

set_option linter.unusedVariables true
set_option linter.unusedVariables.funArgs true
set_option linter.unusedVariables.patternVars true

-- ============================================================
-- NOTE: Tactic bloat detection is handled externally by
-- semantic_linter.py (Rule 8) since linter.unusedTactic
-- is not available in this Lean 4 version.
-- ============================================================

