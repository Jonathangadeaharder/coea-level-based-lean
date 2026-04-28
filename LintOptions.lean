/-!
# Global Lint Options for Formal Verification Hardening

These options enforce strict variable tracking and tactic hygiene across
all modules in the CoEA Level-Based formalization. Every `.lean` file
in the project must `import LintOptions` to inherit these constraints.

## Enforced checks

1. **Unused variables** — any declared variable that does not appear in the
   proof body is flagged by the compiler.
2. **Function argument tracking** — unused function arguments are flagged.
3. **Pattern variable tracking** — unused pattern-match binders are flagged.

## CI enforcement (additional, external)

The `.github/workflows/ci.yml` pipeline enforces:
- `sorry` — forbidden outside `LBTCoupling.lean` (three documented deferred proofs)
- `axiom` declarations — forbidden in all project files
- `admit` — forbidden in all project files
- `native_decide` — forbidden in all project files (bypasses the Lean kernel)

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
-- NOTE: native_decide is banned via CI (see ci.yml).
-- It bypasses the Lean kernel by compiling to native code,
-- so proofs using it are not kernel-checked.
-- Use `decide` (kernel-checked) instead.
-- ============================================================
