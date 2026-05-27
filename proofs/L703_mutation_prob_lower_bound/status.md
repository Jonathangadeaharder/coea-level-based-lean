state: done
owner: manual
depends_on: (none — frontier leaf)
estimated_lines: 80–150
estimated_hours: 4–8

# Result

Merged into `LBTCoupling.lean` at `mutation_prob_lower_bound` (L703). Scratchpad
`attempt.lean` compiles and was used as the source for the merge.

# Notes
- Top-level case split on `hw(x) < n` vs `hw(x) = n`.
- ENNReal-to-Real conversion via `ENNReal.toReal_le_toReal`.
- Helper `one_minus_p_mut` avoids Lean misparsing `(1 - p_mut n).toReal`.

- [2026-05-27 13:00 UTC] goedel: failed — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T130046Z.log`
- [2026-05-27 13:02 UTC] goedel: ok — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T130117Z.log`
- [2026-05-27 15:08 UTC] goedel: ok — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T150820Z.log`
- [2026-05-27 15:09 UTC] goedel: ok — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T150846Z.log`
- [2026-05-27 15:14 UTC] goedel: ok — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T151004Z.log`
- [2026-05-27 15:19 UTC] goedel: ok — log `.mathprover/attempts/L703_mutation_prob_lower_bound/20260527T151506Z.log`
- [2026-05-27] manual: proof complete — merged from `attempt.lean` into main file
