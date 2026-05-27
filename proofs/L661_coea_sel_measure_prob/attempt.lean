-- WORKER SCRATCHPAD for L661 coea_sel_measure_prob.
-- Goedel/Aristotle: close the sorry below using paper_source.md.
-- Merge: copy proof body into LBTCoupling.lean:657 (replace sorry).

import LBTCoupling

open MeasureTheory ENNReal

namespace L661Attempt

lemma coea_sel_measure_prob {n : ℕ} (lambda_pop : ℕ)
    (P : Population (BitString n) lambda_pop) :
    coea_sel_measure lambda_pop P Set.univ = 1 := by
  dsimp [coea_sel_measure]
  split_ifs with h
  · simp [Measure.dirac_apply_of_mem (Set.mem_univ _)]
  · sorry

end L661Attempt
