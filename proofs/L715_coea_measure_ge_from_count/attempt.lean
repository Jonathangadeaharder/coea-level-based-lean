-- WORKER SCRATCHPAD for L715 coea_measure_ge_from_count.
-- 1. Unfold coea_measure = λ^{-1} · Σ_i parent_mut_measure.
-- 2. Restrict the sum to indices with P i ∈ A_ge j; LB by L703 per index.
-- 3. Combine with h_count to get λ^{-1} · (λ/4) · (1/(en)) = 1/(4en).

import LBTCoupling

-- TODO(worker): proof body. Depends on L703.
