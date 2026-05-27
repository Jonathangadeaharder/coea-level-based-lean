state: blocked
owner: (unassigned)
depends_on: L669_coea_sel_measure_cdf
estimated_lines: 40–80
estimated_hours: 2–4

# Notes
Once L669 (the CDF identity) is proved, this lemma is a one-line consequence:
rewrite via L669, then apply `pow_le_pow_right_of_le_one` on `1 - p ∈ [0,1]`.

Worker may start in "shadow mode" (assume L669 via local placeholder axiom) to
develop the toReal/ENNReal arithmetic, then swap to the real lemma when ready.
