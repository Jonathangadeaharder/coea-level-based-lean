# Paper source — `coea_measure_ge_from_count`

## Statement (informal)
If at least `λ/4` parents in `P` are at level `≥ j`, then the offspring
mutation distribution averaged over all parents puts probability at least
`1/(4·e·n)` on level `≥ j+1`.

## Citation
Corus et al. 2018, derivation of the **G1** condition for OneMax level sets. Standard EA-theory averaging.

## Paper-style proof
By definition `coea_measure = λ^{-1} · Σ_{i} parent_mut_measure(P i)`. So
```
coea_measure(A_ge(j+1)) = λ^{-1} · Σ_{i} parent_mut_measure(P i)(A_ge(j+1))
                       ≥ λ^{-1} · Σ_{i: P i ∈ A_ge(j)} parent_mut_measure(P i)(A_ge(j+1))
                       ≥ λ^{-1} · #{i: P i ∈ A_ge(j)} · (1/(en))    [by L703]
                       ≥ λ^{-1} · (λ/4) · (1/(en))                   [by h_count]
                       = 1 / (4·e·n).
```

## Mathlib candidates
- `Measure.sum_apply` (already in file as `measure_sum_apply`)
- `Finset.sum_le_sum`
- `Nat.card_pos_iff` and `Finset.card_filter`
- ENNReal-to-Real conversion at the end.
