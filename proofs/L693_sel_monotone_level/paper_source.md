# Paper source — `sel_monotone_level`

## Statement (informal)
Best-of-λ selection (weakly) increases the probability of being in any upper-level set: `μ_sel(A_ge(j)) ≥ μ(A_ge(j))`.

## Citation
Trivial consequence of the order-statistic inequality `1 - (1-p)^λ ≥ p` for `p ∈ [0,1]`, `λ ≥ 1`. Standard probability folklore. In Mathlib, this follows from `Real.one_sub_pow_le_one_sub_of_*` or directly from Bernoulli.

## Paper-style proof

From L669, `μ_sel(A_ge(j)) = 1 - (1 - μ(A_ge(j)))^λ`. Set `p := μ(A_ge(j)).toReal ∈ [0,1]`. We need `1 - (1-p)^λ ≥ p`.

Equivalently `(1-p)^λ ≤ 1-p`. Since `λ ≥ 1` and `1 - p ∈ [0,1]`:
```
(1-p)^λ ≤ (1-p)^1 = 1 - p .
```
Subtracting from 1: `1 - (1-p)^λ ≥ p`. ∎

## Mathlib candidates
- `pow_le_pow_right_of_le_one : 0 ≤ a → a ≤ 1 → m ≤ n → a^n ≤ a^m`  (apply with `m=1, n=λ`)
- ENNReal lift: `ENNReal.toReal_pow`, `ENNReal.toReal_sub_of_le`
- For the toReal version: `ENNReal.toReal_mono`, `ENNReal.sub_le_sub_left`
