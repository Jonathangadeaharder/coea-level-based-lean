# Paper source — `coea_sel_measure_prob`

## Statement (informal)
The best-of-λ selection measure, defined via the weight-level CDF
decomposition
```
μ_sel = Σ_x ((sel_cdf(hw(x)+1) - sel_cdf(hw(x))) / C(n, hw(x))) · δ_x ,
```
integrates to 1 over the whole bitcube `{0,1}^n`.

## Citation
No external paper. This is the definitional check that `coea_sel_measure` is a probability measure (required for the `IsMarkovKernel coea_sel_kernel` instance at LBTCoupling.lean:679).

## Paper-style proof

Group the sum over `x` by Hamming weight:
```
Σ_x w(x) = Σ_{w=0..n} Σ_{x : hw(x)=w} ((sel_cdf(w+1) - sel_cdf(w)) / C(n,w))
        = Σ_{w=0..n} C(n,w) · (sel_cdf(w+1) - sel_cdf(w)) / C(n,w)
        = Σ_{w=0..n} (sel_cdf(w+1) - sel_cdf(w))
        = sel_cdf(n+1) - sel_cdf(0)            [telescoping]
        = (1 - μ(A_ge(n+1)))^λ - (1 - μ(A_ge(0)))^λ
        = (1 - 0)^λ - (1 - 1)^λ
        = 1 - 0 = 1.
```
where `sel_cdf(n+1) = (1 - 0)^λ = 1` since `A_ge(n+1) = ∅`, and
`sel_cdf(0) = (1 - 1)^λ = 0^λ = 0` for `λ ≥ 1`, since `A_ge(0) = univ` and `μ(univ) = 1` by `coea_measure_univ`.

## Mathlib candidates
- `Finset.sum_fiberwise_of_maps_to` — group by hamming_weight (the "fiber").
- `Finset.sum_range_succ` — for the telescoping inner sum.
- `ENNReal.sub_add_cancel_of_le`
- `Measure.sum_apply`, `measure_sum_apply` (already in file)
- `Nat.card_filter_hamming_weight_eq` (likely not in Mathlib; may need bespoke lemma)
- `Finset.card_eq_choose` (binomial coefficient = card of level set)

## Key intermediate fact
**Cardinality of a level set**: `Nat.card {x : BitString n // hw(x) = w} = C(n, w)`. May need to prove this as a child lemma; closely related to `Finset.card_powersetCard`.
