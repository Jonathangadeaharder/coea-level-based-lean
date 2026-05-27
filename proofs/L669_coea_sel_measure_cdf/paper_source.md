# Paper source — `coea_sel_measure_cdf`

## Statement (informal)
The selection measure assigns to the upper-level set `A_ge(k) = {x : hw(x) ≥ k}` the probability
```
μ_sel(A_ge(k)) = 1 - (1 - μ(A_ge(k)))^λ ,
```
i.e. one minus the chance that all λ sampled offspring have weight strictly below `k`.

## Citation
Standard order-statistic CDF identity. See Casella & Berger, *Statistical Inference*, §5.4, on max of i.i.d. random variables; or any probability textbook on the CDF of `max(X_1, …, X_λ)` for i.i.d. `X_i ∼ μ`. Best-of-λ selection in the EA literature: e.g. Lehre, *Fitness-levels for non-elitist populations*, GECCO 2011.

## Paper-style proof
Partition `A_ge(k) = ⊔_{w=k..n} A_lvl(w)`. The selection measure on `A_lvl(w)` is
```
μ_sel(A_lvl(w)) = C(n,w) · (sel_cdf(w+1) - sel_cdf(w)) / C(n,w)
                = sel_cdf(w+1) - sel_cdf(w).
```
Summing telescopically from `w = k` to `w = n`:
```
μ_sel(A_ge(k)) = Σ_{w=k..n} (sel_cdf(w+1) - sel_cdf(w))
              = sel_cdf(n+1) - sel_cdf(k)
              = 1 - (1 - μ(A_ge(k)))^λ ,
```
since `sel_cdf(n+1) = (1 - μ(A_ge(n+1)))^λ = 1^λ = 1` (the empty set has measure 0) and `sel_cdf(k)` is by definition `(1 - μ(A_ge(k)))^λ`.

## Mathlib candidates
Same as L661, plus:
- `Finset.sum_Ico_telescope_eq` or hand-rolled telescoping
- `pow_zero`, `one_pow` for boundary cases
- `ENNReal.sub_self` (`a - a = 0` in ENNReal under subtractable conditions)
