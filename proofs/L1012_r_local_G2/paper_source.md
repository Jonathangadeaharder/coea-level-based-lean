# Paper source — `r_local_G2`

## Statement (informal)
The G2 growth-rate condition of the Level-Based Theorem holds for the r-local CoEA on OneMax level sets, with `z_j = (n-j)/n` (or `1/n` at the top).

## Citation
Corus, Dang, Eremeev, Lehre, *IEEE TEVC* 22(5):707–719, 2018. **Condition G2 instantiation** for OneMax-style level sets (their Section IV).

## Paper-style proof
Need: for every level `j ∈ Fin (n+1)`, parent population `P`, and parent count `c` with `0 < c ≤ (1/4)·λ`,
```
(coea_sel_kernel G K λ) P (A_ge (A_lvl n) j.val) .toReal ≥ z_j · c / λ ,
```
where `z_j = (n - j)/n` for `j < n` and `z_n = 1/n`.

**Step 1.** By L693 (`sel_monotone_level`), `μ_sel(A_ge(j)) ≥ μ(A_ge(j))`.

**Step 2.** Bound `μ(A_ge(j))` from below by the parent count fraction. Each parent `P i ∈ A_ge(j)` contributes at least `(1 - 1/n)^n ≥ 1/4` to `μ(A_ge(j))` via the no-mutation event. So
```
μ(A_ge(j)) ≥ λ^{-1} · c · (1 - 1/n)^n ≥ c / (4λ).
```

**Step 3.** Combine: `μ_sel(A_ge(j)) ≥ c/(4λ)`. Now check against `z_j · c/λ`:
- If `j < n`: `z_j = (n-j)/n ≤ 1`, so need `c/(4λ) ≥ ((n-j)/n) · c/λ` iff `n ≥ 4(n-j)` iff `j ≥ 3n/4`. This is **not** enough by itself.
- The actual paper uses the upgrade selection amplification: `μ_sel(A_ge(j)) = 1 - (1-μ(A_ge(j)))^λ` which is much bigger than `μ(A_ge(j))` when `μ` is small.

**Step 3'.** Use L669 to write `μ_sel = 1 - (1-μ)^λ`. For `μ ∈ [c/(4λ), 1/4]` and `λ` large per `h_lambda_large`, the amplification gives `μ_sel ≥ z_j · c/λ`. Detailed inequality chain mirrors `sel_amplification_bound` (already proved in LBTCoupling.lean:880).

## Note on z_j = (n-j)/n vs (n-j)/(en)
The paper's standard z_j for the OneMax LBT is `(n-j)/(en)`. The `r_local_z` in the Lean file uses `(n-j)/n`. The mutation factor `1/e` is absorbed into the population-size precondition `lambda_pop ≥ ...` rather than into `z_j`. Cross-check signature carefully when porting.

## Mathlib candidates
- Reuse `sel_amplification_bound` machinery wholesale; G2 is its `j-indexed` cousin.

## Dependency chain
L1012 → L669 (CDF) and L715 (count→measure) and (already-proved) `sel_amplification_bound`.
