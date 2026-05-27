# Paper source — `mutation_prob_lower_bound`

## Citation
Corus, Dang, Eremeev, Lehre, *Level-Based Analysis of Genetic Algorithms and Other Search Processes*, IEEE TEVC 22(5):707–719, 2018. **Lemma 2**.

Also: Doerr, *Analyzing randomized search heuristics: tools from probability theory*, Series on Theoretical Computer Science (2011), folklore.

## Statement (informal)

For standard bit mutation with rate `p = 1/n` on the `n`-bit hypercube, any parent `x` at Hamming level `≥ j` (with `j < n`) produces an offspring at level `≥ j+1` with probability at least `1/(e·n)`.

## Paper-style proof

`x ∈ A_ge j` and `j < n` ⇒ there exists at least one bit position `k*` with `x k* = false` (otherwise `hw(x) = n > j` is fine, but actually we need at least `n - j ≥ 1` false bits when `hw(x) ≤ n`; since `hw(x) ≥ j`, and `j < n`, false-bit-count `= n - hw(x) ≤ n - j`; we need this ≥ 1, which holds iff `hw(x) ≤ n - 1`. If `hw(x) = n` then `x` is already at the target, and `A_ge (j+1)` trivially contains `x` itself via the no-mutation event, giving probability `(1-1/n)^n ≥ 1/4 ≥ 1/(en)` for `n ≥ 2`).

**Case A: `hw(x) < n`.** Pick any false bit `k*`. Construct `y := x[k* ↦ true]`. Then `hw(y) = hw(x) + 1 ≥ j + 1`, so `y ∈ A_lvl ⟨hw(x)+1, ...⟩ ⊆ A_ge (j+1)`. The mutation probability of producing exactly `y` is
```
mutation_prob x y = ∏_k bit_prob n (x k) (y k)
                  = (1/n) · ∏_{k ≠ k*} (1 - 1/n)
                  = (1/n) · (1 - 1/n)^(n-1)
                  ≥ (1/n) · (1/e)              [standard inequality]
                  = 1/(e·n).
```
Hence `parent_mut_measure x (A_ge (j+1)) ≥ parent_mut_measure x {y} = mutation_prob x y ≥ 1/(e·n)`.

**Case B: `hw(x) = n`.** Then `x ∈ A_ge (j+1)` already. The no-mutation event has probability `(1 - 1/n)^n ≥ exp(-1) · n/(n-1) ≥ 1/(e·n)` for `n ≥ 2`. (Actually we get `≥ 1/4`, much stronger.) So `parent_mut_measure x {x} ≥ (1-1/n)^n ≥ 1/(en)`.

Both cases give the claim.

## Standard inequality used

`(1 - 1/n)^(n-1) ≥ 1/e` for `n ≥ 1`. Proof via `log(1-x) ≥ -x/(1-x)`:
```
(n-1)·log(1-1/n) ≥ (n-1) · (-(1/n)/(1-1/n)) = (n-1) · (-1/(n-1)) = -1.
```
Hence `(1-1/n)^(n-1) ≥ e^{-1} = 1/e`.

## Mathlib candidates
- `Real.one_sub_le_exp_neg : 1 - x ≤ Real.exp (-x)`
- `Real.exp_neg`, `Real.exp_one_pow`
- `Real.log_le_sub_one_of_pos`
- For ENNReal: `ENNReal.toReal_pow`, `ENNReal.toReal_inv`, `Measure.dirac_apply_of_mem`.
