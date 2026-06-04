import Mathlib

open scoped BigOperators
open Real

/-!
# k-dimensional Dirichlet hyperbola count bound.

The number of ordered k-tuples of positive integers with product ≤ N is
`≍ N (log N)^{k-1}` (the summatory function of the k-fold divisor function).
We need the clean UPPER bound

  `#{ d : Fin k → ℕ | (∀i, 1 ≤ dᵢ) ∧ ∏ᵢ dᵢ ≤ N } ≤ N · (1 + log N)^{k-1}`   (k ≥ 1).

This is the last missing analytic brick for GPY/Maynard sub-step (c) analytic
obligation #2 (`∑_{diag}|coeff| = o(main)`): the diagonal sieve weight is bounded
by `‖F‖∞² ·` this count (see `BoundedGaps.Sieve.diagonal_weight_le_count`), and
`N·(log N)^{k-1} = o(N·(log N)^k)` gives the required `o(main)`.

## Proof sketch (induction on k)
- **k = 1:** the set is `{d : d ≤ N}`, card `= N`; RHS `= N·(1+log N)^0 = N`. ✓
- **k → k+1:** partition the (k+1)-tuples by the value `m = d 0 ∈ [1,N]`. The fiber
  is `{ d' : Fin k → ℕ | ∏ d' ≤ N/m }` (nat division `⌊N/m⌋`), so
  `count_{k+1}(N) = ∑_{m=1}^N count_k(⌊N/m⌋)`
  `≤ ∑_{m=1}^N ⌊N/m⌋ · (1 + log⌊N/m⌋)^{k-1}`   (induction hyp)
  `≤ (1+log N)^{k-1} · ∑_{m=1}^N (N/m)`           (`⌊N/m⌋ ≤ N/m ≤ N`, `log` monotone)
  `≤ (1+log N)^{k-1} · N·(1+log N)`               (`∑_{m≤N} 1/m = harmonic N ≤ 1+log N`)
  `= N·(1+log N)^k`. ✓

## Mathlib ingredients
- `harmonic_le_one_add_log : harmonic n ≤ 1 + Real.log n` (the harmonic upper bound).
- `harmonic` `= ∑_{m=1}^n 1/m` (`harmonic_eq_sum_Icc` / its def).
- `Nat.le_div_iff_mul_le`, `Nat.div_le_self`, floor vs `N/m ≤ (N:ℝ)/m`.
- `Finset.card_eq_sum_card_fiberwise` (partition the filtered set by coordinate 0),
  `Fintype.piFinset`, `Fin.cons`/`Fin.tail` to peel coordinate 0.
- `Real.log` monotone (`Real.log_le_log`), `pow_le_pow_left₀`.

Prove the `sorry`. Keep it `#print axioms`-clean (no new axioms, no `sorry`).
-/

theorem hyperbola_count_le (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) :
    (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
        (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ)
      ≤ (N : ℝ) * (1 + Real.log N) ^ (k - 1) := by
  sorry
