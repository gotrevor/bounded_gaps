import Mathlib

open ArithmeticFunction Finset

/-- The Mertens summand `μ²(n)/φ(n)` (zero off the squarefree numbers). -/
noncomputable def mertensSummand (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

/-- **Euler-product upper bound (the Mertens 1D upper companion).**
`∑_{n=1}^{N} μ²(n)/φ(n) ≤ ∏_{p ≤ N, p prime} (1 + 1/(p-1))`.

Mathematical content: `μ²` restricts the sum to squarefree `n`, and for squarefree
`n = p₁⋯p_k` the summand `μ²(n)/φ(n) = ∏_{p∣n} 1/(p-1)` is multiplicative with
`g(p) = 1/(p-1)`. Expanding the finite product over primes `p ≤ N`
(`Finset.prod_add` / `Finset.prod_one_add` gives `∏_p (1 + g(p)) =
∑_{S ⊆ {p≤N}} ∏_{p∈S} g(p)`), each term is `μ²(d)/φ(d)` for the squarefree
`d = ∏_{p∈S} p`, and every squarefree `d ≤ N` arises from some such `S` (its set
of prime factors, all `≤ d ≤ N`). Hence the truncated sum is dominated by the full
product (extra non-negative terms for squarefree `d` with `d > N` but all prime
factors `≤ N`).

Suggested route: reduce to squarefree `n` (the others contribute `0`); rewrite
`mertensSummand n = ∏_{p ∈ n.primeFactors} 1/((p:ℝ)-1)` for squarefree `n > 0`
(via `Nat.totient` on squarefree = `∏_{p∣n}(p-1)`, `ArithmeticFunction.moebius`
squarefree `= ±1` so `μ² = 1`); then map each squarefree `n ≤ N` to its
`primeFactors ⊆ (Icc 2 N).filter Nat.Prime` and apply `Finset.prod_one_add`
(`∏_{i∈s}(1 + f i) = ∑_{t ⊆ s} ∏_{i∈t} f i`) with non-negativity of the dropped
terms (`Finset.sum_le_sum_of_subset_of_nonneg`). -/
theorem mertens_prod_upper (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, mertensSummand n ≤
      ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 + 1 / ((p : ℝ) - 1)) := by
  sorry
