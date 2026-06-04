import Mathlib

open Finset

/-- **Prime-power tail bound.** The von Mangoldt sum restricted to TRUE prime powers
`p^k` with `k ≥ 2` (i.e. prime powers that are not themselves prime) is bounded by 1,
uniformly in N:

  `∑_{n ≤ N, n a prime power but not prime} Λ(n)/n ≤ 1`.

This is the convergent tail separating `∑_{n≤N} Λ(n)/n` from `∑_{p≤N} (log p)/p`.
Reason: `Λ(p^k) = log p`, so the sum is `∑_{p} (log p)·∑_{k≥2, p^k≤N} p^{-k}`
`≤ ∑_p (log p)·p^{-2}/(1-1/p) = ∑_p (log p)/(p(p-1))`, and this prime sum is
`≈ 0.76 < 1` (dominated by p=2: log2/2 ≈ 0.347). Useful facts:
`ArithmeticFunction.vonMangoldt_apply` (Λ n = if IsPrimePow n then log(minFac n) else 0),
`IsPrimePow`, `Nat.minFac`, geometric series `tsum_geometric_of_lt_one`. -/
theorem prime_power_tail_le (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ 1 := by
  sorry
