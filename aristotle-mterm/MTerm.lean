import Mathlib

/-- **Mertens-2nd term bound.** For `n ≥ 2`,

  `(1 + log n)·(1/log n − 1/log (n+1)) ≤ (1 + 1/log 2) / (n · log n)`.

This bounds each summand of the difference-sum in the second Abel step toward
`∑_{p≤N} 1/p`. Derivation:
* `1/log n − 1/log(n+1) = (log(n+1) − log n)/(log n · log(n+1))`;
* `log(n+1) − log n = log((n+1)/n) = log(1 + 1/n) ≤ 1/n` (`Real.log_le_sub_one_of_pos`);
* `log n ≤ log(n+1)`, so `(log(n+1)−log n)·log n ≤ (1/n)·log(n+1)`, giving
  `1/log n − 1/log(n+1) ≤ (1/n)/(log n)²`;
* `1 + log n ≤ (1 + 1/log 2)·log n` since `1 ≤ log n / log 2` for `n ≥ 2`.
Multiplying gives the claim. All logs are positive for `n ≥ 2`. -/
theorem mertens_second_term_bound (n : ℕ) (hn : 2 ≤ n) :
    (1 + Real.log n) * (1 / Real.log n - 1 / Real.log (n + 1))
      ≤ (1 + 1 / Real.log 2) / ((n : ℝ) * Real.log n) := by
  sorry
