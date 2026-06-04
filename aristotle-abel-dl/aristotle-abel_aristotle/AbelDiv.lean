import Mathlib

open Finset

/-
**Abel summation / Chebyshev-style divisor bound.**

If the partial sums `A(n) = ∑_{1 ≤ k ≤ n} a k` are bounded by `c · n`, and the
terms `a k` are nonnegative, then the "harmonically weighted" sum is bounded by
`c` times the harmonic sum:

  `∑_{1 ≤ n ≤ N} a n / n ≤ c · ∑_{1 ≤ n ≤ N} 1/n`.

This is the discrete analogue of `∫ A(t)/t² dt` partial summation. The intended
application: `a n = (if n.Prime then Real.log n else 0)`, whose partial sums are
the Chebyshev function `θ(n) ≤ n · log 4`, giving the Mertens estimate
`∑_{p ≤ N} (log p)/p = O(log N)`.

Proof sketch (summation by parts, `Finset.sum_range_by_parts`):
let `A n = ∑_{k ∈ Icc 1 n} a k`. Then
  `∑_{n=1}^N a n / n = A N / N + ∑_{n=1}^{N-1} A n · (1/n − 1/(n+1))`,
and each `A n · (1/n − 1/(n+1)) ≤ c·n·(1/n − 1/(n+1)) = c/(n+1)` (since the
weight `1/n − 1/(n+1) ≥ 0`), while `A N / N ≤ c`. Summing the telescoped
right-hand side gives `c·(1 + ∑_{n=2}^N 1/n) = c · ∑_{n=1}^N 1/n`.
-/
theorem abel_div_le (N : ℕ) (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0 ≤ a n)
    (hA : ∀ n, ∑ k ∈ Finset.Icc 1 n, a k ≤ c * (n : ℝ)) :
    ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) ≤ c * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
  -- By Abel's summation formula, we have:
  have h_abel : ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) = (∑ n ∈ Finset.Icc 1 N, a n) / N + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) / (n * (n + 1)) := by
    induction N <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring;
    cases ‹ℕ› <;> norm_num [ Finset.sum_Ioc_succ_top ] at * ; ring;
    grind;
  -- Applying the bound from `hA` to each term in the sum:
  have h_bound : (∑ n ∈ Finset.Icc 1 N, a n) / N + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) / (n * (n + 1)) ≤ c + ∑ n ∈ Finset.Icc 1 (N - 1), c / (n + 1) := by
    refine' add_le_add _ ( Finset.sum_le_sum fun n hn => _ );
    · exact div_le_of_le_mul₀ ( Nat.cast_nonneg _ ) hc ( hA N );
    · rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 1 by exact_mod_cast Finset.mem_Icc.mp hn |>.1, hA n, hc ];
  rcases N with ( _ | N ) <;> simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  exact h_bound.trans ( by erw [ Finset.sum_Ico_eq_sum_range _ _ ] ; erw [ Finset.sum_Ico_eq_sum_range _ _ ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ] )