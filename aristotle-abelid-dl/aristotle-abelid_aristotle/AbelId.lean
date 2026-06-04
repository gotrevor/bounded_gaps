import Mathlib

open Finset

/-- **Abel summation identity (summation by parts).**

For arbitrary real sequences `a, w : ℕ → ℝ`, writing the partial sums
`A n = ∑_{k=1}^{n} a k`, one has

  `∑_{n=1}^N a n · w n = A N · w N − ∑_{n=1}^{N-1} A n · (w (n+1) − w n)`.

This is the discrete analogue of integration by parts. It is the key tool for
converting a partial-sum bound `A n ≤ f n` into a bound on a weighted sum
`∑ a n · w n` (e.g. Chebyshev θ-bounds into Mertens prime-reciprocal sums).

Proof: induction on `N` (with `A 0 = 0`, reindex the shifted sum).
-/
theorem abel_summation_identity (N : ℕ) (a w : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, a n * w n
      = (∑ k ∈ Finset.Icc 1 N, a k) * w N
        - ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) * (w (n + 1) - w n) := by
  induction' N with N ih <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring!;
  cases N <;> norm_num [ add_comm, Finset.sum_Ioc_succ_top ] at * ; linarith!;