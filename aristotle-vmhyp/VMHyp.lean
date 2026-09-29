/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

open Finset

/-- **Von Mangoldt hyperbola identity** (entry point to *sharp* Mertens' first
theorem). With `Λ` the von Mangoldt function and `⌊N/n⌋ = N / n` (nat division),

  `∑_{1≤n≤N} Λ(n)·⌊N/n⌋ = ∑_{1≤m≤N} log m  ( = log (N!) )`.

Proof: `⌊N/n⌋ = #{m ≤ N : n ∣ m}`, so swapping the order of summation gives
`∑_{m≤N} ∑_{n∣m} Λ(n) = ∑_{m≤N} log m` by `ArithmeticFunction.vonMangoldt_sum`
(`∑_{i∣m} Λ i = log m`). This is the standard divisor/hyperbola manipulation. -/
theorem vonMangoldt_hyperbola (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  sorry
