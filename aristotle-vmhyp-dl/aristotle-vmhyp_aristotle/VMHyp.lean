import Mathlib

open Finset

/-
**Von Mangoldt hyperbola identity** (entry point to *sharp* Mertens' first
theorem). With `Λ` the von Mangoldt function and `⌊N/n⌋ = N / n` (nat division),

  `∑_{1≤n≤N} Λ(n)·⌊N/n⌋ = ∑_{1≤m≤N} log m  ( = log (N!) )`.

Proof: `⌊N/n⌋ = #{m ≤ N : n ∣ m}`, so swapping the order of summation gives
`∑_{m≤N} ∑_{n∣m} Λ(n) = ∑_{m≤N} log m` by `ArithmeticFunction.vonMangoldt_sum`
(`∑_{i∣m} Λ i = log m`). This is the standard divisor/hyperbola manipulation.
-/
theorem vonMangoldt_hyperbola (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  -- By interchanging the order of summation, we can rewrite the left-hand side as:
  have h_interchange : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) * (Finset.card (Finset.filter (fun m => n ∣ m) (Finset.Icc 1 N))) = ∑ m ∈ Finset.Icc 1 N, (∑ n ∈ Finset.filter (fun n => n ∣ m) (Finset.Icc 1 N), (ArithmeticFunction.vonMangoldt n)) := by
    simp +decide only [card_filter, sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Nat.cast_sum ] ; rw [ Finset.mul_sum ] ; congr ; ext ; aesop;
  have h_filter : ∀ m ∈ Finset.Icc 1 N, (Finset.filter (fun n => n ∣ m) (Finset.Icc 1 N)) = (Nat.divisors m) := by
    simp +contextual [ Finset.ext_iff, Nat.mem_divisors ];
    exact fun m hm₁ hm₂ a => ⟨ fun h => ⟨ h.2, by linarith ⟩, fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hm₁, Nat.le_trans ( Nat.le_of_dvd hm₁ h.1 ) hm₂ ⟩, h.1 ⟩ ⟩;
  convert h_interchange using 1;
  · convert rfl;
    convert Nat.Ioc_filter_dvd_card_eq_div N ‹_› using 1;
  · rw [ Finset.sum_congr rfl ];
    intro m hm; rw [ ← ArithmeticFunction.vonMangoldt_sum ] ; aesop;