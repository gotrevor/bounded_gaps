import Mathlib

open scoped BigOperators

/-!
# General Dirichlet hyperbola interchange.

For any real-valued `g : ℕ → ℝ` and `N : ℕ`, summing `g` over the divisors of
each `n ∈ [1, N]` and then over `n` equals summing `g d` weighted by the number
of multiples `⌊N/d⌋ = N / d` of `d` in `[1, N]`:

  `∑_{n=1}^N ∑_{d ∣ n} g d = ∑_{d=1}^N g d · ⌊N/d⌋`.

This is the standard summation interchange behind every summatory-function /
Dirichlet-hyperbola asymptotic. (A `vonMangoldt`-weighted special case is already
proven; this is the general form.) Mathlib ingredients: `Nat.divisors`,
`Finset.sum_comm`, and `#{n ∈ Icc 1 N : d ∣ n} = N / d`
(`Nat.Ioc_filter_dvd_card_eq_div`, noting `Icc 1 N = Ioc 0 N`).

Prove the `sorry`. Keep it `#print axioms`-clean (no new axioms, no `sorry`).
-/

theorem dirichlet_hyperbola (N : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, g d)
      = ∑ d ∈ Finset.Icc 1 N, g d * ((N / d : ℕ) : ℝ) := by
  sorry
