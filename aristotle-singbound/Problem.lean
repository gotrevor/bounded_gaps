import Mathlib

open scoped BigOperators
open ArithmeticFunction

/-!
# Bounded singular sum: `∑_{d≤N} μ²(d)/(φ(d)·d) ≤ 3`.

The main-term coefficient of the average `∑_{n≤N} n/φ(n) = ∑_{d≤N} (μ²(d)/φ(d))·⌊N/d⌋`
is the singular sum `∑_{d≤N} μ²(d)/(φ(d)·d)`, which is bounded by an absolute
constant (it converges to `ζ(2)ζ(3)/ζ(6)`). Here we only need a crude uniform bound.

Strategy (one standard route):
* Only squarefree `d` contribute (`μ(d)² = 1` iff `d` squarefree, else `0`).
* For squarefree `d`, `μ²(d)/(φ(d)·d) = ∏_{p∣d} 1/(p·(p-1))` since `φ` and `id`
  are multiplicative on squarefree numbers, and the factor at a prime `p` is
  `1/((p-1)·p)`.
* Summing over squarefree `d ∈ [1,N]` (subsets of the prime factors) gives a value
  `≤ ∏_{p ≤ N} (1 + 1/(p·(p-1)))` (expand the product; the squarefree-divisor sum
  is a sub-sum). Use `Finset.prod_one_add` / `sum_divisors_filter_squarefree`.
* `∏_{p} (1 + 1/(p(p-1))) ≤ exp(∑_p 1/(p(p-1)))` (since `1+x ≤ exp x`), and
  `∑_p 1/(p(p-1)) ≤ ∑_{k=2}^∞ 1/(k(k-1)) = 1` by telescoping `1/(k(k-1)) = 1/(k-1) - 1/k`.
* Hence the sum is `≤ exp 1 < 3`.

Any correct proof is fine; the constant `3` is generous. Keep it `#print axioms`-clean
(only `propext`, `Classical.choice`, `Quot.sound`; no new axioms, no `sorry`).
-/

theorem singular_sum_bounded (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) * (d : ℝ)) ≤ 3 := by
  sorry
