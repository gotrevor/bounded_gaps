import Mathlib

open scoped BigOperators

/-!
# Bounded absolute b-series: `∑_{e≤N} |b(e)| ≤ 8`.

`b : ℕ → ℝ` is the multiplicative arithmetic function arising in the sharp Mertens
asymptotic `∑_{n≤x} μ²(n)/φ(n) = log x + O(1)` (it is `B(e)/e`, `B = μ ⋆ (id·g)`,
`g = μ²/φ`). Its prime-power values are
  `b(1)=1,  b(p)=1/(p(p-1)),  b(p²)=−1/(p(p-1)),  b(p^k)=0 (k≥3)`,
and it is multiplicative on coprime arguments. We need its absolute series to be
uniformly bounded (this controls the `O(1)` error terms in the assembly).

These facts are supplied as axioms (proved in the real development from
`B := μ ⋆ (id · μ²/φ)`); only the analytic bound is open.

## Strategy (the Euler-product route; this exact route proved the sister bound
`∑_{d≤N} μ²(d)/(φ(d)d) ≤ 3` cleanly)

`|b|` is multiplicative with `|b(p)| = |b(p²)| = 1/(p(p-1))`, `|b(p^k)|=0 (k≥3)`.
Every `e` with `b(e)≠0` factors uniquely as `e = a·c²` with `a, c` squarefree and
`coprime a c` (a = product of the exponent-1 primes, c = product of the exponent-2
primes), and `|b(e)| = h(a)·h(c)` where `h(s) = ∏_{p∣s} 1/(p(p-1))` over squarefree s.
Hence
  `∑_{e≤N} |b(e)| ≤ (∑_{s squarefree} h(s))²`.
For the inner squarefree sum, the standard Euler-product / powerset-expansion bound
gives `∑_{s squarefree, s≤N} h(s) ≤ ∏_{p≤N}(1 + 1/(p(p-1))) ≤ exp(∑_p 1/(p(p-1))) ≤ exp 1`
(telescoping `1/(k(k-1)) = 1/(k-1) − 1/k ⇒ ∑ ≤ 1`). So `∑_{e≤N}|b(e)| ≤ (exp 1)² = exp 2 < 8`.

Any correct proof is fine; the constant `8` is generous. Keep it `#print axioms`-clean
(only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no new axioms beyond
those provided below).
-/

namespace BAbs

/-- The multiplicative b-function (supplied abstractly by its defining properties). -/
axiom b : ℕ → ℝ
axiom b_one : b 1 = 1
/-- Multiplicative on coprime arguments. -/
axiom b_mul {m n : ℕ} (h : Nat.Coprime m n) : b (m * n) = b m * b n
/-- `b(p) = 1/(p(p-1))` at primes. -/
axiom b_prime {p : ℕ} (hp : p.Prime) : b p = 1 / ((p : ℝ) * ((p : ℝ) - 1))
/-- `b(p²) = −1/(p(p-1))` at prime squares. -/
axiom b_prime_sq {p : ℕ} (hp : p.Prime) : b (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))
/-- `b(p^k) = 0` for `k ≥ 3`. -/
axiom b_prime_pow_high {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k) : b (p ^ k) = 0

/-- **Target.** The absolute b-series is uniformly bounded by `8`. -/
theorem babs_bounded (N : ℕ) : ∑ e ∈ Finset.Icc 1 N, |b e| ≤ 8 := by
  sorry

end BAbs
