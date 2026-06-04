import Mathlib

open scoped BigOperators

/-!
# Bounded log-weighted b-series: `∑_{e≤N} |b(e)|·|log e| ≤ 20`.

`b : ℕ → ℝ` is the multiplicative function of the sharp Mertens asymptotic
`∑_{n≤x} μ²(n)/φ(n) = log x + O(1)`, with prime-power values
  `b(1)=1, b(p)=1/(p(p-1)), b(p²)=−1/(p(p-1)), b(p^k)=0 (k≥3)`,
multiplicative on coprime arguments. We need the LOG-WEIGHTED absolute series to be
uniformly bounded (it controls the `Q(N)=∑ b(e) log e` term of the decomposition, so
`Q(N)=O(1)` hence `Q(N)/log N → 0`).

The unweighted bound `∑_{e≤N}|b(e)| ≤ 8` is its companion (sister job). This is the
weighted version; the constant `20` is generous.

## Strategy (von Mangoldt / additivity of log)

`Real.log e = ∑_{d ∣ e} Λ(d)` (`vonMangoldt_sum` : `∑_{d∣n} Λ d = log n`). So
  `∑_{e≤N} |b(e)|·log e = ∑_{e≤N} |b(e)| ∑_{d∣e} Λ(d)
                        = ∑_{d≤N} Λ(d) · ∑_{e≤N, d∣e} |b(e)|`.
`Λ(d) ≠ 0` only for `d = p^k`; and `∑_{e: p^k∣e} |b(e)| ≤ (∑_e |b(e)|) =: M ≤ 8`
restricted, more precisely `≤ M·(|b(p)|+|b(p²)|) = M·2/(p(p-1))` for the `p`-part.
Summing `Λ(p^k)=log p`:
  `≤ M · ∑_p (∑_k log p · [p^k contributes]) · 2/(p(p-1)) ≪ ∑_p (log p)/(p(p-1)) < ∞`.
Telescoping/comparison `∑_p (log p)/(p(p-1)) ≤ ∑_{k≥2} (log k)/(k(k-1))` converges
(e.g. `(log k)/(k(k-1)) ≤ 2/k^{3/2}` for `k ≥ 2`, or compare to `∑ k^{-3/2}`).

Alternatively, bound directly via the Euler-product expansion as in the unweighted
sister, carrying the extra `log e = ∑_{p^a‖e} a log p ≤ 2∑_{p∣e} log p` factor.

For e ≥ 1, `log e ≥ 0`, so `|log e| = log e` on the support. Keep `#print axioms`-clean
(only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
-/

namespace BLog

axiom b : ℕ → ℝ
axiom b_one : b 1 = 1
axiom b_mul {m n : ℕ} (h : Nat.Coprime m n) : b (m * n) = b m * b n
axiom b_prime {p : ℕ} (hp : p.Prime) : b p = 1 / ((p : ℝ) * ((p : ℝ) - 1))
axiom b_prime_sq {p : ℕ} (hp : p.Prime) : b (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))
axiom b_prime_pow_high {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k) : b (p ^ k) = 0

/-- **Target.** The log-weighted absolute b-series is uniformly bounded by `20`. -/
theorem blog_bounded (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, |b e| * |Real.log (e : ℝ)| ≤ 20 := by
  sorry

end BLog
