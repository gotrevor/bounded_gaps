import Mathlib

open scoped BigOperators

/-!
# Riemann-sum convergence for the `1/n` log-weight (analytic heart of GPY sub-step (c))

The GPY/Maynard sieve main term needs the WEIGHTED Mertens asymptotic
`∑_{d≤R} (μ²(d)/φ(d))·F(log d / log R) ∼ (∫₀¹ F)·log R`. By Abel summation against the
sharp Mertens asymptotic `∑_{d≤t} μ²/φ ∼ log t` (already proved, axiom-clean), this reduces
to the **model case** where the arithmetic weight is replaced by its average `1/n`:

  `(1 / log R) · ∑_{n=2}^{⌊R⌋} (1/n)·F(log n / log R)  →  ∫₀¹ F(u) du`   as `R → ∞`.

This is a pure real-analysis Riemann-sum statement (no number theory): with the substitution
`u = log n / log R` (so `Δu ≈ 1/(n log R)`), the sum is a Riemann sum of `F` over `[0,1]`.

## Strategy
Compare the sum to the integral `∫_2^R (1/t) F(log t / log R) dt`. Substitute `u = log t/log R`
(`du = dt/(t log R)`): the integral equals `log R · ∫_{log 2/log R}^{1} F(u) du`, and dividing by
`log R` gives `∫_{log2/logR}^1 F → ∫₀¹ F` (lower limit → 0). The sum-vs-integral error is
`O(1/log R) → 0` because `t ↦ (1/t)F(log t/log R)` has bounded variation on `[2,R]`
(`F` continuous on the compact `[0,1]`, so bounded and uniformly continuous; the monotone
`1/t` factor controls the comparison — `AntitoneOn.sum_le_integral_Ico` / `MonotoneOn` sandwich,
plus uniform continuity of `F` to absorb the sample-point error). Keep `#print axioms` clean
(only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
-/

namespace WMertens

/-- **Riemann-sum convergence for the `1/n` log-weight.** For `F` continuous on `[0,1]`,
`(∑_{n=2}^{R} (1/n)·F(log n/log R)) / log R → ∫₀¹ F`. -/
theorem riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0:ℝ) 1)) :
    Filter.Tendsto
      (fun R : ℕ =>
        (∑ n ∈ Finset.Icc 2 R, F (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
      Filter.atTop (nhds (∫ u in (0:ℝ)..1, F u)) := by
  sorry

end WMertens
