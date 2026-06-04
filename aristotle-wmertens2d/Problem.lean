import Mathlib

open scoped BigOperators
open Filter Topology

/-!
# 2-D coupled (simplex-constrained) weighted Riemann sum — analytic core of the GPY
multidimensional main term (sub-step (c), k=2).

The 1-D weighted Mertens `(∑_{2≤n≤R} F(log n/log R)/n)/log R → ∫₀¹F` is DONE (machine-checked,
axiom-clean: `riemann_sum_log_weight` below, provided as an axiom you may use freely). The next
ingredient for the GPY/Maynard main term is its **2-D simplex-coupled** analogue: the double sum
over `m·n ≤ R` (equivalently `log m + log n ≤ log R`, the 2-simplex `{x+y ≤ 1}`), normalized by
`(log R)²`, converges to the iterated simplex integral.

Sanity check (F = G = 1): inner `∑_{n=2}^{⌊R/m⌋} 1/n ≈ log(R/m)`, outer
`∑_{m} (log R − log m)/m ≈ (log R)²/2`, so `/(log R)² → 1/2 = ∫₀¹(1−x)dx`. ✓

## Strategy hint
For each fixed `m` with `log m/log R = s ∈ [0,1)`, the inner sum
`(∑_{n=2}^{⌊R/m⌋} G(log n/log R)/n)` is a 1-D log-weighted Riemann sum whose sample points
`log n/log R` range over `[0, log(R/m)/log R] = [0, 1−s]`; dividing by `log R` it tends to
`∫₀^{1−s} G`. So the whole expression is an outer 1-D log-weighted Riemann sum (in `m`) of
`x ↦ F(x)·∫₀^{1−x} G`, tending to `∫₀¹ F(x)·(∫₀^{1−x} G(y) dy) dx`. Make the inner→integral
convergence uniform in `m` (uniform continuity of `G` on the compact `[0,1]`), then apply the
outer 1-D argument. Keep `#print axioms` free of `sorry`.
-/

namespace WMertens2D

/-- 1-D weighted Mertens (already proved & axiom-clean in the main project) — use freely. -/
axiom riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0:ℝ) 1)) :
    Tendsto
      (fun R : ℕ => (∑ n ∈ Finset.Icc 2 R, F (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
      atTop (nhds (∫ u in (0:ℝ)..1, F u))

/-- **2-D coupled weighted Riemann sum → iterated simplex integral.** For `F, G` continuous on
`[0,1]`,
`(∑_{m=2}^{R} ∑_{n=2}^{⌊R/m⌋} F(log m/log R)·G(log n/log R)/(m·n)) / (log R)²
   → ∫₀¹ F(x)·(∫₀^{1−x} G(y) dy) dx`. -/
theorem weighted_riemann_2d (F G : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0:ℝ) 1)) (hG : ContinuousOn G (Set.Icc (0:ℝ) 1)) :
    Tendsto
      (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
            F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log R) ^ 2)
      atTop (nhds (∫ x in (0:ℝ)..1, F x * ∫ y in (0:ℝ)..(1 - x), G y)) := by
  sorry

end WMertens2D
