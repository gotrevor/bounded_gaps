import Mathlib

open Filter Topology MeasureTheory
open scoped BigOperators

/-!
# Inner uniform convergence — the clean core of the GPY/Maynard 2-D simplex limit.

The 2-D simplex weighted-Riemann limit `weighted_riemann_2d` has been REDUCED in the main project
(`BoundedGaps/WeightedRiemann2D.lean`, axiom-clean) to the single ingredient below via
`weighted_riemann_2d_of_inner` (outer assembly + `perturbed_riemann` already PROVED). What remains
is the *inner uniform convergence*: the inner log-sum, normalized by `log R`, converges to the
simplex partial integral `∫₀^{1-s} G` UNIFORMLY in the outer index `m ∈ [2,R]` (where
`s = log m/log R`).

The 1-D non-uniform limit is provided below as the usable axiom `riemann_sum_log_weight`
(already PROVED & axiom-clean in the main project). Prove the uniform-in-`m` version.

## Why uniform-in-`m` is the crux
For FIXED `m` the limit is a scale change: with `R' = ⌊R/m⌋`, `s = log m/log R`,
`inner/log R = (1-s)·(∑_{n≤R'} G((1-s)·log n/log R')/n)/log R' → (1-s)∫₀¹ G((1-s)u)du = ∫₀^{1-s} G`.
But as `R→∞` with `m` ranging up to `R`, `m` near `R` gives `R'=⌊R/m⌋` SMALL (not →∞), so the
pointwise Riemann approximation degrades. The saving grace: there `1-s` is near `0`, so BOTH the
sum and the integral `∫₀^{1-s} G` are `O(1-s)`-small, hence the error is uniformly controlled. A
clean way: split `m ∈ [2, R^{1-δ}]` (where `R'≥R^δ→∞`, uniform Riemann convergence by equicontinuity
of `u ↦ G((1-s)u)` over `s∈[0,1]` — `G` uniformly continuous on the compact `[0,1]`) and
`m ∈ (R^{1-δ}, R]` (where `1-s < δ`, so `|inner/log R| ≤ ‖G‖∞·δ + o(1)` and `|∫₀^{1-s}G| ≤ ‖G‖∞·δ`,
both `≤ ε/2` for `δ` small). Take `δ` from `ε`, then `R` large.

Prove the `sorry`. Keep `#print axioms` free of `sorry`.
-/

namespace InnerUniform

/-- 1-D weighted Mertens / log-weighted Riemann limit (PROVED & axiom-clean in the main
project; use freely). -/
axiom riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, F (Real.log n / Real.log N) / (n : ℝ)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u))

/-- **Inner uniform convergence.** For `G` continuous on `[0,1]`, the inner log-sum (normalized by
`log R`) converges to the simplex partial integral `∫₀^{1 - log m/log R} G` uniformly in
`m ∈ [2,R]`. This is the sole remaining ingredient of the GPY/Maynard 2-D simplex main term. -/
theorem inner_uniform (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
      |(∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R
        - ∫ y in (0 : ℝ)..(1 - Real.log m / Real.log R), G y| ≤ ε := by
  sorry

end InnerUniform
