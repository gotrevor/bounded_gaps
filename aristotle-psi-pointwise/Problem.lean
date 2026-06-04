import Mathlib

open Filter Topology MeasureTheory
open scoped BigOperators

/-!
# Pointwise scale-change limit for the GPY/Maynard inner Riemann sum.

In the main project the inner-UNIFORM convergence has been REDUCED (axiom-clean, via Pólya's
theorem) to the single POINTWISE limit below. Proving it closes the last analytic gap of the
GPY/Maynard 2-D simplex main term (`weighted_riemann_2d`).

`Ψ G R t = (∑_{n=2}^{⌊R^t⌋} G(log n/log R)/n)/log R`. For fixed `t ∈ [0,1]` and continuous `G`,
`Ψ G R t → ∫₀^t G` as `R → ∞`. This is the classical "fixed-`m` scale change".

The 1-D limit `riemann_sum_log_weight` (PROVED & axiom-clean in the main project) is supplied below
as a usable axiom; use it freely.

## Proof sketch (one standard route)
* `t = 0`: `⌊R^0⌋ = 1`, the sum over `Finset.Icc 2 1` is empty `= 0`, and `∫₀^0 G = 0`. Trivial.
* `t ∈ (0,1]`: set `N = ⌊R^t⌋` (so `N → ∞`) and `c_R = log N / log R`. Then `c_R → t`
  (since `N = ⌊R^t⌋` gives `log N = t·log R + log(N/R^t)` with `N/R^t → 1`, so `log(N/R^t)/log R → 0`).
  Rewrite the summand `G(log n/log R) = G(c_R · (log n/log N))`. By uniform continuity of `G` on the
  compact `[0,1]`, `sup_n |G(c_R·u) − G(t·u)| → 0` (as `c_R → t`, with `u = log n/log N ∈ [0,1]`),
  and `(∑_{n≤N} 1/n)/log N` is bounded; so the sum with the drifting argument `c_R` and the one with
  the fixed `t` have the same limit. Apply `riemann_sum_log_weight` to `F_t(u) = G(t·u)` (continuous,
  maps `[0,1]→[0,t]⊆[0,1]`): `(∑_{n≤N} F_t(log n/log N)/n)/log N → ∫₀¹ G(t·u) du`. Finally
  `Ψ G R t = [(∑_{n≤N} G(c_R·…)/n)/log N] · c_R → (∫₀¹ G(t·u)du)·t = ∫₀^t G` (substitute `y = t·u`).

Prove the `sorry`. Keep `#print axioms` free of `sorry`.
-/

namespace PsiPointwise

/-- 1-D log-weighted Riemann limit (PROVED & axiom-clean in the main project; use freely). -/
axiom riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, F (Real.log n / Real.log N) / (n : ℝ)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u))

/-- The inner Riemann partial sum truncated at `⌊R^t⌋`, normalized by `log R`. -/
noncomputable def Psi (G : ℝ → ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 ⌊(R : ℝ) ^ t⌋₊, G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R

/-- **Pointwise scale-change limit.** For `G` continuous on `[0,1]` and fixed `t ∈ [0,1]`,
`Ψ G R t → ∫₀^t G` as `R → ∞`. -/
theorem psi_tendsto (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => Psi G R t) atTop (nhds (∫ y in (0 : ℝ)..t, G y)) := by
  sorry

end PsiPointwise
