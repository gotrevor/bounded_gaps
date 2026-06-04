import Mathlib

open Filter Topology MeasureTheory
open scoped BigOperators

/-!
# 3-D pointwise scale-change limit (the sole remaining nut of the GPY 3-D simplex Riemann sum)

This is the LAST piece of `WeightedRiemann3D` in the `bounded_gaps` repo. The full 3-D coupled
log-weighted Riemann sum has been reduced (in-kernel, axiom-clean) to this single POINTWISE limit via
a Pólya monotone-to-continuous upgrade. Proving it discharges the whole 3-D simplex main term.

## The target
For fixed `t ∈ [0,1]` and continuous `G, H`, the `t`-scaled inner 2-D log-weighted Riemann sum
`Psi3 G H R t` converges to the 2-D simplex integral `Phi2 G H (1-t) = ∫_{u+v ≤ t, u,v ≥ 0} G(u)H(v)`.

## The proof strategy (MIRROR the 1-D case, one dimension up)
The 1-D analogue `Psi G R t → ∫₀^t G` is proven in the repo by: rescale `F̃(u) := G(t·u)`, set
`N(R) := ⌊R^t⌋` (so `N → ∞`) and `c_R := log N / log R → t`; feed `F̃` into the 1-D weighted Mertens
limit at level `N`; absorb the `c_R → t` argument drift by uniform continuity (the difference
`G(log n/log R) − F̃(log n/log N)` is uniformly small, times a bounded harmonic sum); finally
`Psi G R t = c_R · (sum/log N) → t · ∫₀¹ F̃ = ∫₀^t G`.

Here it is IDENTICAL one dimension up. Rescale `F̃(u) := G(t·u)`, `G̃(v) := H(t·v)`,
`N(R) := ⌊R^t⌋`, `c_R := log N/log R → t`:
1. **2-D Riemann at level N** — feed `F̃, G̃` into `weighted_riemann_2d` (PROVIDED below as `axiom
   weighted_riemann_2d`; it is genuinely proven in the repo, so you may use it freely):
   `(∑_{m≤N}∑_{n≤N/m} F̃(log m/log N)·G̃(log n/log N)/(mn))/(log N)² → ∫₀¹ F̃(x)·∫₀^{1-x} G̃`.
2. **Drift → 0** — the difference between the real summand `G(log m/log R)·H(log n/log R)` and
   `F̃(log m/log N)·G̃(log n/log N)` is `O(ε)` uniformly (uniform continuity of `G,H` on `[0,1]`,
   `|c_R − t| → 0`, and `|G(c u)H(c v) − G(t u)H(t v)| ≤ |G|·|H(cv)−H(tv)| + |H|·|G(cu)−G(tu)|`),
   times the bounded 2-D harmonic sum `(∑∑ 1/(mn))/(log N)²` (bounded since it converges, by
   `weighted_riemann_2d` with `F = G = 1`).
3. **Reassemble** — `Psi3 G H R t = c_R² · (realSum/log N²)`, and `realSum/log N² → ∫₀¹ F̃·∫ G̃`
   (step 1 + step 2), so `Psi3 → t² · ∫₀¹ F̃(x)∫₀^{1-x} G̃`.
4. **Change of variables** — `t² · ∫₀¹ G(t x)∫₀^{1-x} H(t y) dy dx = ∫₀^t G(u)∫₀^{t-u} H(v) dv du
   = Phi2 G H (1-t)` (two nested linear substitutions `u = t x`, `v = t y`; use
   `intervalIntegral.mul_integral_comp_mul_left` / `integral_comp_mul_left`, `t ≠ 0`).

The `t = 0` case is trivial: `⌊R^0⌋ = 1`, so the sum is empty `= 0`, and `Phi2 G H 1 = 0`.

Keep `#print axioms` clean apart from the supplied `weighted_riemann_2d` (no `sorry`).
-/

namespace AristotlePsi3

/-- `Φ_H(w) = ∫₀^{1-w} H`. -/
noncomputable def Phi (H : ℝ → ℝ) (w : ℝ) : ℝ := ∫ y in (0 : ℝ)..(1 - w), H y

/-- `Φ₂(s) = ∫₀^{1-s} G(y)·Φ_H(s+y) dy = ∫_{y,z ≥ 0, y+z ≤ 1-s} G(y)H(z)`. -/
noncomputable def Phi2 (G H : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(1 - s), G y * Phi H (s + y)

/-- The inner 2-D sum reparametrised by `t` (outer truncation `⌊R^t⌋`), normalised by `(log R)²`. -/
noncomputable def Psi3 (G H : ℝ → ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ t⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ t⌋₊ / m),
      G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
    / (Real.log R) ^ 2

/-- **PROVIDED (proven in the repo `BoundedGaps.InnerUniformReduction`).** The 2-D coupled
log-weighted Riemann sum converges to the iterated simplex integral. Use it freely. -/
axiom weighted_riemann_2d (F G : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
            F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log R) ^ 2)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * ∫ y in (0 : ℝ)..(1 - x), G y))

/-- **3-D pointwise scale-change limit.** For fixed `t ∈ [0,1]` and continuous `G, H`, the `t`-scaled
inner 2-D log-weighted Riemann sum converges to the 2-D simplex integral `Φ₂(1-t)`. -/
theorem psi3_pointwise (G H : ℝ → ℝ)
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => Psi3 G H R t) atTop (nhds (Phi2 G H (1 - t))) := by
  sorry

end AristotlePsi3
