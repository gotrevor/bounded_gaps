import BoundedGaps.InnerUniformReduction

/-!
# 3-D coupled log-weighted Riemann limit (GPY/Maynard simplex main term, next level).

The GPY/Maynard diagonal asymptotic needs the **`k`-dimensional** simplex-coupled weighted Riemann
sum: `∑_{n_1⋯n_k ≤ R} ∏ᵢ Fᵢ(log nᵢ/log R)/nᵢ`, normalized by `(log R)^k`, converges to the iterated
simplex integral `∫_{∑tᵢ≤1} ∏ᵢ Fᵢ`. The 1-D case is `WeightedMertens.riemann_sum_log_weight`; the
2-D case is `WeightedRiemann2D.weighted_riemann_2d` (proven). **This file is the 3-D level** — the
next inductive step toward the full `k`-D lift (sub-step (c) of the s1/s2 analytic core).

The construction mirrors the 2-D one EXACTLY, one dimension up:
- `Phi2 G H s = ∫₀^{1-s} G(y)·Φ_H(s+y) dy` — the 2-D *inner* simplex integral (the cross-section
  `{(y,z) : y,z ≥ 0, y+z ≤ 1-s}`), here written as a single `intervalIntegral` against the 1-D
  `Phi H`. Continuous everywhere (for continuous `G,H`) via the parametric-primitive theorem.
- `inner2D G H R l = (∑_{m≤R/l}∑_{n≤R/(l m)} G·H/(m n))/(log R)²` — the inner 2-D sum at outer level
  `l`, the `a R l` consumed by `perturbed_riemann`.
- `three_d_factor` — the 3-D sum factors over the outer variable `l` into
  `(∑_l F(log l/log R)·(inner2D R l)/l)/log R` (pure field algebra, mirrors `two_d_factor`).
- `weighted_riemann_3d_of_inner` — the capstone: the 3-D simplex limit GIVEN the **inner uniform**
  convergence `inner2D R l → Φ₂(log l/log R)` uniformly in `l ∈ [2,R]`. Combines `three_d_factor`
  with the SAME reusable `perturbed_riemann` (with `Φ := Φ₂`, `a := inner2D`).

**Net:** the deep 3-D nut is reduced to the *inner uniform 2-D statement* — exactly as the 2-D nut
was reduced to the inner uniform 1-D statement. That 2-D inner uniform claim is the one genuinely
new analytic ingredient (a 2-D Pólya / monotone-step upgrade of the pointwise 2-D scale change);
everything else is discharged here in-kernel. NO new axioms.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace BoundedGaps.WeightedRiemann3D

open BoundedGaps.WeightedRiemann2D (Phi perturbed_riemann)

/-- The 2-D *inner* simplex integral `Φ₂(s) = ∫₀^{1-s} G(y)·Φ_H(s+y) dy`. Since
`Φ_H(w) = ∫₀^{1-w} H`, this equals `∫_{y,z ≥ 0, y+z ≤ 1-s} G(y)H(z) dz dy`, the cross-section of the
3-simplex at outer coordinate `s`. It is the `Φ` fed to `perturbed_riemann` for the outer var. -/
noncomputable def Phi2 (G H : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(1 - s), G y * Phi H (s + y)

/-- The inner 2-D log-sum at outer level `l`, normalized by `(log R)²`: the `a R l` consumed by
`perturbed_riemann`. The truncations `m ≤ R/l`, `n ≤ R/(l·m)` encode `l·m·n ≤ R` (the simplex). -/
noncomputable def inner2D (G H : ℝ → ℝ) (R l : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
      G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
    / (Real.log R) ^ 2

/-- `Φ_H` is continuous on all of `ℝ` when `H` is continuous: it is the primitive of `H` (continuous
since `H` is interval-integrable on every compact) composed with the continuous `w ↦ 1 - w`. -/
lemma phi_continuous (H : ℝ → ℝ) (hH : Continuous H) : Continuous (Phi H) := by
  have hprim : Continuous (fun w : ℝ => ∫ y in (0 : ℝ)..w, H y) :=
    intervalIntegral.continuous_primitive (fun a b => hH.intervalIntegrable a b) 0
  exact hprim.comp (continuous_const.sub continuous_id)

/-- **`Φ₂` is continuous** (for continuous `G, H`). The integrand `(s,y) ↦ G(y)·Φ_H(s+y)` is jointly
continuous, so the parametric primitive `(s, b) ↦ ∫₀^b …` is continuous; compose with the continuous
`s ↦ (s, 1-s)`. -/
lemma phi2_continuous (G H : ℝ → ℝ) (hG : Continuous G) (hH : Continuous H) :
    Continuous (Phi2 G H) := by
  have hPhiH : Continuous (Phi H) := phi_continuous H hH
  have huncurry : Continuous (Function.uncurry (fun s y => G y * Phi H (s + y))) := by
    refine Continuous.mul ?_ ?_
    · exact hG.comp continuous_snd
    · exact hPhiH.comp (continuous_fst.add continuous_snd)
  have hpar : Continuous
      (fun p : ℝ × ℝ => ∫ y in (0 : ℝ)..p.2, (fun s y => G y * Phi H (s + y)) p.1 y) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (a₀ := (0 : ℝ)) huncurry
  exact hpar.comp (continuous_id.prodMk (continuous_const.sub continuous_id))

/-- **Factoring the 3-D log-weighted triple sum.** The `l·m·n ≤ R` triple sum, normalized by
`(log R)³`, equals the outer sum of `F(log l/log R)·(inner2D R l)/l` normalized by `log R`. Pure
field algebra (mirrors `two_d_factor`); holds unconditionally. -/
lemma three_d_factor (F G H : ℝ → ℝ) (R : ℕ) :
    (∑ l ∈ Finset.Icc 2 R, ∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
        F (Real.log l / Real.log R) * G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
          / ((l : ℝ) * (m : ℝ) * (n : ℝ)))
      / (Real.log R) ^ 3
    = (∑ l ∈ Finset.Icc 2 R,
        F (Real.log l / Real.log R) * inner2D G H R l / (l : ℝ)) / Real.log R := by
  have key : ∀ l ∈ Finset.Icc 2 R,
      (∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
          F (Real.log l / Real.log R) * G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
            / ((l : ℝ) * (m : ℝ) * (n : ℝ)))
      = F (Real.log l / Real.log R) / (l : ℝ)
          * (∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
                / ((m : ℝ) * (n : ℝ))) := by
    intro l _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have key2 : ∀ l ∈ Finset.Icc 2 R,
      F (Real.log l / Real.log R) * inner2D G H R l / (l : ℝ)
      = (F (Real.log l / Real.log R) / (l : ℝ)
          * (∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
                / ((m : ℝ) * (n : ℝ)))) / (Real.log R) ^ 2 := by
    intro l _
    unfold inner2D
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_congr rfl key2, ← Finset.sum_div]
  ring

/-- **GPY/Maynard 3-D simplex limit, modulo the inner uniform convergence.** Given that the inner
2-D log-sum converges to `Φ₂` uniformly in `l ∈ [2,R]` (the genuinely-hard analytic ingredient = the
2-D Pólya inner-uniform statement), the full 3-D coupled Riemann sum converges to the iterated
3-simplex integral `∫₀¹ F(x)·Φ₂(x) dx = ∫_{x+y+z≤1} F·G·H`. Reduces the deep 3-D nut to the
(cleaner, 2-D-shaped) inner uniform statement; combines `three_d_factor` + `perturbed_riemann`. NO
new axioms. -/
theorem weighted_riemann_3d_of_inner (F G H : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : Continuous G) (hH : Continuous H)
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ l ∈ Finset.Icc 2 R,
        |inner2D G H R l - Phi2 G H (Real.log l / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ =>
        (∑ l ∈ Finset.Icc 2 R, ∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
            F (Real.log l / Real.log R) * G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
              / ((l : ℝ) * (m : ℝ) * (n : ℝ))) / (Real.log R) ^ 3)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Phi2 G H x)) := by
  have hPhi2cont : ContinuousOn (Phi2 G H) (Set.Icc (0 : ℝ) 1) :=
    (phi2_continuous G H hG hH).continuousOn
  have hgoal := perturbed_riemann F (Phi2 G H) (inner2D G H) hF hPhi2cont huni
  rw [funext (fun R => three_d_factor F G H R)]
  exact hgoal

/-- **The 3-D limit is the iterated 3-simplex integral.** Unfolding `Φ₂` and `Φ_H`, the limit
`∫₀¹ F·Φ₂` of `weighted_riemann_3d_of_inner` is exactly `∫₀¹∫₀^{1-x}∫₀^{1-x-y} F(x)G(y)H(z)`, the
integral over the 3-simplex `{x,y,z ≥ 0, x+y+z ≤ 1}`. Confirms the analytic target is the genuine
GPY/Maynard simplex main term (the separable-`F` shadow of `mkF_denominator = ∫_{simplex} F²`). -/
lemma integral_F_phi2_eq_simplex (F G H : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..1, F x * Phi2 G H x)
      = ∫ x in (0 : ℝ)..1, F x
          * ∫ y in (0 : ℝ)..(1 - x), G y * ∫ z in (0 : ℝ)..(1 - x - y), H z := by
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Phi2, Phi]
  congr 1
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  have : (1 : ℝ) - (x + y) = 1 - x - y := by ring
  rw [this]

end BoundedGaps.WeightedRiemann3D
