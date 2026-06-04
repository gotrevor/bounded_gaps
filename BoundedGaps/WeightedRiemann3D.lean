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

/-- **Change of variables for `Φ₂`.** `Φ₂(1-t) = t²·∫₀¹ G(t x)·(∫₀^{1-x} H(t y) dy) dx` for `t ≠ 0`.
Two nested linear substitutions `u = t x`, `v = t y` (via `mul_integral_comp_mul_left`); the `t²`
Jacobian matches the `(log R)²` vs `(log ⌊R^t⌋)² = t²(log R)²` normalisation mismatch in the
pointwise scale change. RHS = the limit of `weighted_riemann_2d` applied to `G(t·)`, `H(t·)`. -/
lemma phi2_scale (G H : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    Phi2 G H (1 - t)
      = t ^ 2 * ∫ x in (0 : ℝ)..1, G (t * x) * ∫ y in (0 : ℝ)..(1 - x), H (t * y) := by
  have hinner : ∀ x : ℝ,
      (∫ y in (0 : ℝ)..(1 - x), H (t * y)) = t⁻¹ * ∫ z in (0 : ℝ)..(t - t * x), H z := by
    intro x
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := H) (c := t) (a := (0 : ℝ)) (b := 1 - x)
    rw [mul_zero, show t * (1 - x) = t - t * x from by ring] at h
    rw [← h, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  have hLHS : Phi2 G H (1 - t)
      = ∫ y in (0 : ℝ)..t, G y * ∫ z in (0 : ℝ)..(t - y), H z := by
    simp only [Phi2, Phi]
    rw [show (1 : ℝ) - (1 - t) = t from by ring]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [show (1 : ℝ) - (1 - t + y) = t - y from by ring]
  rw [hLHS]
  have hA : (∫ x in (0 : ℝ)..1, G (t * x) * ∫ y in (0 : ℝ)..(1 - x), H (t * y))
      = t⁻¹ * ∫ x in (0 : ℝ)..1, G (t * x) * ∫ z in (0 : ℝ)..(t - t * x), H z := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [hinner x]; ring
  rw [hA, show t ^ 2 * (t⁻¹ * ∫ x in (0 : ℝ)..1, G (t * x) * ∫ z in (0 : ℝ)..(t - t * x), H z)
        = t * ∫ x in (0 : ℝ)..1, G (t * x) * ∫ z in (0 : ℝ)..(t - t * x), H z from by
      rw [← mul_assoc, pow_two, mul_assoc t t t⁻¹, mul_inv_cancel₀ ht, mul_one]]
  have hC := intervalIntegral.mul_integral_comp_mul_left
    (f := fun u => G u * ∫ z in (0 : ℝ)..(t - u), H z) (c := t) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hC
  rw [hC]

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

/-! ## Inner-uniform 2-D convergence via Pólya (reducing the 3-D nut to a pointwise limit)

Exactly mirroring `InnerUniformReduction` one dimension up: reparametrise `t = 1 - log l/log R` so
the outer truncation `R/l = ⌊R^t⌋` (`floor_rpow_one_sub`); the reparametrised inner 2-D sum `Psi3`
then a *monotone* (in `t`, for `G,H ≥ 0`) step function whose limit `Φ₂(1-t)` is continuous, so
`PolyaUniform.polya_uniform` upgrades the pointwise scale-change limit to the uniform `huni`
hypothesis of `weighted_riemann_3d_of_inner`. The single remaining analytic input is the *pointwise*
2-D scale change `Psi3 G H R t → Φ₂(1-t)` — the clean, isolated next target. -/

/-- The inner 2-D sum reparametrised by `t` (outer truncation `⌊R^t⌋`), normalised by `(log R)²`.
At `t = 1 - log l/log R` it equals `inner2D G H R l` (`psi3_reparam`). -/
noncomputable def Psi3 (G H : ℝ → ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ t⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ t⌋₊ / m),
      G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
    / (Real.log R) ^ 2

/-- **`Psi3` is monotone in `t`** (for `G,H ≥ 0`): as `t` grows `⌊R^t⌋` grows, so both
the outer `m`-range and each inner `n`-range grow, and all summands are `≥ 0`. Mirrors
`psi_monotoneOn` with the extra (inner) layer. -/
lemma psi3_monotoneOn (G H : ℝ → ℝ) (hG : ∀ x, 0 ≤ G x) (hH : ∀ x, 0 ≤ H x) (R : ℕ) :
    MonotoneOn (Psi3 G H R) (Set.Icc (0 : ℝ) 1) := by
  rcases Nat.lt_or_ge R 2 with hRlt | hR2
  · have hlog0 : Real.log (R : ℝ) = 0 := by interval_cases R <;> simp
    intro a _ b _ _; simp [Psi3, hlog0]
  · have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    have hlogpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    intro a _ b _ hab
    have hpow : (R : ℝ) ^ a ≤ (R : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hR1' hab
    have hfloor : ⌊(R : ℝ) ^ a⌋₊ ≤ ⌊(R : ℝ) ^ b⌋₊ := Nat.floor_mono hpow
    have hterm_nonneg : ∀ m n : ℕ,
        0 ≤ G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)) :=
      fun m n => div_nonneg (mul_nonneg (hG _) (hH _)) (by positivity)
    have hinner : ∀ m : ℕ,
        (∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ a⌋₊ / m),
            G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
        ≤ (∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ b⌋₊ / m),
            G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ))) :=
      fun m => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.div_le_div_right hfloor))
        (fun n _ _ => hterm_nonneg m n)
    have hnum :
        (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ a⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ a⌋₊ / m),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          ≤ (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ b⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ b⌋₊ / m),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ))) := by
      calc (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ a⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ a⌋₊ / m),
                G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
            ≤ (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ a⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ b⌋₊ / m),
                G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ))) :=
              Finset.sum_le_sum (fun m _ => hinner m)
        _ ≤ (∑ m ∈ Finset.Icc 2 ⌊(R : ℝ) ^ b⌋₊, ∑ n ∈ Finset.Icc 2 (⌊(R : ℝ) ^ b⌋₊ / m),
                G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ))) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hfloor)
                (fun m _ _ => Finset.sum_nonneg (fun n _ => hterm_nonneg m n))
    exact div_le_div_of_nonneg_right hnum (by positivity)

/-- **Reparametrisation:** at `t = 1 - log l/log R`, `Psi3 = inner2D`. Uses `floor_rpow_one_sub`
(`⌊R^t⌋ = R/l`) and `Nat.div_div_eq_div_mul` (`(R/l)/m = R/(l·m)`). -/
lemma psi3_reparam (G H : ℝ → ℝ) (R l : ℕ) (hR2 : 2 ≤ R) (hl1 : 1 ≤ l) :
    Psi3 G H R (1 - Real.log l / Real.log R) = inner2D G H R l := by
  unfold Psi3 inner2D
  rw [BoundedGaps.InnerUniformReduction.floor_rpow_one_sub R l hR2 hl1]
  simp only [Nat.div_div_eq_div_mul]

/-- **3-D inner-uniform convergence from the pointwise scale-change limit (`G,H ≥ 0` core).** Given
the pointwise limit `Psi3 G H R t → Φ₂(1-t)` for every `t ∈ [0,1]`, the inner 2-D sum converges to
`Φ₂(log l/log R)` UNIFORMLY in `l ∈ [2,R]` — exactly the `huni` hypothesis of
`weighted_riemann_3d_of_inner`. Pólya (monotone `Psi3` + continuous limit) + the `t = 1-log l/log R`
reparametrisation. This isolates the 3-D analytic nut to the pointwise statement. -/
theorem inner_uniform_3d_of_pointwise_nonneg (G H : ℝ → ℝ)
    (hG : ∀ x, 0 ≤ G x) (hH : ∀ x, 0 ≤ H x)
    (hGcont : Continuous G) (hHcont : Continuous H)
    (hptw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => Psi3 G H R t) atTop (𝓝 (Phi2 G H (1 - t)))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ l ∈ Finset.Icc 2 R,
      |inner2D G H R l - Phi2 G H (Real.log l / Real.log R)| ≤ ε := by
  have hΦcont : ContinuousOn (fun t => Phi2 G H (1 - t)) (Set.Icc (0 : ℝ) 1) :=
    ((phi2_continuous G H hGcont hHcont).comp
      (continuous_const.sub continuous_id)).continuousOn
  have hpoly := BoundedGaps.PolyaUniform.polya_uniform
    (fun t => Phi2 G H (1 - t)) (Psi3 G H) hΦcont
    (fun R => psi3_monotoneOn G H hG hH R) hptw
  intro ε hε
  filter_upwards [hpoly ε hε, eventually_ge_atTop 2] with R hR hR2 l hl
  obtain ⟨hl2, hlR⟩ := Finset.mem_Icc.mp hl
  have hl1 : 1 ≤ l := by omega
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR2)
  have hlogl_nonneg : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hl1)
  have hlogl_le : Real.log (l : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < l)) (by exact_mod_cast hlR)
  have htl_mem : (1 - Real.log l / Real.log R) ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : Real.log l / Real.log R ≤ 1 := by rw [div_le_one hlogRpos]; exact hlogl_le
    have h0 : 0 ≤ Real.log l / Real.log R := div_nonneg hlogl_nonneg hlogRpos.le
    exact ⟨by linarith, by linarith⟩
  have hreparam : Psi3 G H R (1 - Real.log l / Real.log R) = inner2D G H R l :=
    psi3_reparam G H R l hR2 hl1
  have hphi_eq : Phi2 G H (1 - (1 - Real.log l / Real.log R))
      = Phi2 G H (Real.log l / Real.log R) := by congr 1; ring
  have hb := hR (1 - Real.log l / Real.log R) htl_mem
  rw [hreparam, hphi_eq] at hb
  exact hb

set_option maxHeartbeats 1000000 in
open BoundedGaps.InnerUniformReduction (weighted_riemann_2d tendsto_logFloor_rpow_div) in
/-- **3-D pointwise scale-change limit.** For fixed `t ∈ [0,1]` and continuous `G, H`, the
`t`-scaled inner 2-D log-weighted Riemann sum `Psi3 G H R t` converges to the simplex integral
`Φ₂(1-t)`. Mirrors `InnerUniformReduction.psi_tendsto` one dimension up: rescale `Ft(u)=G(t·u)`,
`Gt(v)=H(t·v)`, `N(R)=⌊R^t⌋`, `c_R=log N/log R → t`; feed `Ft,Gt` into `weighted_riemann_2d` at
level `N`; absorb the `c_R→t` drift (product split + 2-D harmonic from `weighted_riemann_2d 1 1`);
reassemble
`Psi3 = c_R²·(realSum/log N²) → t²·∫₀¹Ft·∫Gt = Φ₂(1-t)` (`phi2_scale`). -/
theorem psi3_pointwise (G H : ℝ → ℝ)
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => Psi3 G H R t) atTop (nhds (Phi2 G H (1 - t))) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with hteq | htpos
  · -- `t = 0`: the sum is empty (`⌊R^0⌋ = 1`), and `Φ₂(1) = ∫₀^0 = 0`.
    rw [← hteq]
    have hzero : (fun R : ℕ => Psi3 G H R 0) = fun _ => 0 := by
      funext R
      simp only [Psi3, Real.rpow_zero, Nat.floor_one]
      rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from rfl]
      simp
    rw [hzero, show Phi2 G H (1 - 0) = 0 from by simp [Phi2, Phi]]
    exact tendsto_const_nhds
  · -- `t > 0`.
    set Ft : ℝ → ℝ := fun u => G (t * u) with hFt
    set Gt : ℝ → ℝ := fun v => H (t * v) with hGt
    have hmaps : Set.MapsTo (fun u => t * u) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
      intro u hu; obtain ⟨hu0, hu1⟩ := hu; exact ⟨by positivity, by nlinarith⟩
    have hFt_cont : ContinuousOn Ft (Set.Icc (0 : ℝ) 1) :=
      hG.comp ((continuous_const.mul continuous_id).continuousOn) hmaps
    have hGt_cont : ContinuousOn Gt (Set.Icc (0 : ℝ) 1) :=
      hH.comp ((continuous_const.mul continuous_id).continuousOn) hmaps
    set N : ℕ → ℕ := fun R => ⌊(R : ℝ) ^ t⌋₊ with hN
    have hNtop : Tendsto N atTop atTop := by
      have : Tendsto (fun R : ℕ => (R : ℝ) ^ t) atTop atTop :=
        (tendsto_rpow_atTop htpos).comp tendsto_natCast_atTop_atTop
      exact tendsto_nat_floor_atTop.comp this
    have hcR : Tendsto (fun R : ℕ => Real.log (N R : ℝ) / Real.log (R : ℝ)) atTop (𝓝 t) :=
      tendsto_logFloor_rpow_div t htpos
    -- 2-D Riemann at level `N` with the rescaled functions.
    have hriem : Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ))
              / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, Ft x * ∫ y in (0 : ℝ)..(1 - x), Gt y)) :=
      (weighted_riemann_2d Ft Gt hFt_cont hGt_cont).comp hNtop
    -- sup bounds for `G`, `H` on `[0,1]`.
    obtain ⟨MG, hMG⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
    obtain ⟨MH, hMH⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
    have hMG0 : 0 ≤ MG := le_trans (norm_nonneg _) (hMG 0 ⟨le_refl _, zero_le_one⟩)
    have hMH0 : 0 ≤ MH := le_trans (norm_nonneg _) (hMH 0 ⟨le_refl _, zero_le_one⟩)
    -- 2-D harmonic bound: eventually `≤ C` for some `C > 0` (C kept opaque via `obtain`).
    obtain ⟨C, hC0, hharm⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
        (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            (1 : ℝ) / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2 ≤ C := by
      set L : ℝ := ∫ x in (0 : ℝ)..1, (1 : ℝ) * ∫ _y in (0 : ℝ)..(1 - x), (1 : ℝ) with hL
      have hharm_lim : Tendsto (fun R : ℕ =>
          (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              (1 : ℝ) * (1 : ℝ) / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2) atTop (𝓝 L) :=
        (weighted_riemann_2d (fun _ => 1) (fun _ => 1) continuousOn_const
          continuousOn_const).comp hNtop
      refine ⟨|L| + 1, by positivity, ?_⟩
      have h1 := (Metric.tendsto_nhds.1 hharm_lim) 1 (by norm_num)
      filter_upwards [h1] with R hR
      rw [Real.dist_eq] at hR
      have heq : (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            (1 : ℝ) * (1 : ℝ) / ((m : ℝ) * (n : ℝ)))
          = (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            (1 : ℝ) / ((m : ℝ) * (n : ℝ))) := by simp
      rw [heq] at hR
      have h2 := (abs_lt.1 hR).2
      have h3 := le_abs_self L
      linarith
    -- drift → 0.
    have hdrift : Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            (G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
              - Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ)))
              / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2) atTop (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      have hMGH1 : (0 : ℝ) < MG + MH + 1 := by linarith [hMG0, hMH0]
      have hDpos : (0 : ℝ) < 2 * C * (MG + MH + 1) :=
        mul_pos (mul_pos (by norm_num) hC0) hMGH1
      set εpp : ℝ := ε / (2 * C * (MG + MH + 1)) with hεpp
      have hεpp0 : 0 < εpp := by rw [hεpp]; exact div_pos hε hDpos
      have hucG : UniformContinuousOn G (Set.Icc (0 : ℝ) 1) :=
        isCompact_Icc.uniformContinuousOn_of_continuous hG
      have hucH : UniformContinuousOn H (Set.Icc (0 : ℝ) 1) :=
        isCompact_Icc.uniformContinuousOn_of_continuous hH
      obtain ⟨δG, hδG0, hδG⟩ := Metric.uniformContinuousOn_iff_le.1 hucG εpp hεpp0
      obtain ⟨δH, hδH0, hδH⟩ := Metric.uniformContinuousOn_iff_le.1 hucH εpp hεpp0
      set δ : ℝ := min δG δH with hδ
      have hδ0 : 0 < δ := lt_min hδG0 hδH0
      have hcR' : ∀ᶠ R : ℕ in atTop, |Real.log (N R : ℝ) / Real.log (R : ℝ) - t| ≤ δ := by
        have := Metric.tendsto_nhds.1 hcR δ hδ0
        filter_upwards [this] with R hR; rw [Real.dist_eq] at hR; linarith
      filter_upwards [hcR', hharm, hNtop.eventually_ge_atTop 2, eventually_ge_atTop 2]
        with R hcRδ hharmR hNR2 hR2
      have hNR1 : (1 : ℝ) < (N R : ℝ) := by exact_mod_cast (by omega : 1 < N R)
      have hlogNRpos : 0 < Real.log (N R : ℝ) := Real.log_pos hNR1
      have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
      have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hR1
      have hNRleR : (N R : ℝ) ≤ (R : ℝ) := by
        have h1 : (N R : ℝ) ≤ (R : ℝ) ^ t := Nat.floor_le (by positivity)
        have h2 : (R : ℝ) ^ t ≤ (R : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1.le ht1
        rw [Real.rpow_one] at h2; linarith
      have hcR0' : 0 ≤ Real.log (N R : ℝ) / Real.log (R : ℝ) := by positivity
      have hcR1 : Real.log (N R : ℝ) / Real.log (R : ℝ) ≤ 1 := by
        rw [div_le_one hlogRpos]; exact Real.log_le_log (by positivity) hNRleR
      -- per-term drift bound.
      have hterm : ∀ m ∈ Finset.Icc 2 (N R), ∀ n ∈ Finset.Icc 2 (N R / m),
          |G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
            - Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ))|
            ≤ (MG + MH) * εpp := by
        intro m hm n hn
        rw [Finset.mem_Icc] at hm hn
        have hm2 : 2 ≤ m := hm.1; have hmNR : m ≤ N R := hm.2
        have hn2 : 2 ≤ n := hn.1
        have hnNR : n ≤ N R := le_trans hn.2 (Nat.div_le_self _ _)
        set um : ℝ := Real.log m / Real.log (N R : ℝ) with hum
        set vn : ℝ := Real.log n / Real.log (N R : ℝ) with hvn
        set cR : ℝ := Real.log (N R : ℝ) / Real.log (R : ℝ) with hcRdef
        have hum0 : 0 ≤ um := by rw [hum]; positivity
        have hum1 : um ≤ 1 := by
          rw [hum, div_le_one hlogNRpos]
          exact Real.log_le_log (by positivity) (by exact_mod_cast hmNR)
        have hvn0 : 0 ≤ vn := by rw [hvn]; positivity
        have hvn1 : vn ≤ 1 := by
          rw [hvn, div_le_one hlogNRpos]
          exact Real.log_le_log (by positivity) (by exact_mod_cast hnNR)
        -- arguments land in `[0,1]`.
        have hcum : cR * um ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul hcR1 hum1 hum0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        have htum : t * um ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul ht1 hum1 hum0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        have hcvn : cR * vn ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul hcR1 hvn1 hvn0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        have htvn : t * vn ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul ht1 hvn1 hvn0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        -- rewrite the log-ratios.
        have hrwm : Real.log (m : ℝ) / Real.log (R : ℝ) = cR * um := by
          rw [hcRdef, hum]; field_simp
        have hrwn : Real.log (n : ℝ) / Real.log (R : ℝ) = cR * vn := by
          rw [hcRdef, hvn]; field_simp
        have hFtval : Ft um = G (t * um) := rfl
        have hGtval : Gt vn = H (t * vn) := rfl
        -- distance bounds for the arguments.
        have hdistu : dist (cR * um) (t * um) ≤ δ := by
          rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg hum0]
          calc |cR - t| * um ≤ δ * 1 := mul_le_mul hcRδ hum1 hum0 hδ0.le
            _ = δ := by ring
        have hdistv : dist (cR * vn) (t * vn) ≤ δ := by
          rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg hvn0]
          calc |cR - t| * vn ≤ δ * 1 := mul_le_mul hcRδ hvn1 hvn0 hδ0.le
            _ = δ := by ring
        have hGdiff : |G (cR * um) - G (t * um)| ≤ εpp := by
          have := hδG _ hcum _ htum (le_trans hdistu (min_le_left _ _))
          rwa [Real.dist_eq] at this
        have hHdiff : |H (cR * vn) - H (t * vn)| ≤ εpp := by
          have := hδH _ hcvn _ htvn (le_trans hdistv (min_le_right _ _))
          rwa [Real.dist_eq] at this
        have hGbd : |G (cR * um)| ≤ MG := hMG _ hcum
        have hHbd : |H (t * vn)| ≤ MH := hMH _ htvn
        -- product split.
        rw [hrwm, hrwn, hFtval, hGtval]
        have hsplit : G (cR * um) * H (cR * vn) - G (t * um) * H (t * vn)
            = G (cR * um) * (H (cR * vn) - H (t * vn))
              + (G (cR * um) - G (t * um)) * H (t * vn) := by ring
        rw [hsplit]
        calc |G (cR * um) * (H (cR * vn) - H (t * vn)) + (G (cR * um) - G (t * um)) * H (t * vn)|
            ≤ |G (cR * um) * (H (cR * vn) - H (t * vn))|
                + |(G (cR * um) - G (t * um)) * H (t * vn)| := abs_add_le _ _
          _ = |G (cR * um)| * |H (cR * vn) - H (t * vn)|
                + |G (cR * um) - G (t * um)| * |H (t * vn)| := by rw [abs_mul, abs_mul]
          _ ≤ MG * εpp + εpp * MH := by
              apply add_le_add
              · exact mul_le_mul hGbd hHdiff (abs_nonneg _) hMG0
              · exact mul_le_mul hGdiff hHbd (abs_nonneg _) hεpp0.le
          _ = (MG + MH) * εpp := by ring
      -- assemble the drift sum bound.
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogNRpos 2),
        div_lt_iff₀ (pow_pos hlogNRpos 2)]
      have hsum_abs :
          |∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              (G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
                - Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ)))
                / ((m : ℝ) * (n : ℝ))|
            ≤ ((MG + MH) * εpp)
                * ∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
                    (1 : ℝ)/((m:ℝ)*(n:ℝ)) := by
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro m hm
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        have hmn0 : (0 : ℝ) < (m : ℝ) * (n : ℝ) := by
          have hm1 : 1 ≤ m := by rw [Finset.mem_Icc] at hm; omega
          have hn1 : 1 ≤ n := by rw [Finset.mem_Icc] at hn; omega
          positivity
        rw [abs_div, abs_of_pos hmn0,
          show ((MG + MH) * εpp) * ((1:ℝ)/((m:ℝ)*(n:ℝ)))
            = ((MG + MH) * εpp) / ((m:ℝ)*(n:ℝ)) from by ring]
        exact div_le_div_of_nonneg_right (hterm m hm n hn) (by positivity)
      have hlogNRsq : (0 : ℝ) < (Real.log (N R : ℝ)) ^ 2 := pow_pos hlogNRpos 2
      have hMGHnn : (0 : ℝ) ≤ MG + MH := by linarith [hMG0, hMH0]
      calc |∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              (G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
                - Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ)))
                / ((m : ℝ) * (n : ℝ))|
          ≤ ((MG + MH) * εpp)
              * ∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m), (1:ℝ)/((m:ℝ)*(n:ℝ)) :=
            hsum_abs
        _ ≤ ((MG + MH) * εpp) * (C * (Real.log (N R:ℝ))^2) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMGHnn hεpp0.le)
            exact (div_le_iff₀ hlogNRsq).1 hharmR
        _ = ((MG + MH) * εpp * C) * (Real.log (N R:ℝ))^2 := by ring
        _ < ε * (Real.log (N R:ℝ))^2 := by
            apply mul_lt_mul_of_pos_right _ hlogNRsq
            have hεppD : εpp * (2 * C * (MG + MH + 1)) = ε := by
              rw [hεpp]; exact div_mul_cancel₀ ε (ne_of_gt hDpos)
            rw [← hεppD]
            nlinarith [mul_pos hεpp0 hC0, hMG0, hMH0,
              mul_pos (mul_pos hεpp0 hC0) (by linarith [hMG0, hMH0] : (0:ℝ) < MG + MH + 2)]
    -- `realSum/log N² → ∫₀¹ Ft·∫ Gt`.
    have hBlim : Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
            G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log (N R : ℝ)) ^ 2) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, Ft x * ∫ y in (0 : ℝ)..(1 - x), Gt y)) := by
      have hsplit : (fun R : ℕ =>
          (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
            / (Real.log (N R : ℝ)) ^ 2)
          = (fun R : ℕ =>
              (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
                  Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ))
                    / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2
              + (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
                  (G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
                    - Ft (Real.log m / Real.log (N R : ℝ)) * Gt (Real.log n / Real.log (N R : ℝ)))
                    / ((m : ℝ) * (n : ℝ))) / (Real.log (N R : ℝ)) ^ 2) := by
        funext R
        rw [← add_div, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [← add_div]; congr 1; ring
      rw [hsplit]
      simpa using hriem.add hdrift
    -- `Psi3 = c_R² · (realSum/log N²)`.
    have hPsiEq : (fun R : ℕ => Psi3 G H R t) =ᶠ[atTop]
        (fun R : ℕ => (Real.log (N R : ℝ) / Real.log (R : ℝ)) ^ 2 *
          ((∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
            / (Real.log (N R : ℝ)) ^ 2)) := by
      filter_upwards [hNtop.eventually_ge_atTop 2, eventually_ge_atTop 2] with R hNR2 hR2
      have hlogNRne : Real.log (N R : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N R)))
      have hlogRne : Real.log (R : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < R)))
      show (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
          G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log (R : ℝ)) ^ 2
        = (Real.log (N R : ℝ) / Real.log (R : ℝ)) ^ 2 *
          ((∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
              G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
            / (Real.log (N R : ℝ)) ^ 2)
      set S := (∑ m ∈ Finset.Icc 2 (N R), ∑ n ∈ Finset.Icc 2 (N R / m),
          G (Real.log m / Real.log R) * H (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ))) with hS
      rw [div_pow]
      field_simp
    rw [tendsto_congr' hPsiEq]
    rw [phi2_scale G H (ne_of_gt htpos)]
    have hgoal := hcR.pow 2 |>.mul hBlim
    exact hgoal

/-- **GPY/Maynard 3-D simplex limit — UNCONDITIONAL (for `G,H ≥ 0`).** The fully-coupled triple
log-weighted Riemann sum over `l·m·n ≤ R` converges to the iterated 3-simplex integral
`∫₀¹ F·Φ₂ = ∫_{x+y+z≤1} F·G·H`. Chains the three in-kernel results: `psi3_pointwise` (the pointwise
scale change) ⟹ `inner_uniform_3d_of_pointwise_nonneg` (Pólya upgrade to inner-uniform) ⟹
`weighted_riemann_3d_of_inner` (the 3-D reduction). The 3-D level of the `k`-D weighted-Mertens
lift, done. (`G,H ≥ 0` powers the Pólya monotonicity; `F` only needs continuity.) -/
theorem weighted_riemann_3d (F G H : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : Continuous G) (hH : Continuous H)
    (hG0 : ∀ x, 0 ≤ G x) (hH0 : ∀ x, 0 ≤ H x) :
    Tendsto (fun R : ℕ =>
        (∑ l ∈ Finset.Icc 2 R, ∑ m ∈ Finset.Icc 2 (R / l), ∑ n ∈ Finset.Icc 2 (R / (l * m)),
            F (Real.log l / Real.log R) * G (Real.log m / Real.log R) * H (Real.log n / Real.log R)
              / ((l : ℝ) * (m : ℝ) * (n : ℝ))) / (Real.log R) ^ 3)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Phi2 G H x)) := by
  refine weighted_riemann_3d_of_inner F G H hF hG hH ?_
  refine inner_uniform_3d_of_pointwise_nonneg G H hG0 hH0 hG hH ?_
  intro t ht
  exact psi3_pointwise G H hG.continuousOn hH.continuousOn t ht

end BoundedGaps.WeightedRiemann3D
