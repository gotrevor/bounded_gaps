import BoundedGaps.WeightedMertens

/-!
# 2-D coupled log-weighted Riemann limit (GPY/Maynard simplex main term).

The multidimensional Selberg/GPY diagonal asymptotic (`s1_holds_from_nonprime_asym`, leaf 1) rests
on the **2-D simplex-coupled** generalization of the 1-D weighted Mertens limit
(`BoundedGaps.WeightedMertens.riemann_sum_log_weight`): the double sum over `m·n ≤ R`
(equivalently the simplex `log m + log n ≤ log R`), normalized by `(log R)²`, converges to the
iterated simplex integral `∫₀¹ F(x)·(∫₀^{1-x} G) dx`.

This file proves that limit **modulo a single, much cleaner ingredient** — the *inner uniform
convergence* `(∑_{n≤R/m} G(log n/log R)/n)/log R → Φ_G(log m/log R)` uniformly in `m ∈ [2,R]`
(`Φ_G(x) = ∫₀^{1-x} G`). Everything else is discharged in-kernel:
- `phi_continuousOn` — the simplex partial-integral `Φ_G` is continuous on `[0,1]`.
- `perturbed_riemann` — THE analytic core: a perturbed log-weighted Riemann limit. If `a R m → Φ`
  *uniformly in `m`*, the `a`-weighted log-sum has the same limit `∫₀¹ F·Φ` as the `Φ`-weighted
  one. Lifts the 1-D `riemann_sum_log_weight` to an `R`-dependent integrand via a `MAIN + ERROR`
  decomposition (error squeezed by the uniform bound × a bounded `‖F‖₁`-type sum).
- `two_d_factor` — the 2-D double sum factors over the outer variable into `perturbed_riemann`'s
  shape (`Finset.mul_sum` + `Finset.sum_div`, pure field algebra).
- `weighted_riemann_2d_of_inner` — the capstone: 2-D simplex limit GIVEN the inner uniform claim.

**Net:** the deep 2-D nut is reduced to the inner uniform statement — a 1-D-shaped, self-contained
problem (a far better Aristotle target than the monolithic 2-D sum). NO new axioms.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace BoundedGaps.WeightedRiemann2D

/-- The simplex partial-integral `Φ_G(x) = ∫₀^{1-x} G`. -/
noncomputable def Phi (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..(1 - x), G y

/-- `Φ_G` is continuous on `[0,1]`: the primitive of `G` (continuous since `G` is integrable on the
compact `[0,1]`) composed with the continuous `x ↦ 1-x`, which maps `[0,1]` into `[0,1]`. -/
lemma phi_continuousOn (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc 0 1)) :
    ContinuousOn (Phi G) (Set.Icc (0 : ℝ) 1) := by
  have hint : IntegrableOn G (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hG.integrableOn_compact isCompact_Icc
  have hprim : ContinuousOn (fun u => ∫ y in (0 : ℝ)..u, G y) (Set.Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval hint
    rwa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at this
  have hmap : Set.MapsTo (fun x => 1 - x) (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) := by
    intro x hx; simp only [Set.mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  exact hprim.comp (continuous_const.sub continuous_id).continuousOn hmap

/-- **Perturbed log-weighted Riemann limit.** If `a R m` converges to `Φ(log m/log R)`
*uniformly in `m ∈ [2,R]`* as `R → ∞`, then the `a`-weighted log-sum converges to the same integral
`∫₀¹ F·Φ` as the `Φ`-weighted one. This is the analytic core that lifts the 1-D
`riemann_sum_log_weight` to a perturbed (`R`-dependent) integrand. -/
theorem perturbed_riemann (F Φ : ℝ → ℝ) (a : ℕ → ℕ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
        |a R m - Φ (Real.log m / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, F (Real.log m / Real.log R) * a R m / (m : ℝ)) / Real.log R)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Φ x)) := by
  have hmain : Tendsto (fun R : ℕ =>
      (∑ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) / (m : ℝ)) / Real.log R)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Φ x)) :=
    BoundedGaps.WeightedMertens.riemann_sum_log_weight (fun x => F x * Φ x) (hF.mul hΦ)
  set A : ℝ := ∫ x in (0 : ℝ)..1, |F x| with hA
  have habsf : Tendsto (fun R : ℕ =>
      (∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ)) / Real.log R)
      atTop (nhds A) :=
    BoundedGaps.WeightedMertens.riemann_sum_log_weight (fun x => |F x|) hF.abs
  have hA0 : 0 ≤ A :=
    intervalIntegral.integral_nonneg zero_le_one (fun u _ => abs_nonneg _)
  have herr : Tendsto (fun R : ℕ =>
      (∑ m ∈ Finset.Icc 2 R, F (Real.log m / Real.log R) * a R m / (m : ℝ)) / Real.log R
        - (∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) / (m : ℝ)) / Real.log R)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hAp : (0 : ℝ) < A + 1 := by linarith
    set ε₀ : ℝ := ε / (2 * (A + 1)) with hε₀
    have hε₀p : 0 < ε₀ := by positivity
    have e2 : ∀ᶠ R : ℕ in atTop,
        (∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ)) / Real.log R < A + 1 := by
      have h1 : ∀ᶠ R : ℕ in atTop,
          |(∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ)) / Real.log R - A| < 1 :=
        habsf (Metric.ball_mem_nhds A one_pos)
      filter_upwards [h1] with R hR
      rw [abs_lt] at hR; linarith [hR.2]
    have e3 : ∀ᶠ R : ℕ in atTop, (2:ℕ) ≤ R := eventually_atTop.mpr ⟨2, fun n hn => hn⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((huni ε₀ hε₀p).and (e2.and e3))
    refine ⟨N, fun R hR => ?_⟩
    obtain ⟨hu, habs_lt, h2R⟩ := hN R hR
    have hRpos : (1:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 1 < R)
    have hlogR : 0 < Real.log R := Real.log_pos hRpos
    rw [Real.dist_eq, sub_zero]
    rw [div_sub_div_same, ← Finset.sum_sub_distrib]
    have hterm_eq : ∀ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R) * a R m / (m : ℝ)
          - F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) / (m : ℝ)
        = F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) / (m : ℝ) := by
      intro m _; ring
    rw [Finset.sum_congr rfl hterm_eq, abs_div, abs_of_pos hlogR]
    have hnum : |∑ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) / (m : ℝ)|
        ≤ ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ) := by
      calc |∑ m ∈ Finset.Icc 2 R,
              F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) / (m : ℝ)|
          ≤ ∑ m ∈ Finset.Icc 2 R,
              |F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) / (m : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 2 R, ε₀ * (|F (Real.log m / Real.log R)| / (m : ℝ)) := by
            refine Finset.sum_le_sum (fun m hm => ?_)
            have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
            have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
            rw [abs_div, abs_mul, abs_of_pos hmpos]
            have hrw : ε₀ * (|F (Real.log m / Real.log R)| / (m : ℝ))
                = |F (Real.log m / Real.log R)| * ε₀ / (m : ℝ) := by ring
            rw [hrw]
            gcongr
            exact hu m hm
        _ = ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ) := by
            rw [Finset.mul_sum]
    calc |∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) / (m : ℝ)|
            / Real.log R
        ≤ (ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ)) / Real.log R :=
          div_le_div_of_nonneg_right hnum hlogR.le
      _ = ε₀ * ((∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| / (m : ℝ)) / Real.log R) := by
          rw [mul_div_assoc]
      _ ≤ ε₀ * (A + 1) := by
          apply mul_le_mul_of_nonneg_left _ hε₀p.le
          exact le_of_lt habs_lt
      _ = ε / 2 := by rw [hε₀]; field_simp
      _ < ε := by linarith
  have hcomb := hmain.add herr
  rw [add_zero] at hcomb
  exact hcomb.congr (fun R => by ring)

/-- **Factoring the 2-D log-weighted double sum.** The `mn ≤ R` double sum, normalized by
`(log R)²`, equals the outer sum of `F(log m/log R)·(inner/log R)/m` normalized by `log R`,
where `inner = ∑_{n≤R/m} G(log n/log R)/n`. Pure field algebra; holds unconditionally. -/
lemma two_d_factor (F G : ℝ → ℝ) (R : ℕ) :
    (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
        F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
      / (Real.log R) ^ 2
    = (∑ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R)
          * ((∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
          / (m : ℝ)) / Real.log R := by
  have key : ∀ m ∈ Finset.Icc 2 R,
      (∑ n ∈ Finset.Icc 2 (R / m),
        F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
      = F (Real.log m / Real.log R) / (m : ℝ)
          * ∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ) := by
    intro m _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  have key2 : ∀ m ∈ Finset.Icc 2 R,
      F (Real.log m / Real.log R)
          * ((∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
          / (m : ℝ)
      = (F (Real.log m / Real.log R) / (m : ℝ)
          * ∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R := by
    intro m _; ring
  rw [Finset.sum_congr rfl key, Finset.sum_congr rfl key2, ← Finset.sum_div, div_div, ← pow_two]

/-- **GPY/Maynard 2-D simplex limit, modulo the inner uniform convergence.** Given that the inner
log-sum converges to `Phi G` uniformly in `m ∈ [2,R]` (the genuinely-hard analytic ingredient = the
in-flight Aristotle `weighted_riemann_2d` problem's inner claim), the full 2-D coupled Riemann sum
converges to the iterated simplex integral. Reduces the deep 2-D nut to the (cleaner, 1-D-shaped)
inner uniform statement; combines `two_d_factor` + `perturbed_riemann`. NO new axioms. -/
theorem weighted_riemann_2d_of_inner (F G : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
        |(∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R
          - Phi G (Real.log m / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
            F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log R) ^ 2)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * ∫ y in (0 : ℝ)..(1 - x), G y)) := by
  have hgoal := perturbed_riemann F (Phi G)
    (fun R m => (∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
    hF (phi_continuousOn G hG) huni
  rw [funext (fun R => two_d_factor F G R)]
  exact hgoal

/-- **Abstract-weight perturbed Riemann limit** (the reusable engine behind both the bare `1/n`
ladder and the `μ²/φ` `y_r`-space ladder). For a nonnegative per-term weight `w R m`, GIVEN the two
weighted 1-D limits — the main `(∑ F·Φ·w)/log R → ∫F·Φ` and the absolute majorant `(∑ |F|·w)/log R →
A` — and the uniform convergence `a R m → Φ(log m/log R)`, the `a`-weighted sum has the same limit
`∫F·Φ`. The error `∑ F·(a−Φ)·w` is squeezed by `ε₀·(A+1)`. This isolates the only weight-specific
inputs (the two 1-D limits) so the `μ²/φ` engine reuses `WeightedMertens.weighted_mertens` exactly
where the `1/n` engine uses `riemann_sum_log_weight`. -/
theorem perturbed_riemann_gen (F Φ : ℝ → ℝ) (a w : ℕ → ℕ → ℝ) (A : ℝ)
    (hw0 : ∀ R : ℕ, ∀ m ∈ Finset.Icc 2 R, 0 ≤ w R m)
    (hmain : Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) * w R m) / Real.log R)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Φ x)))
    (habsf : Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m) / Real.log R)
      atTop (nhds A))
    (hA0 : 0 ≤ A)
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
        |a R m - Φ (Real.log m / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, F (Real.log m / Real.log R) * a R m * w R m) / Real.log R)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Φ x)) := by
  have herr : Tendsto (fun R : ℕ =>
      (∑ m ∈ Finset.Icc 2 R, F (Real.log m / Real.log R) * a R m * w R m) / Real.log R
        - (∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) * w R m) / Real.log R)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hAp : (0 : ℝ) < A + 1 := by linarith
    set ε₀ : ℝ := ε / (2 * (A + 1)) with hε₀
    have hε₀p : 0 < ε₀ := by positivity
    have e2 : ∀ᶠ R : ℕ in atTop,
        (∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m) / Real.log R < A + 1 := by
      have h1 : ∀ᶠ R : ℕ in atTop,
          |(∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m) / Real.log R - A| < 1 :=
        habsf (Metric.ball_mem_nhds A one_pos)
      filter_upwards [h1] with R hR
      rw [abs_lt] at hR; linarith [hR.2]
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((huni ε₀ hε₀p).and (e2.and (eventually_ge_atTop 2)))
    refine ⟨N, fun R hR => ?_⟩
    obtain ⟨hu, habs_lt, h2R⟩ := hN R hR
    have hRpos : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
    have hlogR : 0 < Real.log R := Real.log_pos hRpos
    rw [Real.dist_eq, sub_zero, div_sub_div_same, ← Finset.sum_sub_distrib]
    have hterm_eq : ∀ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R) * a R m * w R m
          - F (Real.log m / Real.log R) * Φ (Real.log m / Real.log R) * w R m
        = F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) * w R m := by
      intro m _; ring
    rw [Finset.sum_congr rfl hterm_eq, abs_div, abs_of_pos hlogR]
    have hnum : |∑ m ∈ Finset.Icc 2 R,
        F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) * w R m|
        ≤ ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m := by
      calc |∑ m ∈ Finset.Icc 2 R,
              F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) * w R m|
          ≤ ∑ m ∈ Finset.Icc 2 R,
              |F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) * w R m| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 2 R, ε₀ * (|F (Real.log m / Real.log R)| * w R m) := by
            refine Finset.sum_le_sum (fun m hm => ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg (hw0 R m hm)]
            have hrw : ε₀ * (|F (Real.log m / Real.log R)| * w R m)
                = |F (Real.log m / Real.log R)| * ε₀ * w R m := by ring
            rw [hrw]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hu m hm) (abs_nonneg _)) (hw0 R m hm)
        _ = ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m := by
            rw [Finset.mul_sum]
    calc |∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * (a R m - Φ (Real.log m / Real.log R)) * w R m|
            / Real.log R
        ≤ (ε₀ * ∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m) / Real.log R :=
          div_le_div_of_nonneg_right hnum hlogR.le
      _ = ε₀ * ((∑ m ∈ Finset.Icc 2 R, |F (Real.log m / Real.log R)| * w R m) / Real.log R) := by
          rw [mul_div_assoc]
      _ ≤ ε₀ * (A + 1) := by
          apply mul_le_mul_of_nonneg_left _ hε₀p.le
          exact le_of_lt habs_lt
      _ = ε / 2 := by rw [hε₀]; field_simp
      _ < ε := by linarith
  have hcomb := hmain.add herr
  rw [add_zero] at hcomb
  exact hcomb.congr (fun R => by ring)

open BoundedGaps.WeightedMertens BoundedGaps.SingularSeries in
/-- **`(μ²/φ)`-weighted Mertens over `Icc 2`** (`y_r`-space, reordered to weight-on-the-right). Drops
the `n=1` term (`= G 0`, whose `/log N → 0`) from `WeightedMertens.weighted_mertens` (`Icc 1`). The
`Icc 2` form matches the `perturbed_riemann_gen` weight shape `… * w N m`. -/
theorem weighted_mertens_Icc2 {G : ℝ → ℝ} {M : ℝ}
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|)
    (hCont : ContinuousOn G (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ =>
        (∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) * gMoebiusSqTotient m) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, G u)) := by
  have hwm := weighted_mertens hLip hCont
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => G 0 / Real.log N) atTop (nhds 0) :=
    (tendsto_const_nhds (x := G 0)).div_atTop hlog
  have hcomb := hwm.sub hconst
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : gMoebiusSqTotient 1 * G (Real.log ((1 : ℕ) : ℝ) / Real.log N) = G 0 := by
    rw [gMoebiusSqTotient_apply]; simp
  have hcomm : (∑ m ∈ Finset.Icc 2 N, gMoebiusSqTotient m * G (Real.log m / Real.log N))
      = ∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) * gMoebiusSqTotient m :=
    Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [hins, Finset.sum_insert (by simp), h1, hcomm]
  ring

open BoundedGaps.WeightedMertens BoundedGaps.SingularSeries in
/-- **`(μ²/φ)`-weighted perturbed Riemann limit** (`y_r`-space engine — the `μ²/φ` analog of
`perturbed_riemann`). The weight `1/m` is replaced by `gMoebiusSqTotient m = μ²(m)/φ(m)`: if
`a R m → Φ(log m/log R)` uniformly, the `(μ²/φ)`-weighted `a`-sum converges to `∫₀¹ F·Φ`. Built from
`perturbed_riemann_gen` with the two weighted 1-D limits from `weighted_mertens_Icc2` (for `F·Φ` and
`|F|`). Requires `F, Φ` Lipschitz with nonnegative constants (the `weighted_mertens` discrepancy
hypothesis); satisfied by smooth GPY cutoffs. The 2-D/k-D `y_r`-space ladder mirrors the bare ladder
one cons up, replacing `perturbed_riemann` by this. -/
theorem perturbed_riemann_muphi (F Φ : ℝ → ℝ) (a : ℕ → ℕ → ℝ) {MF MΦ : ℝ}
    (hMF0 : 0 ≤ MF) (hMΦ0 : 0 ≤ MΦ)
    (hFLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ MF * |x - y|)
    (hΦLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |Φ x - Φ y| ≤ MΦ * |x - y|)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hΦ : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
        |a R m - Φ (Real.log m / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R,
            F (Real.log m / Real.log R) * a R m * gMoebiusSqTotient m) / Real.log R)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * Φ x)) := by
  obtain ⟨BF, hBF⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  obtain ⟨BΦ, hBΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ
  have hBF' : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x| ≤ BF := fun x hx => hBF x hx
  have hBΦ' : ∀ x ∈ Set.Icc (0 : ℝ) 1, |Φ x| ≤ BΦ := fun x hx => hBΦ x hx
  have hBF0 : 0 ≤ BF := le_trans (abs_nonneg _) (hBF' 0 ⟨le_refl _, zero_le_one⟩)
  -- `F·Φ` is Lipschitz on `[0,1]` with constant `BF·MΦ + MF·BΦ`.
  have hFΦLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x * Φ x - F y * Φ y| ≤ (BF * MΦ + MF * BΦ) * |x - y| := by
    intro x hx y hy
    have e1 : |F x| * |Φ x - Φ y| ≤ BF * (MΦ * |x - y|) :=
      mul_le_mul (hBF' x hx) (hΦLip x hx y hy) (abs_nonneg _) hBF0
    have e2 : |F x - F y| * |Φ y| ≤ (MF * |x - y|) * BΦ :=
      mul_le_mul (hFLip x hx y hy) (hBΦ' y hy) (abs_nonneg _) (mul_nonneg hMF0 (abs_nonneg _))
    calc |F x * Φ x - F y * Φ y|
        = |F x * (Φ x - Φ y) + (F x - F y) * Φ y| := by congr 1; ring
      _ ≤ |F x * (Φ x - Φ y)| + |(F x - F y) * Φ y| := abs_add_le _ _
      _ = |F x| * |Φ x - Φ y| + |F x - F y| * |Φ y| := by rw [abs_mul, abs_mul]
      _ ≤ BF * (MΦ * |x - y|) + (MF * |x - y|) * BΦ := add_le_add e1 e2
      _ = (BF * MΦ + MF * BΦ) * |x - y| := by ring
  have hw0 : ∀ R : ℕ, ∀ m ∈ Finset.Icc 2 R, 0 ≤ gMoebiusSqTotient m := by
    intro R m _
    rw [gMoebiusSqTotient_apply]; positivity
  refine perturbed_riemann_gen F Φ a (fun _ m => gMoebiusSqTotient m)
    (∫ u in (0 : ℝ)..1, |F u|) (fun R m hm => hw0 R m hm)
    ?_ ?_ (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)) huni
  · exact weighted_mertens_Icc2 (G := fun x => F x * Φ x) hFΦLip (hF.mul hΦ)
  · exact weighted_mertens_Icc2 (G := fun x => |F x|)
      (fun x hx y hy => (abs_abs_sub_abs_le_abs_sub (F x) (F y)).trans (hFLip x hx y hy)) hF.abs

end BoundedGaps.WeightedRiemann2D
