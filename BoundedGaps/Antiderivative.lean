import BoundedGaps.Sieve

/-!
# The antiderivative operator and the FTC bridge `∫ 𝔉'² = ∫ F²`

Path-Y, build-order item (1) (Trevor's settled 2026-06-04 convention, see
`archive/findings/ON-LINE-FINDINGS-2026-06-04-gpy-diagonal-asymptotic.md`): the GPY/Maynard `s1`
asymptotic constant `c = ∫₀¹ F'(t)² dt` is a *derivative* (Polymath8b `c-def`), while our s1 axiom
advertises `α = ∫_{simplex} F²`. These reconcile by feeding `lambdaTransform`/`selberg_nu` the
**antiderivative** `𝔉` of the variational `F` (`𝔉' = F`), keeping the constant `∫F²` and the entire
`M_k`/witness layer untouched. Maynard's final §6 remark: *"our function `F` corresponds to `f`
differentiated with respect to each coordinate."*

This file provides that operator and the corresponding FTC bridge:
* `antideriv F x = ∫_0^x F` — the boundary antiderivative (`𝔉(0) = 0`);
* `hasDerivAt_antideriv` / `deriv_antideriv` — `𝔉' = F` for continuous `F` (FTC-1);
* `contDiff_antideriv` — `𝔉` is `C^∞` when `F` is (`contDiff_infty_iff_deriv`);
* `mkF_denominator_antideriv_sep` — the k-D separable FTC bridge: the mixed partial of the
  antiderivative-tensor is `F`, so `∫_{simplex} (∏ᵢ 𝔉ᵢ'(tᵢ))² = mkF_denominator k (∏ᵢ Fᵢ)`. This
  ties the antiderivative-fed separable sieve weight directly to the now-proven `s1` main term
  (`S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep`).
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace BoundedGaps.Antiderivative

/-- The boundary antiderivative `𝔉(x) = ∫_0^x F` (so `𝔉(0) = 0`, `𝔉' = F`). -/
noncomputable def antideriv (F : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, F t

@[simp] lemma antideriv_zero (F : ℝ → ℝ) : antideriv F 0 = 0 := by
  simp [antideriv]

/-- **FTC-1 for `antideriv`.** For continuous `F`, `antideriv F` has derivative `F x` at every `x`. -/
theorem hasDerivAt_antideriv {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ) :
    HasDerivAt (antideriv F) (F x) x :=
  intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
    hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt

/-- The derivative of `antideriv F` is `F` (pointwise) for continuous `F`. -/
@[simp] theorem deriv_antideriv {F : ℝ → ℝ} (hF : Continuous F) : deriv (antideriv F) = F := by
  funext x; exact (hasDerivAt_antideriv hF x).deriv

theorem differentiable_antideriv {F : ℝ → ℝ} (hF : Continuous F) :
    Differentiable ℝ (antideriv F) :=
  intervalIntegral.differentiable_integral_of_continuous hF

/-- **`antideriv` preserves `C^∞`.** If `F` is smooth, so is its antiderivative (its derivative is
`F`, which is smooth — `contDiff_infty_iff_deriv`). -/
theorem contDiff_antideriv {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (antideriv F) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨differentiable_antideriv hF.continuous, by rw [deriv_antideriv hF.continuous]; exact hF⟩

/-- **1-D FTC bridge.** `∫_{[0,1]} (𝔉')² = ∫_{[0,1]} F²` for `𝔉 = antideriv F`, `F` continuous —
the constant is unchanged by passing to the antiderivative-fed weight. -/
theorem ftc_bridge_one {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in Set.Icc (0:ℝ) 1, (deriv (antideriv F) x) ^ 2)
      = ∫ x in Set.Icc (0:ℝ) 1, (F x) ^ 2 := by
  rw [deriv_antideriv hF]

/-- **k-D separable FTC bridge.** Feeding `selberg_nu` the per-coordinate antiderivatives
`𝔉ᵢ = antideriv (Fsᵢ)` and forming the mixed partial recovers `∏ᵢ Fsᵢ`, so the Rayleigh denominator
is unchanged: `∫_{simplex k} (∏ᵢ 𝔉ᵢ'(tᵢ))² = mkF_denominator k (∏ᵢ Fsᵢ)`. The right-hand side is
exactly the limit of the now-proven `y_r`-space `s1` main term
(`S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep`). -/
theorem mkF_denominator_antideriv_sep (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (hFs : ∀ i, Continuous (Fs i)) :
    (∫ t in Sieve.simplex k, (∏ i, deriv (antideriv (Fs i)) (t i)) ^ 2)
      = Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)) := by
  rw [show Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i))
        = ∫ t in Sieve.simplex k, (∏ i, Fs i (t i)) ^ 2 from rfl]
  refine MeasureTheory.setIntegral_congr_fun (Sieve.isClosed_simplex k).measurableSet
    (fun t _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [deriv_antideriv (hFs i)]

end BoundedGaps.Antiderivative
