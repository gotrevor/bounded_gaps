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

/-- **k-D general finite-separable FTC bridge.** For the actual sieve test function shape
`F = ∑_j c_j ∏_i Fs_{j,i}`, feeding `selberg_nu` the per-coordinate antiderivatives and forming the
mixed partials recovers `F`, so the Rayleigh denominator is unchanged:
`∫_{simplex k} (∑_j c_j ∏_i 𝔉_{j,i}'(tᵢ))² = mkF_denominator k (∑_j c_j ∏_i Fs_{j,i})`. This is the
denominator identity behind the antiderivative convention at the `s1` axiom's `hFdecomp` shape; the
right-hand side is the limit of `S1MainTermDecomp.s1_yr_mainTerm_eq_mkF_denominator_decomp`. -/
theorem mkF_denominator_antideriv_decomp (k J : ℕ) (c : Fin J → ℝ) (Fs : Fin J → Fin k → ℝ → ℝ)
    (hFs : ∀ j i, Continuous (Fs j i)) :
    (∫ t in Sieve.simplex k, (∑ j, c j * ∏ i, deriv (antideriv (Fs j i)) (t i)) ^ 2)
      = Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) := by
  rw [show Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i))
        = ∫ t in Sieve.simplex k, (∑ j, c j * ∏ i, Fs j i (t i)) ^ 2 from rfl]
  refine MeasureTheory.setIntegral_congr_fun (Sieve.isClosed_simplex k).measurableSet
    (fun t _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [deriv_antideriv (hFs j i)]

/-- **Support viability of the antiderivative convention.** The convention feeds the sieve weight
`lambdaTransform`/`selberg_nu` the antiderivative `𝔉 = antideriv F`, and the sieve's level-`R` cutoff
relies on the fed test function vanishing outside `[0,1]` (so `𝔉(log d/log R) = 0` for `d > R`). A
general antiderivative `∫₀ˣ F` is *constant* `= ∫₀¹F` for `x ≥ 1`, hence not compactly supported —
**unless** `∫₀¹F = 0`. That moment condition is automatic in Maynard's actual convention, where the
variational `F` is the sieve weight `f` *differentiated* (§6 final remark): if `F = f'` with `f`
vanishing outside `(0,1)` then `∫₀¹F = f(1) − f(0) = 0` and `antideriv F = f` is again `[0,1]`-supported.
This lemma records the precise sufficient condition: `F` vanishing on `(−∞,0]` and `[1,∞)` together with
`∫₀¹F = 0` forces `antideriv F` to vanish outside `(0,1)`. -/
theorem antideriv_eq_zero_of_vanishing {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ t, t ≤ 0 → F t = 0) (hF1 : ∀ t, 1 ≤ t → F t = 0)
    (hF_int : ∫ t in (0:ℝ)..1, F t = 0) :
    ∀ x, x ≤ 0 ∨ 1 ≤ x → antideriv F x = 0 := by
  intro x hx
  unfold antideriv
  rcases hx with hx | hx
  · have heq : Set.EqOn F (fun _ => (0:ℝ)) (Set.uIcc 0 x) := by
      intro t ht
      rw [Set.uIcc_of_ge hx] at ht
      exact hF0 t ht.2
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  · have heq : Set.EqOn F (fun _ => (0:ℝ)) (Set.uIcc 1 x) := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact hF1 t ht.1
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable 0 1) (hF.intervalIntegrable 1 x),
      hF_int, zero_add, intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

/-- **`antideriv F` is `[0,1]`-supported** under the moment/vanishing conditions of
`antideriv_eq_zero_of_vanishing` — so the antiderivative-fed sieve weight keeps the level-`R` cutoff
(`𝔉(log d/log R) = 0` for `d > R`). -/
theorem antideriv_support_subset {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ t, t ≤ 0 → F t = 0) (hF1 : ∀ t, 1 ≤ t → F t = 0)
    (hF_int : ∫ t in (0:ℝ)..1, F t = 0) :
    Function.support (antideriv F) ⊆ Set.Icc 0 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  exact hx (antideriv_eq_zero_of_vanishing hF hF0 hF1 hF_int x
    (by rcases hmem with h | h
        · exact Or.inl h.le
        · exact Or.inr h.le))

end BoundedGaps.Antiderivative
