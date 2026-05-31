/-
# Smooth cutoffs for the Maynard simplex.

Infrastructure for discharging `SievePolynomial.Mk_ge_polynomialMkF`
(`Sieve.Mk k ≥ Sieve.MkF k P.toFun` for a polynomial sieve weight `P`).

`Mk k = sSup (MkSet k)` ranges over **smooth functions supported on the
simplex**, but a polynomial has full support, so `MkF P.toFun ∉ MkSet k` and the
bound is *not* a bare `le_csSup`. The honest proof multiplies `P` by a smooth
cutoff `χ_n` that is `1` on the `n`-interior of the simplex and supported inside
it, then sends `n → ∞`: `MkF (χ_n · P) ∈ MkSet k` and `MkF (χ_n · P) → MkF P`
by dominated convergence, giving `sSup (MkSet k) ≥ MkF P`.

This file builds the cutoff `χ_n` and its core properties (smooth, `[0,1]`-valued,
supported in the simplex, `→ 1` on the interior). The convergence/assembly step
(two-layer dominated convergence on `mkF_numerator`/`mkF_denominator`, using
`Convex.μ_frontier = 0` for the interior-is-conull fact and
`MeasureTheory.tendsto_integral_of_dominated_convergence`) is the remaining work;
all required mathlib lemmas have been confirmed present (v4.29.1).
-/
import BoundedGaps.Sieve

namespace BoundedGaps.Sieve

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Explicit smooth cutoff for the `k`-simplex at scale `n`:
`χ_n(t) = (∏_i σ(n·t_i)) · σ(n·(1 - ∑_j t_j))` where `σ = Real.smoothTransition`.
Smooth, `[0,1]`-valued, supported in `simplex k`, and `→ 1` on the interior. -/
noncomputable def chi (k n : ℕ) (t : Fin k → ℝ) : ℝ :=
  (∏ i : Fin k, Real.smoothTransition (n * t i)) *
    Real.smoothTransition (n * (1 - ∑ j, t j))

lemma chi_nonneg (k n : ℕ) (t : Fin k → ℝ) : 0 ≤ chi k n t := by
  unfold chi
  exact mul_nonneg (Finset.prod_nonneg fun i _ => Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

lemma chi_le_one (k n : ℕ) (t : Fin k → ℝ) : chi k n t ≤ 1 := by
  unfold chi
  apply mul_le_one₀
  · exact Finset.prod_le_one (fun i _ => Real.smoothTransition.nonneg _)
      (fun i _ => Real.smoothTransition.le_one _)
  · exact Real.smoothTransition.nonneg _
  · exact Real.smoothTransition.le_one _

lemma chi_smooth (k n : ℕ) : ContDiff ℝ ∞ (chi k n) := by
  unfold chi
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_apply ℝ ℝ i))
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_const.sub
        (ContDiff.sum fun j _ => contDiff_apply ℝ ℝ j)))

/-- The cutoff is supported in the simplex: if `χ_n t ≠ 0` then `t ∈ simplex k`. -/
lemma chi_support_subset (k n : ℕ) : Function.support (chi k n) ⊆ simplex k := by
  intro t ht
  simp only [Function.mem_support, chi, ne_eq, mul_eq_zero, not_or,
    Finset.prod_eq_zero_iff, not_exists, not_and] at ht
  obtain ⟨hprod, hlast⟩ := ht
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨fun i => ?_, ?_⟩
  · by_contra hneg
    push_neg at hneg
    exact hprod i (Finset.mem_univ i)
      (Real.smoothTransition.zero_of_nonpos (by nlinarith))
  · by_contra hneg
    push_neg at hneg
    exact hlast (Real.smoothTransition.zero_of_nonpos (by nlinarith))

/-- On the interior of the simplex (all coordinates positive, sum `< 1`) the
cutoff is eventually `= 1` as `n → ∞`. -/
lemma chi_eventually_eq_one (k : ℕ) {t : Fin k → ℝ}
    (ht : ∀ i, 0 < t i) (hsum : ∑ j, t j < 1) :
    ∀ᶠ n : ℕ in atTop, chi k n t = 1 := by
  have key : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n * c := fun c hc =>
    (Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hslack : 0 < 1 - ∑ j, t j := by linarith
  have hall : ∀ᶠ n : ℕ in atTop, (∀ i, (1 : ℝ) ≤ n * t i) ∧ (1 : ℝ) ≤ n * (1 - ∑ j, t j) := by
    rw [eventually_and]
    exact ⟨eventually_all.2 fun i => key _ (ht i), key _ hslack⟩
  filter_upwards [hall] with n hn
  unfold chi
  rw [Real.smoothTransition.one_of_one_le hn.2, mul_one]
  exact Finset.prod_eq_one fun i _ => Real.smoothTransition.one_of_one_le (hn.1 i)

/-- Hence on the interior the cutoff tends to `1`. -/
lemma chi_tendsto_one (k : ℕ) {t : Fin k → ℝ}
    (ht : ∀ i, 0 < t i) (hsum : ∑ j, t j < 1) :
    Tendsto (fun n => chi k n t) atTop (𝓝 1) :=
  tendsto_const_nhds.congr'
    (Filter.EventuallyEq.symm
      (show (fun n => chi k n t) =ᶠ[atTop] fun _ => 1 from chi_eventually_eq_one k ht hsum))

end BoundedGaps.Sieve
