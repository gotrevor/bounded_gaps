/-
# The box→simplex bridge for the separable y-space `s1` main term (gap A4 analytic core)

The separable Path-Y sieve weight `selberg_nu_yr_sep` produces a **box-product** heuristic main
term `M·∏ᵢ ∑_{rᵢ}(μ²/φ)Fᵢ²` (`S1YSpace.yr_heuristic_main_eq_muphi`): the coordinate sums are
*independent*, so dividing by `(log R)^k` and taking limits gives the **box** constant
`(φ(W)/W)^k·∏ᵢ ∫₀¹ Fs_{j,i}·Fs_{j',i}` (each factor via `yspace_sieve_quadform_bilinear_tendsto`).

But the Maynard Rayleigh denominator is the **simplex** integral `mkF_denominator k F = ∫_{simplex} F²`.
These reconcile because the witness test function `F = ∑_j c_j ∏_i Fs_{j,i}` is supported on the
simplex, so `∫_{box} F² = ∫_{simplex} F²` — the off-simplex box terms vanish. Expanding the square and
using box Fubini turns `∫_{box} F²` into the box-product double sum. This file proves that bridge:

    box_product_eq_mkF_denominator :
      ∑_{j,j'} c_j c_{j'} ∏_i ∫₀¹ Fs_{j,i}·Fs_{j',i}  =  mkF_denominator k F.

Pure analysis — unconditional, no number theory, no BV. It is the analytic core of gap A4 (the
box→simplex assembly) and lands the separable-sieve box-product main term exactly on the constant the
`s1` axiom advertises. (The remaining gap A4 content — connecting the literal `sieveSum` to this
box-product via the lattice count `M` — is the separate, BV-gated count→`M` obligation.)
-/
import BoundedGaps.Sieve

open MeasureTheory Filter Topology
open scoped BigOperators

namespace BoundedGaps.S1BoxSimplex

/-- The Maynard simplex sits inside the unit box `[0,1]^k`: for `t` with `tᵢ ≥ 0` and `∑ tᵢ ≤ 1`,
each `tᵢ ≤ ∑ⱼ tⱼ ≤ 1`. -/
theorem simplex_subset_box {k : ℕ} :
    Sieve.simplex k ⊆ Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1) := by
  intro t ht
  obtain ⟨hnn, hsum⟩ := ht
  intro i _
  refine ⟨hnn i, ?_⟩
  calc t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    _ ≤ 1 := hsum

/-- **Box Fubini.** `∫_{[0,1]^k} ∏ᵢ gᵢ(tᵢ) = ∏ᵢ ∫₀¹ gᵢ`. The product Lebesgue measure on the box
factors through `Measure.restrict_pi_pi` + `integral_fintype_prod_eq_prod`. -/
theorem setIntegral_box_prod {k : ℕ} (g : Fin k → ℝ → ℝ) :
    (∫ x in Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1), ∏ i, g i (x i))
      = ∏ i, ∫ x in Set.Icc (0:ℝ) 1, g i x := by
  rw [show (∫ x in Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1), ∏ i, g i (x i))
        = ∫ x, ∏ i, g i (x i)
            ∂((Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).restrict
                (Set.univ.pi (fun _ => Set.Icc (0:ℝ) 1))) from rfl,
      MeasureTheory.Measure.restrict_pi_pi,
      MeasureTheory.integral_fintype_prod_eq_prod]

/-- **Box = simplex on `F²`** for `F` supported on the simplex: `mkF_denominator k F =
∫_{[0,1]^k} F²`. Both equal `∫ F²` over the whole space (`F²` vanishes off the simplex, hence also
off the larger box), via `setIntegral_eq_integral_of_forall_compl_eq_zero` twice. -/
theorem mkF_denominator_eq_box {k : ℕ} (F : (Fin k → ℝ) → ℝ)
    (hsupp : Function.support F ⊆ Sieve.simplex k) :
    Sieve.mkF_denominator k F
      = ∫ x in Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1), F x ^ 2 := by
  unfold Sieve.mkF_denominator
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Sieve.simplex k)
        (fun t ht => by
          have hF0 : F t = 0 := by
            by_contra h; exact ht (hsupp (Function.mem_support.mpr h))
          rw [hF0]; ring)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1))
        (fun t ht => by
          have ht2 : t ∉ Sieve.simplex k := fun hmem => ht (simplex_subset_box hmem)
          have hF0 : F t = 0 := by
            by_contra h; exact ht2 (hsupp (Function.mem_support.mpr h))
          rw [hF0]; ring)]

/-- **Box-product = `mkF_denominator`** (the box→simplex bridge, gap A4 analytic core). For
`F = ∑_j c_j ∏_i Fs_{j,i}` (continuous `Fs`) supported on the simplex, the per-coordinate box
products sum to the Maynard Rayleigh denominator:
`∑_{j,j'} c_j c_{j'} ∏_i ∫₀¹ Fs_{j,i}·Fs_{j',i} = ∫_{simplex} F²`. This is the constant the
separable y-space sieve's box-product main term (`S1YSpace.yr_heuristic_main_eq_muphi`) lands on
(each factor `→ (φW/W)∫Fs_{j,i}Fs_{j',i}` via `yspace_sieve_quadform_bilinear_tendsto`). -/
theorem box_product_eq_mkF_denominator {k J : ℕ} (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (hcont : ∀ j i, Continuous (Fs j i))
    (hsupp : Function.support (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) ⊆ Sieve.simplex k) :
    (∑ j, ∑ j', c j * c j' * ∏ i, ∫ x in Set.Icc (0:ℝ) 1, Fs j i x * Fs j' i x)
      = Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) := by
  rw [mkF_denominator_eq_box _ hsupp]
  set box := Set.univ.pi (fun _ : Fin k => Set.Icc (0:ℝ) 1) with hbox
  have hmeas : MeasurableSet box := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have cont_term : ∀ (j j' : Fin J),
      Continuous (fun t : Fin k → ℝ => c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) :=
    fun j j' => continuous_const.mul (continuous_finset_prod _
      (fun i _ => ((hcont j i).mul (hcont j' i)).comp (continuous_apply i)))
  have cont_inner : ∀ (j : Fin J),
      Continuous (fun t : Fin k → ℝ => ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) :=
    fun j => continuous_finset_sum _ (fun j' _ => cont_term j j')
  have hInt_term : ∀ (j j' : Fin J),
      IntegrableOn (fun t : Fin k → ℝ => c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) box :=
    fun j j' => (cont_term j j').continuousOn.integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hInt_inner : ∀ (j : Fin J),
      IntegrableOn
        (fun t : Fin k → ℝ => ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) box :=
    fun j => (cont_inner j).continuousOn.integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsq : ∀ t : Fin k → ℝ, (∑ j, c j * ∏ i, Fs j i (t i)) ^ 2
      = ∑ j, ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i)) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [Finset.prod_mul_distrib]; ring
  symm
  rw [MeasureTheory.setIntegral_congr_fun hmeas (fun t _ => hsq t),
      MeasureTheory.integral_finset_sum _ (fun j _ => hInt_inner j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [MeasureTheory.integral_finset_sum _ (fun j' _ => hInt_term j j')]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [MeasureTheory.integral_const_mul, hbox,
    setIntegral_box_prod (fun i => fun x => Fs j i x * Fs j' i x)]

end BoundedGaps.S1BoxSimplex
