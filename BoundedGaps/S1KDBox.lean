/-
# The k-D box-product `s1` main term → `(φW/W)^k·mkF_denominator` (contour-free)

This assembles the per-coordinate 1-D Path-Y bilinear quadratic forms into the full k-dimensional
`s1` heuristic main term for the **separable** y-space sieve, landing on the Maynard Rayleigh
denominator.

For a finite-separable simplex-supported test function `F = ∑_j c_j ∏_i Fs_{j,i}` (with
`Fs ∈ ContDiff ℝ 1`), opening the square of the separable sieve weight gives `(j,j')` blocks, each a
product over coordinates of the 1-D Selberg bilinear form `quadForm W Fs_{j,i} Fs_{j',i} N`. The
contour-free assembly:

* each coordinate factor `quadForm W Fs_{j,i} Fs_{j',i} N / log N → (φW/W)·∫₀¹ Fs_{j,i}·Fs_{j',i}`
  (`S1YSpace.yspace_sieve_quadform_bilinear_tendsto`, conditional only on the W-coprime base `hBaseW`);
* the product over the `k` coordinates converges to the product of limits (`tendsto_finset_prod`),
  pulling out `(φW/W)^k`;
* the `(j,j')` double sum converges (`tendsto_finset_sum`);
* the resulting box constant `∑_{j,j'} c_j c_{j'} ∏_i ∫₀¹ Fs_{j,i}·Fs_{j',i}` equals the *simplex*
  denominator `mkF_denominator k F` (`S1BoxSimplex.box_product_eq_mkF_denominator`, using `F`'s
  simplex support).

Result (`yspace_kd_box_product_tendsto`):

    (∑_{j,j'} c_j c_{j'} ∏_i quadForm W Fs_{j,i} Fs_{j',i} N) / (log N)^k
      → (φW/W)^k · mkF_denominator k F.

No PNT, no contour. This is the complete contour-free `s1` MAIN-TERM limit for the separable y-space
sieve, in the clean index set `R_N = {r ≤ N : sf ∧ (r,W)=1}`. (Connecting the literal `sieveSum` to
this product form via the lattice count `M` is the separate, BV-gated count→`M` obligation; and the
`(φW/W)^k` singular-series factor is absorbed into the sieve normalisation `B^{-k}`.)
-/
import BoundedGaps.S1YSpace
import BoundedGaps.S1BoxSimplex

open MeasureTheory Filter Topology
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1KDBox

/-- The 1-D y-space Selberg bilinear quadratic form over `R_N = {r ≤ N : sf ∧ (r,W)=1}`:
`∑_{d,e∈R_N} λ^{F₁}_d λ^{F₂}_e / [d,e]` with `λ = S1YSpace.yLambda R_N · (log N)`. -/
noncomputable def quadForm (W : ℕ) (F₁ F₂ : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
    ∑ e ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
      S1YSpace.yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
          F₁ (Real.log N) d
        * S1YSpace.yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
          F₂ (Real.log N) e
        / (Nat.lcm d e : ℝ)

/-- `∫ u in 0..1, g = ∫ x in Set.Icc 0 1, g`: the interval integral on `[0,1]` is the set integral
over `Icc 0 1` (`uIoc 0 1 = Ioc 0 1`, and `Icc`/`Ioc` agree up to the null endpoint). Reconciles the
interval-integral limit of the y-space tendsto with the box (set-integral) form of the bridge. -/
theorem intervalIntegral_eq_setIntegral_Icc (g : ℝ → ℝ) :
    (∫ u in (0:ℝ)..1, g u) = ∫ x in Set.Icc (0:ℝ) 1, g x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc,
      Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), if_pos (by norm_num : (0:ℝ) ≤ 1), one_smul]

/-- Thin wrapper: `quadForm W F₁ F₂ N / log N → (φW/W)·∫₀¹F₁F₂` (= the existing bilinear tendsto with
the `quadForm` def folded). -/
theorem quadForm_div_log_tendsto {W : ℕ} {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ContDiff ℝ 1 F₁) (hF₂ : ContDiff ℝ 1 F₂)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto (fun N : ℕ => quadForm W F₁ F₂ N / Real.log N) atTop
      (nhds ((W.totient : ℝ) / W * ∫ u in (0 : ℝ)..1, F₁ u * F₂ u)) :=
  S1YSpace.yspace_sieve_quadform_bilinear_tendsto hF₁ hF₂ hBaseW

/-- **k-D box-product `s1` main term → `(φW/W)^k·mkF_denominator`** (axiom-clean, mod `hBaseW`). For
`F = ∑_j c_j ∏_i Fs_{j,i}` simplex-supported with `Fs ∈ ContDiff ℝ 1`, the product over coordinates
of the 1-D y-space bilinear forms, summed over `(j,j')` and normalised by `(log N)^k`, converges to
`(φW/W)^k · ∫_{simplex} F²`. Each coordinate factor `→ (φW/W)∫Fs_{j,i}Fs_{j',i}`
(`quadForm_div_log_tendsto`); the product over `i` (`tendsto_finset_prod`), the `(j,j')` sum
(`tendsto_finset_sum`), and the box→simplex bridge (`box_product_eq_mkF_denominator`) assemble it.
-/
theorem yspace_kd_box_product_tendsto {k J : ℕ} {W : ℕ} (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (hFs : ∀ j i, ContDiff ℝ 1 (Fs j i))
    (hsupp : Function.support (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) ⊆ Sieve.simplex k)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto (fun N : ℕ =>
        (∑ j, ∑ j', c j * c j' * ∏ i, quadForm W (Fs j i) (Fs j' i) N) / (Real.log N) ^ k)
      atTop (nhds (((W.totient : ℝ) / W) ^ k * Sieve.mkF_denominator k
        (fun t => ∑ j, c j * ∏ i, Fs j i (t i)))) := by
  -- per-(j,j') coordinate product limit
  have hprod : ∀ j j' : Fin J, Tendsto
      (fun N : ℕ => ∏ i, (quadForm W (Fs j i) (Fs j' i) N / Real.log N)) atTop
      (nhds (∏ i : Fin k, (W.totient : ℝ) / W * ∫ u in (0:ℝ)..1, Fs j i u * Fs j' i u)) := by
    intro j j'
    exact tendsto_finset_prod _ (fun i _ =>
      quadForm_div_log_tendsto (hFs j i) (hFs j' i) hBaseW)
  -- pull out (φW/W)^k from the coordinate product, scale by c j c j'
  have hjj : ∀ j j' : Fin J, Tendsto
      (fun N : ℕ => c j * c j' * (∏ i, quadForm W (Fs j i) (Fs j' i) N) / (Real.log N) ^ k) atTop
      (nhds (c j * c j' * (((W.totient : ℝ) / W) ^ k
        * ∏ i : Fin k, ∫ u in (0:ℝ)..1, Fs j i u * Fs j' i u))) := by
    intro j j'
    have hlimeq : (∏ i : Fin k, (W.totient : ℝ) / W * ∫ u in (0:ℝ)..1, Fs j i u * Fs j' i u)
        = ((W.totient : ℝ) / W) ^ k * ∏ i : Fin k, ∫ u in (0:ℝ)..1, Fs j i u * Fs j' i u := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hfun :
        (fun N : ℕ => c j * c j' * (∏ i, quadForm W (Fs j i) (Fs j' i) N) / (Real.log N) ^ k)
        = (fun N : ℕ => c j * c j' * ∏ i, (quadForm W (Fs j i) (Fs j' i) N / Real.log N)) := by
      funext N
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hfun, ← hlimeq]
    exact ((hprod j j').const_mul (c j * c j'))
  -- distribute the /(log N)^k over the (j,j') double sum
  have hsumfun : (fun N : ℕ =>
      (∑ j, ∑ j', c j * c j' * ∏ i, quadForm W (Fs j i) (Fs j' i) N) / (Real.log N) ^ k)
      = (fun N : ℕ => ∑ j, ∑ j',
          c j * c j' * (∏ i, quadForm W (Fs j i) (Fs j' i) N) / (Real.log N) ^ k) := by
    funext N
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_div _ _ _)
  -- the limit value = (φW/W)^k · mkF_denominator via the box→simplex bridge
  have hval : (∑ j, ∑ j', c j * c j' * (((W.totient : ℝ) / W) ^ k
        * ∏ i : Fin k, ∫ u in (0:ℝ)..1, Fs j i u * Fs j' i u))
      = ((W.totient : ℝ) / W) ^ k * Sieve.mkF_denominator k
          (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) := by
    simp only [intervalIntegral_eq_setIntegral_Icc]
    rw [← S1BoxSimplex.box_product_eq_mkF_denominator c Fs
      (fun j i => (hFs j i).continuous) hsupp]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    ring
  rw [hsumfun, ← hval]
  exact tendsto_finset_sum _ (fun j _ => tendsto_finset_sum _ (fun j' _ => hjj j j'))

end BoundedGaps.S1KDBox
