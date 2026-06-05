import BoundedGaps.S1ConnectionK1
import BoundedGaps.WeightedRiemannSigned

/-!
# The `s1` Path-Y main term for the general finite-separable decomposition

`S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep` handles a single product `F = ∏ᵢ Fsᵢ`. The
actual GPY/Maynard sieve test function is a **finite separable sum** `F t = ∑_j c_j ∏_i Fs_{j,i}(t_i)`
(the box-tensor witnesses are genuinely general-`J`), and the `s1` quadratic form is `F²`, which
expands into **signed** cross terms `∏_i (Fs_{j,i}·Fs_{j',i})`.

This file proves the main term for that general decomposition, composing:
* `WeightedRiemannSigned.weighted_riemann_kd_muphi_signed` (the signed ladder — each cross-term
  product converges to its `nestedPhi`, with no nonnegativity needed);
* `S1Fubini.simplex_integral_prod_eq_nestedPhi` (the Fubini bridge — `nestedPhi = ∫_{simplex} ∏`);
* the algebraic square expansion `(∑_j c_j A_j)² = ∑_{j,j'} c_j c_{j'} A_j A_{j'}` and linearity of
  the integral over the finite double sum.

Result (`s1_yr_mainTerm_eq_mkF_denominator_decomp`): the `(μ²/φ)` `y_r`-space sum of the diagonalised
quadratic form converges to `mkF_denominator k F = ∫_{simplex k} F²` — exactly the analytic main term
the `s1` axiom advertises, in the `hFdecomp` shape.
-/

open MeasureTheory Filter Topology
open scoped BigOperators
open BoundedGaps.SingularSeries (gMoebiusSqTotient)
open BoundedGaps.WeightedRiemannKD (nestedPhi)
open BoundedGaps.WeightedRiemannGen (nestedLogSumW)
open BoundedGaps.WeightedRiemannSigned (weighted_riemann_kd_muphi_signed)

namespace BoundedGaps.S1MainTermDecomp

/-- **`s1` Path-Y main term, general finite-separable `F`** (axiom-clean). For
`F t = ∑_j c_j ∏_i Fs_{j,i}(t_i)`, the `(μ²/φ)` `y_r`-space sum of the diagonalised quadratic form
converges to the Maynard Rayleigh denominator `mkF_denominator k F = ∫_{simplex k} F²`:
`(∑_{j,j'} c_j c_{j'} · nestedLogSumW (μ²/φ) R (ofFn (Fs_j·Fs_{j'})) R) / (log R)^k
  → mkF_denominator k (∑_j c_j ∏_i Fs_{j,i})`. -/
theorem s1_yr_mainTerm_eq_mkF_denominator_decomp (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (hcont : ∀ j i, Continuous (Fs j i)) :
    Tendsto (fun R : ℕ =>
        (∑ j, ∑ j', c j * c j' *
            nestedLogSumW (fun n => gMoebiusSqTotient n) R
              (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) R)
          / (Real.log R) ^ k)
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i)))) := by
  -- continuity / integrability scaffolding
  have cont_term : ∀ (j j' : Fin J),
      Continuous (fun t : Fin k → ℝ => c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) :=
    fun j j' => continuous_const.mul (continuous_finset_prod _
      (fun i _ => ((hcont j i).mul (hcont j' i)).comp (continuous_apply i)))
  have cont_inner : ∀ (j : Fin J),
      Continuous (fun t : Fin k → ℝ => ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i))) :=
    fun j => continuous_finset_sum _ (fun j' _ => cont_term j j')
  have hInt_term : ∀ (j j' : Fin J),
      IntegrableOn (fun t : Fin k → ℝ => c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i)))
        (Sieve.simplex k) :=
    fun j j' => (cont_term j j').continuousOn.integrableOn_compact (Sieve.isCompact_simplex k)
  have hInt_inner : ∀ (j : Fin J),
      IntegrableOn (fun t : Fin k → ℝ => ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i)))
        (Sieve.simplex k) :=
    fun j => (cont_inner j).continuousOn.integrableOn_compact (Sieve.isCompact_simplex k)
  -- per-pair Fubini bridge and continuity of the list
  have hcross_cont : ∀ (j j' : Fin J) (i : Fin k), Continuous (fun x => Fs j i x * Fs j' i x) :=
    fun j j' i => (hcont j i).mul (hcont j' i)
  have hlist_cont : ∀ (j j' : Fin J),
      ∀ g ∈ List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x), Continuous g := by
    intro j j' g hg
    rw [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact hcross_cont j j' i
  have hbridge : ∀ (j j' : Fin J),
      nestedPhi (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) 0
        = ∫ t in Sieve.simplex k, ∏ i, (Fs j i (t i) * Fs j' i (t i)) :=
    fun j j' => (S1Fubini.simplex_integral_prod_eq_nestedPhi k
      (fun i => fun x => Fs j i x * Fs j' i x) (hcross_cont j j')).symm
  -- per-pair convergence (signed ladder + bridge)
  have hconv : ∀ (j j' : Fin J), Tendsto (fun R : ℕ => c j * c j' *
      (nestedLogSumW (fun n => gMoebiusSqTotient n) R
          (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) R / (Real.log R) ^ k))
      atTop (nhds (c j * c j' *
        ∫ t in Sieve.simplex k, ∏ i, (Fs j i (t i) * Fs j' i (t i)))) := by
    intro j j'
    have hbase := weighted_riemann_kd_muphi_signed
      (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) (hlist_cont j j')
    rw [List.length_ofFn] at hbase
    rw [← hbridge j j']
    exact hbase.const_mul (c j * c j')
  -- distribute the `/(log R)^k` over the double sum
  have hfun : (fun R : ℕ =>
      (∑ j, ∑ j', c j * c j' *
          nestedLogSumW (fun n => gMoebiusSqTotient n) R
            (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) R) / (Real.log R) ^ k)
      = (fun R : ℕ => ∑ j, ∑ j', c j * c j' *
          (nestedLogSumW (fun n => gMoebiusSqTotient n) R
            (List.ofFn (fun i : Fin k => fun x => Fs j i x * Fs j' i x)) R / (Real.log R) ^ k)) := by
    funext R
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j' _ => mul_div_assoc _ _ _)
  -- the limit value equals the Rayleigh denominator (square expansion + integral linearity)
  have hlim : Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i))
      = ∑ j, ∑ j', c j * c j' *
          ∫ t in Sieve.simplex k, ∏ i, (Fs j i (t i) * Fs j' i (t i)) := by
    have hsq : ∀ t : Fin k → ℝ, (∑ j, c j * ∏ i, Fs j i (t i)) ^ 2
        = ∑ j, ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i)) := by
      intro t
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      rw [Finset.prod_mul_distrib]; ring
    show (∫ t in Sieve.simplex k, (∑ j, c j * ∏ i, Fs j i (t i)) ^ 2) = _
    rw [MeasureTheory.setIntegral_congr_fun (Sieve.isClosed_simplex k).measurableSet
        (fun t _ => hsq t),
      MeasureTheory.integral_finset_sum _ (fun j _ => hInt_inner j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (∫ t in Sieve.simplex k, ∑ j', c j * c j' * ∏ i, (Fs j i (t i) * Fs j' i (t i)))
        = ∑ j', c j * c j' * ∫ t in Sieve.simplex k, ∏ i, (Fs j i (t i) * Fs j' i (t i))
    rw [MeasureTheory.integral_finset_sum _ (fun j' _ => hInt_term j j')]
    exact Finset.sum_congr rfl (fun j' _ => MeasureTheory.integral_const_mul _ _)
  rw [hfun, hlim]
  exact tendsto_finset_sum _ (fun j _ => tendsto_finset_sum _ (fun j' _ => hconv j j'))

end BoundedGaps.S1MainTermDecomp
