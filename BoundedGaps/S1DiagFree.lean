/-
# The full y-space S1 limit conditional ONLY on the OFF-DIAGONAL correction (diagonal leg discharged)

This file is the payoff of Leg 1 (`S1DiagCorrection`): it strengthens
`S1FullLimit.yspace_s1_sieveSum_div_tendsto` by **discharging the diagonal half of the correction
`hcorr` in-kernel**, leaving as the sole analytic hypothesis the *off-diagonal* correction
(`hoffdiag`, the genuine remaining nut that needs a growing modulus `W = W(N)`).

## Structure
* `yspace_s1_heuristic_main_div_sieveB_tendsto_scale` — the heuristic-main limit with a **general
  scale** `x : ℕ → ℝ` and **general density** `M : ℕ → ℝ` (both threaded; the proof only uses
  `hcov : (W·N)+2 ≤ x N` and `M N ≠ 0`, since `M` cancels in the `B^{+k}·M` normalisation). This is
  the scale-decoupled version the diagonal leg (`S1DiagCorrection`) requires (it needs `x` poly-large
  so the density `M ≥ N^{6k+1}`).
* `offdiagCorr` — the off-diagonal-restricted correction sum (the `¬diag` complement of `diagCorr`).
* `fullCorr_eq_diag_add_offdiag` — the exact split of the full correction (over all `sieveDivisors`,
  at the lattice density) into `diagCorr + offdiagCorr`, via `piFinset_prod_pair_sum_restrict` +
  `Finset.sum_filter_add_sum_filter_not`.
* `yspace_s1_sieveSum_div_tendsto_diagFree` — the full sieve-sum limit, conditional ONLY on
  `offdiagCorr/(B^{+k}·M) → 0` (the diagonal half discharged by `S1DiagCorrection`).

No PNT, no contour, no BV. Conditional on `hBaseW` (discharged for primorial `W` via `CoprimeMertens`)
and the off-diagonal correction.
-/
import BoundedGaps.S1DiagCorrection
import BoundedGaps.S1FullLimit

open MeasureTheory Filter Topology
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1DiagFree

/-- **Scale-general heuristic-main limit (`B^{+k}` normalisation).** As
`S1MainLimit.yspace_s1_heuristic_main_div_sieveB_tendsto`, but with the sieve scale `x : ℕ → ℝ` and
the density `M : ℕ → ℝ` BOTH free functions of `N` (the proof uses only `hcov : (W·N)+2 ≤ x N` and the
eventual `M N ≠ 0`, since `M` cancels in the `B^{+k}·M` normalisation). This is the scale-decoupled
form the diagonal correction leg requires. Composes
`S1CountReconcile.yr_heuristic_main_eq_quadForm_product` (free scale) with
`S1MainLimit.yspace_box_quadform_div_tendsto`. -/
theorem yspace_s1_heuristic_main_div_sieveB_tendsto_scale {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (x M : ℕ → ℝ) (hW : 1 ≤ W)
    (hMne : ∀ᶠ N : ℕ in atTop, M N ≠ 0)
    (hcov : ∀ N : ℕ, (W * N : ℝ) + 2 ≤ x N)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hFsupp : ∀ i : Fin k, ∀ t : ℝ, 1 < t → Fs i t = 0)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto (fun N : ℕ =>
        (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)
                ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)),
            (∏ i : Fin k,
              S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).1
                * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).2)
            * (M N / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
          / (Sieve.sieveB W (N : ℝ) ^ k * M N))
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hφpos : (0 : ℝ) < W.totient := by
    have := Nat.totient_pos.mpr (by omega : 0 < W); exact_mod_cast this
  have hratio_pos : (0 : ℝ) < (W.totient : ℝ) / W := div_pos hφpos hWpos
  have hpk : ((W.totient : ℝ) / W) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hratio_pos)
  have hbox := S1MainLimit.yspace_box_quadform_div_tendsto Fs hFs hsupp hBaseW
  have hdiv := hbox.div_const (((W.totient : ℝ) / W) ^ k)
  have hlim_eq : (((W.totient : ℝ) / W) ^ k
        * Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i))) / ((W.totient : ℝ) / W) ^ k
      = Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)) := by
    field_simp
  rw [hlim_eq] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2, hMne] with N hN2 hMN
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hxN : 0 < x N := by
    have h0 : (0 : ℝ) ≤ (W : ℝ) * (N : ℝ) := by positivity
    have hcN := hcov N
    push_cast at hcN
    linarith
  have hbig := S1CountReconcile.yr_heuristic_main_eq_quadForm_product k Fs H b W
    (x N) (M N) N hxN hW hN2 (hcov N) hFsupp
  rw [hbig]
  have hsB : Sieve.sieveB W (N : ℝ) ^ k = ((W.totient : ℝ) / W) ^ k * (Real.log N) ^ k := by
    rw [Sieve.sieveB, mul_pow]
  rw [hsB]
  have hlogk : (Real.log N) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hlogN)
  field_simp

/-- **The off-diagonal-restricted y-space S1 correction sum** (the `¬diag` complement of
`S1DiagCorrection.diagCorr`). Over the squarefree `W`-coprime candidate sets, restricted to the
*non-diagonal* tuples `P` (some pair of coordinate moduli `lcm(P i)`, `lcm(P j)` is NOT coprime),
the weighted count error. This is the genuine remaining nut: it scales with `M` (cancels against the
main term), so the scale trick is useless; it needs a *growing* modulus `W = W(N)` and the
shared-prime singular-series `∑_{p>D₀}1/p²` tail (`S1OffDiagSize`). -/
noncomputable def offdiagCorr {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (b W : ℕ) (x L M : ℝ) : ℝ :=
  ∑ P ∈ (Fintype.piFinset (fun i : Fin k =>
        ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W))
          ×ˢ ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)))).filter
        (fun P => ¬ ∀ i j : Fin k, i ≠ j →
          Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)),
      (∏ i : Fin k,
        S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).1
          * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).2)
      * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
            (fun m => ∀ i : Fin k,
              (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
          - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))

/-- **The full y-space S1 correction splits as `diagCorr + offdiagCorr`.** The correction over the
*full* candidate lattice `sieveDivisors` (the second summand of
`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`) restricts to the divisor-closed
`Rset` (off-`Rset` terms vanish, `yLambda_eq_zero_of_not_mem`), then splits by the diagonal predicate
(`Finset.sum_filter_add_sum_filter_not`) into `S1DiagCorrection.diagCorr` (PNT-free, Leg 1) plus
`offdiagCorr` (the growing-`W` nut, Leg 2). Pure algebra. -/
theorem fullCorr_eq_diag_add_offdiag {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (b W : ℕ) (x L M : ℝ) :
    (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
          BoundedGaps.Sieve.sieveDivisors H i.val b W x
            ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
        (∏ i : Fin k,
          S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).1
            * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).2)
        * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
            - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      = S1DiagCorrection.diagCorr Fs H b W x L M + offdiagCorr Fs H b W x L M := by
  classical
  rw [S1Correction.piFinset_prod_pair_sum_restrict
      (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W))
      (fun i => BoundedGaps.Sieve.sieveDivisors H i.val b W x)
      (fun i => Finset.filter_subset _ _)
      (fun i => S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L)
      (fun i d hd => S1YSpace.yLambda_eq_zero_of_not_mem _
        (BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x).2.2 (Fs i) L hd)
      (fun P => ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
            (fun m => ∀ i : Fin k,
              (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
          - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))]
  rw [S1DiagCorrection.diagCorr, offdiagCorr]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **The full y-space S1 sieve-sum limit, conditional ONLY on the OFF-DIAGONAL correction.** The
*actual* separable y-space sieve sum `sieveSum (selberg_nu_yr_sep …)` at a poly-large sieve scale
`x = x(N)` (decoupled from the level `N`), level `R = N`, normalised by the y-space main term
`B^{+k}·M` with `M = (⌊2x⌋−(⌈x⌉−1))/W` the exact lattice density, converges to the Maynard Rayleigh
denominator `mkF_denominator k (∏ᵢ Fs i)` — **provided only the OFF-DIAGONAL correction is
`o(B^{+k}·M)`** (`hoffdiag`).

This strengthens `S1FullLimit.yspace_s1_sieveSum_div_tendsto` by discharging the *diagonal* half of
the correction `hcorr` in-kernel (PNT-free, via `S1DiagCorrection.diag_correction_ratio_tendsto_zero`
— the scale-trick), leaving the genuine remaining nut (the off-diagonal leg, which needs a growing
modulus `W = W(N)`). Composes the scale-general heuristic-main limit
(`yspace_s1_heuristic_main_div_sieveB_tendsto_scale`), the correction split
(`fullCorr_eq_diag_add_offdiag`), and Leg 1. No PNT, no contour, no BV; conditional on `hBaseW` +
`hoffdiag`. -/
theorem yspace_s1_sieveSum_div_tendsto_diagFree {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (C : ℝ) (hW : 0 < W)
    (hC : ∀ i, ∀ t, |Fs i t| ≤ C)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hFsupp : ∀ i : Fin k, ∀ t : ℝ, 1 < t → Fs i t = 0)
    (x : ℕ → ℝ) (hcov : ∀ N : ℕ, (W * N : ℝ) + 2 ≤ x N)
    (hgrow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (6 * k + 1)
        ≤ ((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W)))
    (hoffdiag : Tendsto (fun N : ℕ =>
        offdiagCorr Fs H b W (x N) (Real.log (N : ℝ))
            (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
          / (Sieve.sieveB W (N : ℝ) ^ k
              * (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
        BoundedGaps.Sieve.sieveSum (S1YSpace.selberg_nu_yr_sep k Fs H (N : ℝ)
            (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W))) b W (x N)
          / (Sieve.sieveB W (N : ℝ) ^ k
              * (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))))
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have hW1 : 1 ≤ W := hW
  have hMne : ∀ᶠ N : ℕ in atTop,
      ((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ) ≠ 0 := by
    filter_upwards [hgrow, eventually_ge_atTop 1] with N hgN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hpow : (0 : ℝ) < (N : ℝ) ^ (6 * k + 1) := by positivity
    exact ne_of_gt (lt_of_lt_of_le hpow hgN)
  have hheur := yspace_s1_heuristic_main_div_sieveB_tendsto_scale Fs H b W x
    (fun N => ((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
    hW1 hMne hcov hFs hsupp hFsupp hBaseW
  have hdiag := S1DiagCorrection.diag_correction_ratio_tendsto_zero Fs H b W C hW hC hFsupp x hcov hgrow
  have hcomb := hheur.add (hdiag.add hoffdiag)
  simp only [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hxN : 0 < x N := by
    have h0 : (0 : ℝ) ≤ (W : ℝ) * (N : ℝ) := by positivity
    have hcN := hcov N
    push_cast at hcN
    linarith
  rw [S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction k Fs H (N : ℝ)
      (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) b W (x N) hxN
      (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))]
  rw [fullCorr_eq_diag_add_offdiag Fs H b W (x N) (Real.log (N : ℝ))
      (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))]
  beta_reduce
  ring

/-- **The full y-space S1 sieve-sum limit for primorial `W`, conditional ONLY on the off-diagonal.**
Specialises `yspace_s1_sieveSum_div_tendsto_diagFree` to a primorial modulus `W = ∏_{p∈T} p`
(`2 ∈ T`, exactly the sieve's `W = ∏_{p≤D₀} p`), discharging the W-coprime sharp Mertens base
`hBaseW` IN-KERNEL via `CoprimeMertens.hBaseW_of_primes_totient`. So for the actual sieve modulus the
contour-free y-space `s1` rests on **no analytic axiom and only the off-diagonal correction**
(`hoffdiag`): the heuristic main term AND the entire diagonal half of `hcorr` are machine-checked
unconditional (PNT-free). The sole remaining obligation is the off-diagonal leg, which needs a growing
modulus `W = W(N)` (Leg 2). -/
theorem yspace_s1_sieveSum_div_tendsto_diagFree_primorial {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (C : ℝ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (h2 : 2 ∈ T)
    (hWeq : W = ∏ p ∈ T, p)
    (hC : ∀ i, ∀ t, |Fs i t| ≤ C)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hFsupp : ∀ i : Fin k, ∀ t : ℝ, 1 < t → Fs i t = 0)
    (x : ℕ → ℝ) (hcov : ∀ N : ℕ, (W * N : ℝ) + 2 ≤ x N)
    (hgrow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (6 * k + 1)
        ≤ ((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
    (hoffdiag : Tendsto (fun N : ℕ =>
        offdiagCorr Fs H b W (x N) (Real.log (N : ℝ))
            (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
          / (Sieve.sieveB W (N : ℝ) ^ k
              * (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
        BoundedGaps.Sieve.sieveSum (S1YSpace.selberg_nu_yr_sep k Fs H (N : ℝ)
            (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W (x N)).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W))) b W (x N)
          / (Sieve.sieveB W (N : ℝ) ^ k
              * (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))))
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have hW : 0 < W := by
    rw [hWeq]; exact Finset.prod_pos (fun p hp => (hT p hp).pos)
  refine yspace_s1_sieveSum_div_tendsto_diagFree Fs H b W C hW hC hFs hsupp hFsupp x hcov hgrow
    ?_ hoffdiag
  rw [hWeq]
  exact BoundedGaps.CoprimeMertens.hBaseW_of_primes_totient T hT h2

end BoundedGaps.S1DiagFree
