/-
# The full y-space S1 sieve-sum limit, conditional only on the correction

This file assembles the honest top-level statement of the contour-free Path-Y `s1` programme:
the *actual* separable y-space sieve sum `sieveSum (selberg_nu_yr_sep …)`, normalised by the y-space
main term `B^{+k}·M`, converges to the Maynard Rayleigh denominator `mkF_denominator k (∏ᵢ Fs i)` —
**conditional only** on the off-diagonal correction being `o(B^{+k}·M)` (`hcorr`, the BV-gated gap C)
and the W-coprime Mertens base `hBaseW`.

It composes two machine-checked, axiom-clean ingredients:
* `S1MainLimit.yspace_s1_heuristic_main_div_sieveB_tendsto` — the heuristic main term limit
  (unconditional given `hBaseW`);
* `S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction` — the exact `sieveSum =
  heuristic + correction` split (pure algebra).

So the **only** remaining analytic obligation for contour-free y-space `s1` (beyond the architectural
`B^{±k}` flagship convention flip, which is Trevor's call) is the correction bound `hcorr` — whose
diagonal half is already `o(main)` unconditionally (`S1DiagonalSize`), leaving the off-diagonal
BV-gated singular-series discrepancy.
-/
import BoundedGaps.S1MainLimit

open MeasureTheory Filter Topology
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1FullLimit

/-- **The full y-space S1 sieve-sum limit, conditional only on the correction (B^{+k}).** The
*actual* separable y-space sieve sum `sieveSum (selberg_nu_yr_sep …)` at scale `x = W·N+2`, level
`R = N`, candidate sets `Rset_i = sieveDivisors_i.filter(sf∧coprime)`, normalised by the y-space
main term `B^{+k}·M`, converges to `mkF_denominator k (∏ᵢ Fs i) = ∫_{simplex}(∏ᵢ Fs i)²` —
**provided the off-diagonal correction is `o(B^{+k}·M)`** (`hcorr`, the BV-gated obligation, gap C).

This is the honest statement of where contour-free y-space `s1` stands: the heuristic main term is
machine-checked unconditional (`S1MainLimit.yspace_s1_heuristic_main_div_sieveB_tendsto`); the
sieve-sum split is machine-checked algebra
(`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`); so the **only** remaining
analytic input is `correction = o(main)` (`hcorr`) and the architectural `B^{±k}` flagship flip.
No PNT, no contour; conditional on `hBaseW` + `hcorr`. -/
theorem yspace_s1_sieveSum_div_tendsto {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (M : ℝ) (hM : M ≠ 0) (hW : 1 ≤ W)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hFsupp : ∀ i : Fin k, ∀ t : ℝ, 1 < t → Fs i t = 0)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W)))
    (hcorr : Tendsto (fun N : ℕ =>
        (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)
                ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)),
            (∏ i : Fin k,
              S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).1
                * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).2)
            * ((((Finset.Icc ⌈(W * N : ℝ) + 2⌉₊ ⌊2 * ((W * N : ℝ) + 2)⌋₊).filter
                    (fun n => n % W = b % W)).filter
                  (fun m => ∀ i : Fin k,
                    (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
                - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
          / (Sieve.sieveB W (N : ℝ) ^ k * M)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
        BoundedGaps.Sieve.sieveSum (S1YSpace.selberg_nu_yr_sep k Fs H (N : ℝ)
            (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W))) b W ((W * N : ℝ) + 2)
          / (Sieve.sieveB W (N : ℝ) ^ k * M))
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have hheur := S1MainLimit.yspace_s1_heuristic_main_div_sieveB_tendsto Fs H b W M hM hW hFs hsupp
    hFsupp hBaseW
  have hcomb := hheur.add hcorr
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards with N
  have hsplit := S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction k Fs H (N : ℝ)
    (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
      (fun r => Squarefree r ∧ Nat.Coprime r W)) b W ((W * N : ℝ) + 2) (by positivity) M
  rw [hsplit]
  ring

end BoundedGaps.S1FullLimit
