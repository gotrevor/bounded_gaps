/-
# The count→`M` candidate-set reconciliation, assembled (per-coordinate bridge)

The separable y-space sieve's heuristic main term (`S1YSpace.yr_heuristic_main_eq_muphi`) is a box
product of per-coordinate factors, each a y-space bilinear Selberg form over the *actual* candidate
set `Rset_i = sieveDivisors_i.filter (sf ∧ (·,W)=1)` — the squarefree `W`-coprime divisors that
appear in the sieve interval. The contour-free limit (`S1KDBox.yspace_kd_box_product_tendsto`, built
on `S1YSpace.yspace_sieve_quadform_tendsto`) instead sums over the clean index
`{r ≤ N : sf ∧ (r,W)=1}`.

This file assembles the reconciliation between the two index sets into a single per-coordinate
equality (`yr_coord_factor_eq_Icc_sum`), composing:
* `S1YSpace.yr_coord_factor_eq_muphi` — the coordinate factor equals `∑_{r∈Rset_i}(μ²/φ)F²`;
* `S1CandidateSet.filter_Icc_subset_filter_sieveDivisors` — `{r≤N:sf∧(r,W)=1} ⊆ Rset_i` (every small
  `r` appears, by CRT) once the interval is long enough;
* `S1CandidateSet.sieve_interval_covers` — for `x ≥ W·N+2` the interval *is* that long;
* `S1CandidateSet.coord_sum_restrict_to_Icc` — the extra large divisors (`r > N ≥ ⌊R⌋ ⟹ r > R`) have
  `F(log r/log R)=0`, so the `Rset_i`-sum collapses to the clean `{r≤N}`-sum.

Pure combinatorics / NT / real analysis — unconditional, no BV. With this, the only remaining count→`M`
content is the **normalisation glue** (matching `M·(box product)/(log R)^k` to `α·alphaMainTerm`) and
the **off-diagonal `o(main)` correction** (BV-gated, `SieveExpansion.correction_abs_bound`).
-/
import BoundedGaps.S1YSpace
import BoundedGaps.S1CandidateSet

open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1CountReconcile

/-- **Coordinate factor = clean diagonal sum** (the count→`M` candidate-set reconciliation, assembled).
The y-space bilinear coordinate factor over the *actual* candidate set
`Rset_i = sieveDivisors_i.filter(sf∧(·,W)=1)` equals the contour-free limit's clean diagonal sum
`∑_{r≤N: sf∧(r,W)=1} (μ²/φ)·F(log r/log R)²`, for `x` large enough that the sieve interval covers
`[1,N]` (`x ≥ W·N+2`) and `F` supported on `[0,1]` with `N ≥ ⌊R⌋`. Composes
`S1YSpace.yr_coord_factor_eq_muphi` (factor `= ∑_{Rset_i}(μ²/φ)F²`) with
`S1CandidateSet.coord_sum_restrict_to_Icc` (restrict to the clean index via the inclusion +
level cutoff). This is the exact per-coordinate bridge from the capstone
`S1YSpace.yr_heuristic_main_eq_muphi` to `S1KDBox.yspace_kd_box_product_tendsto`. -/
theorem yr_coord_factor_eq_Icc_sum (H : List ℕ) (i b W : ℕ) (x : ℝ) (F : ℝ → ℝ) (R : ℝ) (N : ℕ)
    (hx : 0 < x) (hW : 1 ≤ W) (hR : 1 < R) (hNR : R < (N : ℝ) + 1)
    (hcov : (W * N : ℝ) + 2 ≤ x) (hFsupp : ∀ t : ℝ, 1 < t → F t = 0) :
    (∑ d ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
       ∑ e ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
        S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) d
          * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) e
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / Real.log R) ^ 2 := by
  rw [S1YSpace.yr_coord_factor_eq_muphi H i b W x F R]
  obtain ⟨hAB, hlenN⟩ := S1CandidateSet.sieve_interval_covers x W N hcov
  refine S1CandidateSet.coord_sum_restrict_to_Icc _ F R N hR hNR hFsupp
    (S1CandidateSet.filter_Icc_subset_filter_sieveDivisors H i b W N x hx hW hAB hlenN)
    (fun r hr => (Finset.mem_filter.mp hr).2)

end BoundedGaps.S1CountReconcile
