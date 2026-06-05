/-
# The y-space S1 off-diagonal size bound — the `∑_{p>D₀} 1/p²` tail (UNCONDITIONAL)

The off-diagonal leg of the y-space S1 correction bound (`S1Correction.yspace_correction_abs_bound`)
is `∑_{¬diag P} |∏λλ| · M/∏[dᵢ,eᵢ]`. Classically (Maynard/GPY) this is `o(M·(log R)^k)` because each
off-diagonal `P` carries a *shared prime* `p > D₀` between two coordinates, contributing a `1/p²`
weight to the singular-series discrepancy; summed over all shared primes this is
`∑_{i<j} ∑_{p>D₀} 1/p² → 0` as `D₀ → ∞` — purely a **convergent-series tail**, NO BV/EH.

This file isolates that analytic engine: the `1/n²` (Basel-type) `p`-series tail tends to `0`, and any
finite reciprocal-square sum over a set of naturals all exceeding `D₀` (e.g. the shared primes) is
bounded by that tail. Combined with the off-diagonal vanishing of `S1Correction`, this is the
elementary (unconditional) core of the off-diagonal size estimate.
-/
import BoundedGaps.SieveExpansion

open Filter Topology
open scoped BigOperators

namespace BoundedGaps.S1OffDiagSize

/-- Summability of `1/(k+D₀)²` (the shifted Basel `p`-series). -/
theorem summable_recip_sq_shift (D₀ : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((k + D₀ : ℕ):ℝ)^2) := by
  have hf : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff D₀).mpr hf

/-- **The `1/n²` tail tends to 0.** As `D₀ → ∞`, `∑_{k} 1/(k+D₀)² → 0`. The convergent-series tail
of the Basel-type `p`-series (`tendsto_sum_nat_add`). The analytic engine behind the off-diagonal
S1 correction: a shared prime `p > D₀` contributes a `1/p²` weight, and these sum to `o(1)`. -/
theorem recip_sq_tail_tendsto_zero :
    Tendsto (fun D₀ : ℕ => ∑' k : ℕ, (1:ℝ)/((k + D₀ : ℕ):ℝ)^2) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n => (1:ℝ)/(n:ℝ)^2)

/-- **Finite reciprocal-square sum over a tail set ≤ the infinite tail.** Any finite set `s` of
naturals all exceeding `D₀` (e.g. the shared primes `> D₀` of an off-diagonal tuple) satisfies
`∑_{n∈s}1/n² ≤ ∑'_k 1/(k+(D₀+1))²`. Combined with `recip_sq_tail_tendsto_zero` this gives a
**uniform** `o(1)` bound (in `D₀`) on the off-diagonal singular-series weight — the `∑_{p>D₀}1/p²`
factor of the S1 correction off-diagonal leg, with NO BV/EH. -/
theorem sum_finset_recip_sq_le_tail (D₀ : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, D₀ < n) :
    ∑ n ∈ s, (1:ℝ)/(n:ℝ)^2 ≤ ∑' k : ℕ, (1:ℝ)/((k + (D₀ + 1) : ℕ):ℝ)^2 := by
  classical
  set g : ℕ → ℝ := fun k => (1:ℝ)/((k + (D₀ + 1) : ℕ):ℝ)^2 with hg
  have hginj : Set.InjOn (fun n => n - (D₀ + 1)) s := by
    intro a ha b hb hab
    have ha' : D₀ + 1 ≤ a := hs a ha
    have hb' : D₀ + 1 ≤ b := hs b hb
    simp only at hab
    omega
  have hstep : ∑ n ∈ s, (1:ℝ)/(n:ℝ)^2 = ∑ j ∈ s.image (fun n => n - (D₀ + 1)), g j := by
    rw [Finset.sum_image hginj]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' : D₀ + 1 ≤ n := hs n hn
    rw [hg]
    simp only
    rw [show n - (D₀ + 1) + (D₀ + 1) = n from by omega]
  rw [hstep]
  refine (summable_recip_sq_shift (D₀ + 1)).sum_le_tsum _ (fun j _ => ?_)
  rw [hg]; positivity

end BoundedGaps.S1OffDiagSize
