/-
# Unconditional `hBaseW` instantiation of the y-space `s1` box-product main term

`CoprimeMertens.hBaseW_of_primes_totient` discharges the W-coprime sharp Mertens base `hBaseW`
for any primorial modulus `W = ∏_{p∈T} p` (`T` a finite set of primes with `2 ∈ T`). Threading it
into `S1KDBox.yspace_kd_box_product_tendsto` makes the **k-D box-product `s1` main-term limit fully
unconditional** for such `W` — the contour-free `s1` main term no longer rests on any analytic
axiom (the remaining `s1` input is the off-diagonal correction `hcorr`, handled elsewhere).
-/
import BoundedGaps.S1KDBox
import BoundedGaps.CoprimeMertens

open scoped BigOperators
open Filter Topology

namespace BoundedGaps.S1HBaseW

/-- **k-D box-product `s1` main term, UNCONDITIONAL for primorial `W`.** For `W = ∏_{p∈T} p`
(`T` a finite set of primes, `2 ∈ T`) and `F = ∑_j c_j ∏_i Fs_{j,i}` simplex-supported with
`Fs ∈ ContDiff ℝ 1`, the normalised box-product `s1` form converges to `(φW/W)^k · ∫_{simplex} F²`,
with the W-coprime base `hBaseW` discharged in-kernel (`CoprimeMertens.hBaseW_of_primes_totient`).
No analytic axiom. -/
theorem yspace_kd_box_product_tendsto_primorial {k J : ℕ} (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (h2 : 2 ∈ T) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (hFs : ∀ j i, ContDiff ℝ 1 (Fs j i))
    (hsupp : Function.support (fun t => ∑ j, c j * ∏ i, Fs j i (t i)) ⊆ Sieve.simplex k) :
    Tendsto (fun N : ℕ =>
        (∑ j, ∑ j', c j * c j' * ∏ i,
            BoundedGaps.S1KDBox.quadForm (∏ p ∈ T, p) (Fs j i) (Fs j' i) N) / (Real.log N) ^ k)
      atTop (nhds ((((∏ p ∈ T, p : ℕ).totient : ℝ) / (∏ p ∈ T, p)) ^ k
        * Sieve.mkF_denominator k (fun t => ∑ j, c j * ∏ i, Fs j i (t i)))) :=
  BoundedGaps.S1KDBox.yspace_kd_box_product_tendsto (W := ∏ p ∈ T, p) c Fs hFs hsupp
    (BoundedGaps.CoprimeMertens.hBaseW_of_primes_totient T hT h2)

end BoundedGaps.S1HBaseW
