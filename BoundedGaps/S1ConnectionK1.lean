import BoundedGaps.Sieve
import BoundedGaps.WeightedMertens
import BoundedGaps.WeightedRiemannGen
import BoundedGaps.S1Fubini

/-!
# `s1` Path-Y main term ↔ `mkF_denominator`, the `k = 1` end-to-end connection.

This file closes the GPY/Maynard `s1` (Path-Y, `y_r`-space) analytic chain **at `k = 1`**, fully and
axiom-clean: the `(μ²/φ)`-weighted sum of `F²` over `r ≤ N` converges to the Maynard Rayleigh
denominator `mkF_denominator 1 F = ∫_{simplex 1} F²`.

It composes the two halves now in place:
- `WeightedMertens.weighted_mertens_sq` — the 1-D `y_r`-space asymptotic
  `(∑_{r≤N} (μ²/φ)(r)·g(log r/log N)²)/log N → ∫₀¹ g²` (`g = F(fun _ => ·)`), itself resting on the
  fully-discharged `riemann_sum_log_weight` + sharp Mertens; and
- the `k = 1` simplex reduction `∫_{simplex 1} F² = ∫_{[0,1]} (F(fun _ => t))²` (the trivial Fubini
  case, re-derived here publicly via the volume-preserving `funUnique` identification).

For `k ≥ 2` the same composition runs through `WeightedRiemannGen.weighted_riemann_kd_muphi_sep`
(`→ nestedPhi (ofFn Fs²) 0`) and the general simplex-Fubini bridge `∫_{simplex k} ∏gᵢ =
nestedPhi (ofFn g) 0` (the next connection step; currently on Aristotle). This `k = 1` theorem is the
concrete validation of that whole programme and the template for the `k`-D version.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ContDiff
open BoundedGaps.SingularSeries

namespace BoundedGaps.S1ConnectionK1

/-- The `k = 1` Maynard denominator collapses to a 1-D integral over `[0,1]`:
`mkF_denominator 1 F = ∫_{[0,1]} (F (fun _ => t))²`. The trivial (`k = 1`) Fubini case, via the
volume-preserving identification `MeasurableEquiv.funUnique (Fin 1) ℝ` and
`simplex 1 ≃ [0,1]`. (Re-derived publicly here; the `Sieve` version is `private`.) -/
theorem mkF_denominator_one_eq (F : (Fin 1 → ℝ) → ℝ) :
    Sieve.mkF_denominator 1 F = ∫ t in Set.Icc (0 : ℝ) 1, F (fun _ => t) ^ 2 := by
  have hpre : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹' (Sieve.simplex 1)
      = Set.Icc (0 : ℝ) 1 := by
    ext t
    simp only [Set.mem_preimage, MeasurableEquiv.funUnique, Sieve.simplex, Set.mem_setOf_eq,
      Set.mem_Icc]
    constructor
    · rintro ⟨h0, hsum⟩; exact ⟨h0 0, by simpa [Fin.sum_univ_one] using hsum⟩
    · rintro ⟨h0, h1⟩
      exact ⟨fun i => by fin_cases i; simpa using h0, by simpa [Fin.sum_univ_one] using h1⟩
  have hmp := (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hemb := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
  have key := hmp.setIntegral_preimage_emb hemb (fun y => F y ^ 2) (Sieve.simplex 1)
  rw [hpre] at key
  rw [show Sieve.mkF_denominator 1 F = ∫ t in Sieve.simplex 1, F t ^ 2 from rfl]
  exact key.symm

/-- **`s1` Path-Y main term = `mkF_denominator`, at `k = 1`** (axiom-clean). For a smooth
`F : (Fin 1 → ℝ) → ℝ`, the `(μ²/φ)`-weighted sum of `F²` over `r ≤ N` converges to the Maynard
Rayleigh denominator `mkF_denominator 1 F = ∫_{simplex 1} F²`:
`(∑_{1≤r≤N} (μ²/φ)(r)·F(fun _ => log r/log N)²)/log N → mkF_denominator 1 F`.
The end-to-end `y_r`-space `s1` analytic chain at `k = 1`, composing `weighted_mertens_sq` with the
trivial simplex reduction. -/
theorem s1_yr_mainTerm_eq_mkF_denominator_one (F : (Fin 1 → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    Tendsto (fun N : ℕ =>
        (∑ r ∈ Finset.Icc 1 N,
            gMoebiusSqTotient r * F (fun _ => Real.log r / Real.log N) ^ 2) / Real.log N)
      atTop (nhds (Sieve.mkF_denominator 1 F)) := by
  have hinner : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have hgcd : ContDiff ℝ 1 (fun t : ℝ => F (fun _ => t)) := (hF.comp hinner).of_le (by norm_num)
  have hlim :=
    BoundedGaps.WeightedMertens.weighted_mertens_sq (F := fun t : ℝ => F (fun _ => t)) hgcd
  -- rewrite the limit value `∫₀¹ g²` as `mkF_denominator 1 F`.
  have hint : (∫ u in (0 : ℝ)..1, (fun t : ℝ => F (fun _ => t)) u ^ 2)
      = Sieve.mkF_denominator 1 F := by
    rw [mkF_denominator_one_eq, intervalIntegral.integral_of_le (zero_le_one),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hint] at hlim
  exact hlim

open BoundedGaps.WeightedRiemannKD (nestedPhi)
open BoundedGaps.WeightedRiemannGen (nestedLogSumW weighted_riemann_kd_muphi_sep)

/-- **`s1` Path-Y main term = `mkF_denominator`, all `k`** (axiom-clean, end-to-end). For a
**separable** smooth cutoff `F t = ∏ᵢ Fs i (t i)`, the `(μ²/φ)` `y_r`-space simplex sum of the
squared coordinate weights converges to `mkF_denominator k F = ∫_{simplex k} F²`:
`(∑_{∏rᵢ≤R} ∏ᵢ (μ²/φ)(rᵢ)·Fs i (log rᵢ/log R)²)/(log R)^k → mkF_denominator k (∏ Fs)`.

Composes `weighted_riemann_kd_muphi_sep` (PROVEN: → `nestedPhi (ofFn Fs²) 0`) with the now-discharged
simplex-Fubini bridge `S1Fubini.simplex_integral_prod_eq_nestedPhi` (`∫_{simplex k} ∏gᵢ =
nestedPhi (ofFn g) 0`, applied to `g = Fs²`). This is the k-D generalisation of
`s1_yr_mainTerm_eq_mkF_denominator_one`; the whole `s1` analytic **main term** is now PROVEN. -/
theorem s1_yr_mainTerm_eq_mkF_denominator_sep (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (hcont : ∀ i, Continuous (Fs i)) :
    Tendsto (fun R : ℕ =>
        nestedLogSumW (fun n => gMoebiusSqTotient n) R
            (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)) R / (Real.log R) ^ k)
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have h1 : (fun t : Fin k → ℝ => (∏ i, Fs i (t i)) ^ 2)
      = (fun t => ∏ i, (Fs i (t i)) ^ 2) := by
    funext t; rw [← Finset.prod_pow]
  have hden : Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i))
      = nestedPhi (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)) 0 := by
    show (∫ t in Sieve.simplex k, (∏ i, Fs i (t i)) ^ 2) = _
    rw [h1]
    exact S1Fubini.simplex_integral_prod_eq_nestedPhi k
      (fun i => fun x => (Fs i x) ^ 2) (fun i => (hcont i).pow 2)
  rw [hden]
  exact weighted_riemann_kd_muphi_sep k Fs hcont
