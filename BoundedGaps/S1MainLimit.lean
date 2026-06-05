/-
# The y-space S1 heuristic main term limit (capstone, B^{+k} normalisation)

This file crystallises the entire contour-free Path-Y S1 main-term chain — built across several laps
in `S1YSpace`, `S1KDBox`, `S1CandidateSet`, `S1CountReconcile`, `S1BoxSimplex` — into a **single
limit statement directly about the separable sieve's heuristic main term**.

Setting the level `R = N` and the sieve scale `x = W·N+2` (so `S1CandidateSet` covers `[1,N]`), the
y-space heuristic main term `M·∏ᵢ ∑_{r≤N}(μ²/φ)Fᵢ²`, normalised by the **y-space main term**
`B^{+k}·M` (with `B = sieveB W N = φ(W)/W·log N` evaluated at the level, `M` the lattice density),
converges to `mkF_denominator k (∏ᵢ Fs i) = ∫_{simplex}(∏ᵢ Fs i)²` — the Maynard Rayleigh
denominator, **with the limit constant `α` exactly `mkF_denominator` and no leftover factor**.

This is the contour-free y-space analog of `alphaBound`'s `(α + o(1))·B^{-k}·x/W`: the singular
series `(φW/W)^k` and the `(log N)^k` growth are all absorbed into `B^{+k}` (the y-space
normalisation, vs the d-space `B^{-k}` of `Sieve.alphaMainTerm`), leaving the clean constant. The
only pieces between this and a y-space `alphaBound` are the `B^{±k}` flagship convention flip
(architectural — `PENDING_WORK.md`, memory `[[yspace-s1-normalization-Bpm-k]]`) and the BV-gated
`o(main)` off-diagonal correction.

`yspace_box_quadform_div_tendsto` is the single-family (`J=1`) instantiation of
`S1KDBox.yspace_kd_box_product_tendsto`; the capstone composes it with
`S1CountReconcile.yr_heuristic_main_eq_quadForm_product`. No PNT, no contour; conditional only on
`hBaseW` (the W-coprime sharp Mertens base, Aristotle brick `65d11d89`).
-/
import BoundedGaps.S1CountReconcile

open MeasureTheory Filter Topology
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1MainLimit

/-- **Single-family box quadratic-form limit.** The product over the `k` coordinates of the 1-D
y-space bilinear Selberg forms `quadForm W (Fs i) (Fs i) N`, normalised by `(log N)^k`, converges to
`(φW/W)^k · ∫_{simplex}(∏ᵢ Fs i)²`. The `J=1` instantiation of
`S1KDBox.yspace_kd_box_product_tendsto` — the single-family form the heuristic main term actually
produces. -/
theorem yspace_box_quadform_div_tendsto {k : ℕ} {W : ℕ} (Fs : Fin k → ℝ → ℝ)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto (fun N : ℕ => (∏ i, S1KDBox.quadForm W (Fs i) (Fs i) N) / (Real.log N) ^ k)
      atTop (nhds (((W.totient : ℝ) / W) ^ k
        * Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have h := S1KDBox.yspace_kd_box_product_tendsto (k := k) (J := 1) (W := W)
    (fun _ => (1 : ℝ)) (fun _ i => Fs i) (fun _ i => hFs i)
    (by simpa using hsupp) hBaseW
  simpa using h

/-- **The y-space S1 heuristic main term limit (capstone, B^{+k} normalisation).** Setting the
level `R = N` and the sieve scale `x = W·N+2` (so the candidate set covers `[1,N]`), the separable
y-space sieve's heuristic main term, normalised by the y-space main term `B^{+k}·M` (with
`B = sieveB W N = φ(W)/W·log N` the sieve scale at the level and `M` the lattice density),
converges to `mkF_denominator k (∏ᵢ Fs i) = ∫_{simplex}(∏ᵢ Fs i)²` — the Maynard Rayleigh
denominator, **with α exactly `mkF_denominator` and no leftover factor**. This is the contour-free
y-space analog of `alphaBound`'s `(α + o(1))·B^{-k}·x/W`: the singular series `(φW/W)^k` and the
`(log N)^k` are all absorbed into `B^{+k}`, leaving the clean constant. Composes
`S1CountReconcile.yr_heuristic_main_eq_quadForm_product` (heuristic main `= M·∏ᵢ quadForm`) with
`yspace_box_quadform_div_tendsto` (`∏ᵢ quadForm/(log N)^k → (φW/W)^k·mkF_den`). No PNT, no contour;
conditional only on `hBaseW`. -/
theorem yspace_s1_heuristic_main_div_sieveB_tendsto {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (M : ℝ) (hM : M ≠ 0) (hW : 1 ≤ W)
    (hFs : ∀ i, ContDiff ℝ 1 (Fs i))
    (hsupp : Function.support (fun t => ∏ i, Fs i (t i)) ⊆ Sieve.simplex k)
    (hFsupp : ∀ i : Fin k, ∀ t : ℝ, 1 < t → Fs i t = 0)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N) atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto (fun N : ℕ =>
        (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)
                ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)),
            (∏ i : Fin k,
              S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).1
                * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W ((W * N : ℝ) + 2)).filter
                  (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)) (P i).2)
            * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
          / (Sieve.sieveB W (N : ℝ) ^ k * M))
      atTop (nhds (Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)))) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hφpos : (0 : ℝ) < W.totient := by
    have := Nat.totient_pos.mpr (by omega : 0 < W); exact_mod_cast this
  have hratio_pos : (0 : ℝ) < (W.totient : ℝ) / W := div_pos hφpos hWpos
  have hpk : ((W.totient : ℝ) / W) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hratio_pos)
  -- the box quadform limit, divided by (φW/W)^k
  have hbox := yspace_box_quadform_div_tendsto Fs hFs hsupp hBaseW
  have hdiv := hbox.div_const (((W.totient : ℝ) / W) ^ k)
  have hlim_eq : (((W.totient : ℝ) / W) ^ k
        * Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i))) / ((W.totient : ℝ) / W) ^ k
      = Sieve.mkF_denominator k (fun t => ∏ i, Fs i (t i)) := by
    field_simp
  rw [hlim_eq] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hbig := S1CountReconcile.yr_heuristic_main_eq_quadForm_product k Fs H b W
    ((W * N : ℝ) + 2) M N (by positivity) hW hN2 (le_refl _) hFsupp
  rw [hbig]
  have hsB : Sieve.sieveB W (N : ℝ) ^ k = ((W.totient : ℝ) / W) ^ k * (Real.log N) ^ k := by
    rw [Sieve.sieveB, mul_pow]
  rw [hsB]
  have hlogk : (Real.log N) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hlogN)
  field_simp

end BoundedGaps.S1MainLimit
