/-
# Weighted Mertens (GPY/Maynard sieve main term, sub-step (c), front #4)

The GPY/Maynard sieve main term needs the **weighted Mertens asymptotic**
`∑_{d≤R} (μ²(d)/φ(d))·F(log d / log R) ∼ (∫₀¹ F)·log R`.

Strategy (Abel summation against the sharp Mertens asymptotic, which is already
proved axiom-clean as `BoundedGaps.SharpMertens.sharp_mertens_unconditional`):

* The arithmetic weight `g = μ²/φ` and the model weight `1/n` have the SAME partial
  sums up to `o(log N)`: `G(N) := ∑_{n≤N} g(n) ∼ log N` (sharp Mertens) and the
  harmonic partial sum `harmonic N ∼ log N` (mathlib). Hence `B(N) := G(N) − harmonic N
  = o(log N)`.
* By (integral) Abel summation, `∑ g·F` and the model `∑ (1/n)·F` differ by a term
  governed by `B(⌊t⌋)`, which is `o(log N)`.  The analytic heart of that estimate is a
  **weighted Cesàro statement**: a divergent-weight average of a null sequence is null.
* The model sum `(∑_{n≤R}(1/n)·F(log n/log R))/log R → ∫₀¹ F` is the pure Riemann-sum
  limit (`WMertens.riemann_sum_log_weight`, on Aristotle).

This file collects the *fully-proved, reusable* analytic bricks for that programme:
the harmonic ratio limit and the weighted Cesàro lemma. The Abel-summation assembly
and the Riemann-sum model limit are tracked separately.
-/
import Mathlib
import BoundedGaps.SharpMertens

open scoped BigOperators
open Filter Topology
open BoundedGaps.SingularSeries

namespace BoundedGaps.WeightedMertens

/-! ## Harmonic partial sum ∼ log -/

/-- `harmonic N / log N → 1`. Immediate from the mathlib sandwich
`log (N+1) ≤ harmonic N ≤ 1 + log N` (`Mathlib.NumberTheory.Harmonic.Bounds`):
`harmonic N − log N ∈ [0, 1]` is bounded while `log N → ∞`. -/
theorem harmonic_div_log_tendsto_one :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (nhds 1) := by
  -- write `harmonic N / log N = 1 + (harmonic N - log N)/log N` and show the remainder → 0
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the remainder `r N = (harmonic N - log N)/log N` is squeezed between `0` and `1/log N`
  have hrem : Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log N) / Real.log N)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (nhds 0) := by
      simp only [one_div]
      exact hlog.inv_tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · -- 0 ≤ remainder eventually
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hlogpos : 0 < Real.log N := Real.log_pos hN1
      have h1 : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
        have := log_add_one_le_harmonic N; rwa [Nat.cast_add, Nat.cast_one] at this
      have h2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      apply div_nonneg (by linarith) hlogpos.le
    · -- remainder ≤ 1/log N eventually
      filter_upwards [eventually_gt_atTop 1] with N hN
      have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hlogpos : 0 < Real.log N := Real.log_pos hN1
      have h3 : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
      rw [div_le_div_iff₀ hlogpos hlogpos]
      nlinarith [h3, hlogpos]
  -- now `harmonic N / log N = 1 + remainder` eventually, and `1 + remainder → 1`
  have : Tendsto (fun N : ℕ => 1 + ((harmonic N : ℝ) - Real.log N) / Real.log N)
      atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hrem
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos hN1
  field_simp
  ring

/-! ## Weighted Cesàro: a divergent-weight average of a null sequence is null -/

/-- **Weighted Cesàro for a null sequence.** If `ε n → 0`, the weights `w n ≥ 0`, and the
partial sums `∑_{n<N} w n → ∞`, then the weighted average
`(∑_{n<N} ε n · w n)/(∑_{n<N} w n) → 0`.

This is the analytic heart of the Abel-summation step in the weighted Mertens asymptotic:
with `ε n = B(n)/log n → 0` (`B = G − harmonic = o(log)`) and `w n = (log n)/n` (the
`∑ log n/n` weights), it kills the `g`-vs-`1/n` discrepancy. -/
theorem weighted_cesaro_tendsto_zero {ε w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hε : Tendsto ε atTop (nhds 0))
    (hW : Tendsto (fun N => ∑ n ∈ Finset.range N, w n) atTop atTop) :
    Tendsto
      (fun N => (∑ n ∈ Finset.range N, ε n * w n) / (∑ n ∈ Finset.range N, w n))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- choose M so that |ε n| < δ/2 for n ≥ M
  rw [Metric.tendsto_atTop] at hε
  obtain ⟨M, hM⟩ := hε (δ / 2) (by linarith)
  -- the fixed head constant
  set C : ℝ := |∑ n ∈ Finset.range M, ε n * w n| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  -- choose N₁ so that the weight sum exceeds B := 2C/δ + 1 (hence is positive and C/W < δ/2)
  set B : ℝ := 2 * C / δ + 1 with hB
  have hBpos : 0 < B := by positivity
  have hev : ∀ᶠ N in atTop, B < ∑ n ∈ Finset.range N, w n := hW.eventually_gt_atTop B
  rw [eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  refine ⟨max M N₁, fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) hN
  -- abbreviations
  set S : ℝ := ∑ n ∈ Finset.range N, ε n * w n with hS
  set W : ℝ := ∑ n ∈ Finset.range N, w n with hWdef
  have hWB : B < W := hN₁ N hNN₁
  have hWpos : 0 < W := lt_trans hBpos hWB
  -- split S = head + tail
  have hsplit : S = (∑ n ∈ Finset.range M, ε n * w n) + ∑ n ∈ Finset.Ico M N, ε n * w n := by
    rw [hS, ← Finset.sum_range_add_sum_Ico _ hNM]
  -- tail bound: |∑_{Ico} ε·w| ≤ (δ/2)·W
  have htail : |∑ n ∈ Finset.Ico M N, ε n * w n| ≤ (δ / 2) * W := by
    calc |∑ n ∈ Finset.Ico M N, ε n * w n|
        ≤ ∑ n ∈ Finset.Ico M N, |ε n * w n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.Ico M N, |ε n| * w n := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [abs_mul, abs_of_nonneg (hw n)]
      _ ≤ ∑ n ∈ Finset.Ico M N, (δ / 2) * w n := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            have : |ε n| ≤ δ / 2 := by
              have := hM n (Finset.mem_Ico.mp hn).1
              rw [Real.dist_eq, sub_zero] at this
              exact this.le
            exact mul_le_mul_of_nonneg_right this (hw n)
      _ = (δ / 2) * ∑ n ∈ Finset.Ico M N, w n := by rw [Finset.mul_sum]
      _ ≤ (δ / 2) * W := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            rw [hWdef]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
            · intro i _ _; exact hw i
  -- assemble: |S| ≤ C + (δ/2)·W
  have hSbound : |S| ≤ C + (δ / 2) * W := by
    rw [hsplit]
    calc |(∑ n ∈ Finset.range M, ε n * w n) + ∑ n ∈ Finset.Ico M N, ε n * w n|
        ≤ |∑ n ∈ Finset.range M, ε n * w n| + |∑ n ∈ Finset.Ico M N, ε n * w n| := abs_add_le _ _
      _ ≤ C + (δ / 2) * W := by rw [← hC]; linarith [htail]
  -- C < (δ/2)·W since W > B = 2C/δ + 1
  have hCW : C < (δ / 2) * W := by
    have h1 : 2 * C / δ < W := lt_trans (by linarith) hWB
    rw [div_lt_iff₀ hδ] at h1
    nlinarith [h1, hδ]
  -- final distance bound
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hWpos]
  rw [div_lt_iff₀ hWpos]
  calc |S| ≤ C + (δ / 2) * W := hSbound
    _ < δ * W := by linarith [hCW]

/-- **Weighted average against a divergent majorant.** A variant of
`weighted_cesaro_tendsto_zero` where the normalizer is an arbitrary `D N → ∞` that
*majorizes* the weight partial sums (`∑_{n<N} w n ≤ D N` eventually). Lets us normalize
by a clean closed-form `D N` (e.g. `(log N)²`) instead of the weight sum itself, sidestepping
a separate divergence lemma for `∑ w`. -/
theorem weighted_avg_majorant_tendsto_zero {ε w D : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hε : Tendsto ε atTop (nhds 0))
    (hD : Tendsto D atTop atTop)
    (hmaj : ∀ᶠ N in atTop, (∑ n ∈ Finset.range N, w n) ≤ D N) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, ε n * w n) / D N) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  rw [Metric.tendsto_atTop] at hε
  obtain ⟨M, hM⟩ := hε (δ / 2) (by linarith)
  set C : ℝ := |∑ n ∈ Finset.range M, ε n * w n| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  -- D N exceeds B := 2C/δ + 1 eventually (hence positive and C/D < δ/2)
  set B : ℝ := 2 * C / δ + 1 with hB
  have hBpos : 0 < B := by positivity
  have hev : ∀ᶠ N in atTop, B < D N := hD.eventually_gt_atTop B
  obtain ⟨N₀, hN₀⟩ := (hev.and hmaj).exists_forall_of_atTop
  refine ⟨max M N₀, fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hDB, hWD⟩ := hN₀ N hNN₀
  set S : ℝ := ∑ n ∈ Finset.range N, ε n * w n with hS
  have hDpos : 0 < D N := lt_trans hBpos hDB
  -- split S = head + tail
  have hsplit : S = (∑ n ∈ Finset.range M, ε n * w n) + ∑ n ∈ Finset.Ico M N, ε n * w n := by
    rw [hS, ← Finset.sum_range_add_sum_Ico _ hNM]
  -- tail bound, finishing on the majorant
  have htail : |∑ n ∈ Finset.Ico M N, ε n * w n| ≤ (δ / 2) * D N := by
    calc |∑ n ∈ Finset.Ico M N, ε n * w n|
        ≤ ∑ n ∈ Finset.Ico M N, |ε n * w n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.Ico M N, |ε n| * w n := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [abs_mul, abs_of_nonneg (hw n)]
      _ ≤ ∑ n ∈ Finset.Ico M N, (δ / 2) * w n := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            have hεn : |ε n| ≤ δ / 2 := by
              have := hM n (Finset.mem_Ico.mp hn).1
              rw [Real.dist_eq, sub_zero] at this; exact this.le
            exact mul_le_mul_of_nonneg_right hεn (hw n)
      _ = (δ / 2) * ∑ n ∈ Finset.Ico M N, w n := by rw [Finset.mul_sum]
      _ ≤ (δ / 2) * D N := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hw i)) hWD
            intro x hx; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
  have hSbound : |S| ≤ C + (δ / 2) * D N := by
    rw [hsplit]
    calc |(∑ n ∈ Finset.range M, ε n * w n) + ∑ n ∈ Finset.Ico M N, ε n * w n|
        ≤ |∑ n ∈ Finset.range M, ε n * w n| + |∑ n ∈ Finset.Ico M N, ε n * w n| := abs_add_le _ _
      _ ≤ C + (δ / 2) * D N := by rw [← hC]; linarith [htail]
  have hCD : C < (δ / 2) * D N := by
    have h1 : 2 * C / δ < D N := lt_trans (by linarith) hDB
    rw [div_lt_iff₀ hδ] at h1; nlinarith [h1, hδ]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hDpos, div_lt_iff₀ hDpos]
  calc |S| ≤ C + (δ / 2) * D N := hSbound
    _ < δ * D N := by linarith [hCD]

/-! ## Discrepancy of the arithmetic weight vs the harmonic model -/

/-- **The discrepancy `B(N) = (∑_{n≤N} μ²/φ) − harmonic N` is `o(log N)`.** Immediate from
sharp Mertens (`G(N)/log N → 1`) and `harmonic N/log N → 1`. This is the null sequence
`ε` (after dividing by `log n`) fed to the weighted Cesàro step. -/
theorem discrepancy_div_log_tendsto_zero :
    Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n) - (harmonic N : ℝ)) / Real.log N)
      atTop (nhds 0) := by
  have h := (BoundedGaps.SharpMertens.sharp_mertens_unconditional).sub harmonic_div_log_tendsto_one
  rw [show (1 : ℝ) - 1 = 0 by norm_num] at h
  exact h.congr (fun N => (sub_div _ _ _).symm)

/-! ## Telescoping majorant for the `log`-difference weight -/

/-- **Telescoping majorant.** With the weight `w n = log n · (log (n+1) − log n)` (the natural
weight for the Abel tail of the weighted Mertens, where `log(n+1)−log n` is the increment of the
sample points `log n / log N`), the partial sums are majorized by `(log N)²`:
`∑_{n<N} log n · (log (n+1) − log n) ≤ (log N)²`. Proof: `log n ≤ log N` on the range, and
`∑_{n<N} (log (n+1) − log n) = log N` telescopes (`log 0 = 0`). -/
theorem sum_log_mul_log_diff_le_sq (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.log n * (Real.log (n + 1) - Real.log n)) ≤ (Real.log N) ^ 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  -- telescoping: ∑ (log(n+1) - log n) = log N - log 0 = log N
  have htel : (∑ n ∈ Finset.range N, (Real.log ((n : ℝ) + 1) - Real.log n)) = Real.log N := by
    have := Finset.sum_range_sub (fun n : ℕ => Real.log n) N
    simpa using this
  calc (∑ n ∈ Finset.range N, Real.log n * (Real.log (n + 1) - Real.log n))
      ≤ ∑ n ∈ Finset.range N, Real.log N * (Real.log (n + 1) - Real.log n) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hnN : (n : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (Nat.lt_of_lt_of_le (Finset.mem_range.mp hn) (le_refl N)).le
        have hdiff : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · subst h0; simp
          · have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
              Real.log_le_log (by exact_mod_cast hpos) (by linarith)
            linarith
        have hlogle : Real.log (n : ℝ) ≤ Real.log N := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · subst h0; simpa using hlogN
          · exact Real.log_le_log (by exact_mod_cast hpos) hnN
        exact mul_le_mul_of_nonneg_right hlogle hdiff
    _ = Real.log N * ∑ n ∈ Finset.range N, (Real.log (n + 1) - Real.log n) := by
        rw [Finset.mul_sum]
    _ = Real.log N * Real.log N := by rw [htel]
    _ = (Real.log N) ^ 2 := by ring

end BoundedGaps.WeightedMertens
