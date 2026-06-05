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
import BoundedGaps.Mertens
import BoundedGaps.RiemannSumLogWeight

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

/-- The discrepancy `B(n) = (∑_{k≤n} μ²/φ) − harmonic n` between the arithmetic-weight partial
sum and the harmonic model. This is the partial sum of `a_k = μ²(k)/φ(k) − 1/k`, the difference
appearing in the Abel summation that reduces the weighted Mertens to the `1/n` model. -/
noncomputable def Bdisc (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, gMoebiusSqTotient k) - (harmonic n : ℝ)

@[simp] lemma Bdisc_zero : Bdisc 0 = 0 := by simp [Bdisc]

@[simp] lemma Bdisc_one : Bdisc 1 = 0 := by
  simp only [Bdisc, Finset.Icc_self, Finset.sum_singleton, gMoebiusSqTotient_isMultiplicative.1]
  norm_num [harmonic]

/-- **The discrepancy `B(N) = (∑_{n≤N} μ²/φ) − harmonic N` is `o(log N)`.** Immediate from
sharp Mertens (`G(N)/log N → 1`) and `harmonic N/log N → 1`. This is the null sequence
`ε` (after dividing by `log n`) fed to the weighted Cesàro step. -/
theorem discrepancy_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => Bdisc N / Real.log N) atTop (nhds 0) := by
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

/-! ## The Abel tail estimate (Term 2 of the weighted-Mertens reduction) -/

/-- The majorized weighted average `(∑_{n<N} |B(n)|·(log(n+1)−log n)) / (log N)² → 0`.
This is the analytic heart of the Abel tail: with `ε n = |B(n)/log n| → 0` (sharp Mertens),
weight `w n = log n·(log(n+1)−log n)`, majorant `D N = (log N)²` (telescoping), the
`weighted_avg_majorant_tendsto_zero` lemma applies, and `ε n · w n = |B(n)|·(log(n+1)−log n)`
per term. -/
theorem abel_tail_majorant_tendsto_zero :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n)) / (Real.log N) ^ 2)
      atTop (nhds 0) := by
  -- weight nonneg
  have hw : ∀ n : ℕ, 0 ≤ Real.log n * (Real.log ((n : ℝ) + 1) - Real.log n) := by
    intro n
    refine mul_nonneg (Real.log_natCast_nonneg n) ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast hpos) (by linarith)
      linarith
  -- ε → 0
  have hε : Tendsto (fun n : ℕ => |Bdisc n / Real.log n|) atTop (nhds 0) := by
    have h := discrepancy_div_log_tendsto_zero.abs
    simpa using h
  -- (log N)² → ∞
  have hD : Tendsto (fun N : ℕ => (Real.log N) ^ 2) atTop atTop := by
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have := hlog.atTop_mul_atTop₀ hlog
    simpa [pow_two] using this
  -- majorant
  have hmaj : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, Real.log n * (Real.log ((n : ℝ) + 1) - Real.log n)) ≤ (Real.log N) ^ 2 :=
    Filter.Eventually.of_forall sum_log_mul_log_diff_le_sq
  have key := weighted_avg_majorant_tendsto_zero hw hε hD hmaj
  refine key.congr (fun N => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  -- per term: |B/log n|·(log n·v) = |B|·v
  rcases eq_or_ne (Real.log (n : ℝ)) 0 with h | h
  · rw [h]
    simp only [zero_mul, mul_zero, sub_zero]
    have hn1 : n ≤ 1 := by
      by_contra hc; rw [not_le] at hc
      exact absurd h (ne_of_gt (Real.log_pos (by exact_mod_cast hc)))
    interval_cases n
    · simp
    · simp [Bdisc_one]
  · have hpos : 0 < Real.log (n : ℝ) := lt_of_le_of_ne (Real.log_natCast_nonneg n) (Ne.symm h)
    rw [abs_div, abs_of_pos hpos]
    field_simp

/-- **The Abel tail vanishes (Term 2).** For `F` Lipschitz on `[0,1]` (constant `M`), the Abel
tail of the weighted-Mertens reduction,
`(∑_{1≤n≤N-1} B(n)·(F(log(n+1)/log N) − F(log n/log N))) / log N → 0`.

Bound `|F(log(n+1)/L) − F(log n/L)| ≤ M·(log(n+1)−log n)/L` (Lipschitz; both arguments lie in
`[0,1]` for `1 ≤ n ≤ N−1`), so the tail is `≤ M · (∑_{n<N} |B(n)|·(log(n+1)−log n)) / (log N)²`,
which `→ 0` by `abel_tail_majorant_tendsto_zero`. Squeeze. -/
theorem abel_tail_tendsto_zero {F : ℝ → ℝ} {M : ℝ}
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ M * |x - y|) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 (N - 1), Bdisc n *
          (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N))) / Real.log N)
      atTop (nhds 0) := by
  -- M ≥ 0 (Lipschitz constant; take x = 1, y = 0)
  have hM : 0 ≤ M := by
    have h := hLip 1 (by constructor <;> norm_num) 0 (by constructor <;> norm_num)
    have h2 : (0 : ℝ) ≤ |F 1 - F 0| := abs_nonneg _
    simp only [sub_zero, abs_one, mul_one] at h
    linarith
  -- v n = log(n+1) − log n ≥ 0
  have hvnn : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast hpos) (by linarith)
      linarith
  -- M · Z_N → 0
  have hMZ : Tendsto (fun N : ℕ =>
      M * ((∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n))
        / (Real.log N) ^ 2)) atTop (nhds 0) := by
    have := abel_tail_majorant_tendsto_zero.const_mul M
    simpa using this
  refine squeeze_zero_norm' ?_ hMZ
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  -- per-term Lipschitz bound on the F-increment
  have hDF : ∀ n ∈ Finset.Icc 1 (N - 1),
      |F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N)|
        ≤ M * (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log N := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hltN : n < N := by omega
    have hsuccN : n + 1 ≤ N := by omega
    have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hltN.le
    have hn1R : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hsuccN
    have hlogn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hlogn10 : 0 ≤ Real.log ((n : ℝ) + 1) := by
      have : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
      linarith
    have hb0 : 0 ≤ Real.log n / Real.log N := div_nonneg hlogn0 hLpos.le
    have hb1 : Real.log n / Real.log N ≤ 1 := by
      rw [div_le_one hLpos]; exact Real.log_le_log hnpos hnR
    have ha0 : 0 ≤ Real.log ((n : ℝ) + 1) / Real.log N := div_nonneg hlogn10 hLpos.le
    have ha1 : Real.log ((n : ℝ) + 1) / Real.log N ≤ 1 := by
      rw [div_le_one hLpos]; exact Real.log_le_log (by linarith) hn1R
    have habs : |Real.log ((n : ℝ) + 1) / Real.log N - Real.log n / Real.log N|
        = (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log N := by
      rw [div_sub_div_same, abs_of_nonneg (div_nonneg (hvnn n) hLpos.le)]
    calc |F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N)|
        ≤ M * |Real.log ((n : ℝ) + 1) / Real.log N - Real.log n / Real.log N| :=
          hLip _ ⟨ha0, ha1⟩ _ ⟨hb0, hb1⟩
      _ = M * ((Real.log ((n : ℝ) + 1) - Real.log n) / Real.log N) := by rw [habs]
      _ = M * (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log N := by ring
  -- bound the inner sum
  have hbound : |∑ n ∈ Finset.Icc 1 (N - 1), Bdisc n *
        (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N))|
      ≤ (M / Real.log N)
          * ∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n) := by
    calc |∑ n ∈ Finset.Icc 1 (N - 1), Bdisc n *
            (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N))|
        ≤ ∑ n ∈ Finset.Icc 1 (N - 1), |Bdisc n *
            (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.Icc 1 (N - 1), |Bdisc n| *
            |F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N)| := by
          simp_rw [abs_mul]
      _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1), |Bdisc n|
            * (M * (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log N) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          exact mul_le_mul_of_nonneg_left (hDF n hn) (abs_nonneg _)
      _ = (M / Real.log N)
            * ∑ n ∈ Finset.Icc 1 (N - 1), |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
      _ ≤ (M / Real.log N)
            * ∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hM hLpos.le)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
          · intro x hx
            obtain ⟨_, hx2⟩ := Finset.mem_Icc.mp hx
            exact Finset.mem_range.mpr (by omega)
          · exact mul_nonneg (abs_nonneg _) (hvnn i)
  -- assemble the squeeze bound
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
  have hLne : Real.log N ≠ 0 := hLpos.ne'
  calc |∑ n ∈ Finset.Icc 1 (N - 1), Bdisc n *
          (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N))|
      ≤ (M / Real.log N)
          * ∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n) := hbound
    _ = M * ((∑ n ∈ Finset.range N, |Bdisc n| * (Real.log ((n : ℝ) + 1) - Real.log n))
          / (Real.log N) ^ 2) * Real.log N := by field_simp

/-! ## Abel-summation assembly: the `g`-vs-`1/n` weighted discrepancy vanishes -/

/-- The partial sum of `a_k = μ²(k)/φ(k) − 1/k` is exactly the discrepancy `Bdisc n`. -/
lemma sum_sub_eq_Bdisc (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (gMoebiusSqTotient k - 1 / (k : ℝ))) = Bdisc n := by
  rw [Finset.sum_sub_distrib, Bdisc]
  congr 1
  rw [harmonic_eq_sum_Icc]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => by rw [one_div])

/-- **The weighted `g`-vs-`1/n` discrepancy vanishes after `/ log N`.** For `F` Lipschitz on
`[0,1]`,
`(∑_{1≤n≤N} (μ²(n)/φ(n) − 1/n)·F(log n/log N)) / log N → 0`.

This is the Abel-summation reduction: by `abel_summation_identity`, the sum equals
`Bdisc N · F(1) − (Abel tail)`; dividing by `log N`, the first term `→ F(1)·0` (sharp Mertens,
`discrepancy_div_log_tendsto_zero`) and the second `→ 0` (`abel_tail_tendsto_zero`). -/
theorem discrepancy_weighted_tendsto_zero {F : ℝ → ℝ} {M : ℝ}
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ M * |x - y|) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, (gMoebiusSqTotient n - 1 / (n : ℝ)) * F (Real.log n / Real.log N))
          / Real.log N) atTop (nhds 0) := by
  -- target limit: F 1 · (Bdisc N/log N) − (Abel tail/log N) → F 1·0 − 0 = 0
  have hlim : Tendsto (fun N : ℕ =>
      F 1 * (Bdisc N / Real.log N)
        - (∑ n ∈ Finset.Icc 1 (N - 1), Bdisc n *
            (F (Real.log ((n : ℝ) + 1) / Real.log N) - F (Real.log n / Real.log N)))
          / Real.log N) atTop (nhds 0) := by
    have h1 := discrepancy_div_log_tendsto_zero.const_mul (F 1)
    have h2 := abel_tail_tendsto_zero (F := F) (M := M) hLip
    have := h1.sub h2
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  -- Abel summation identity for a k = g k − 1/k, w m = F(log m/log N)
  have hAbel := BoundedGaps.Mertens.abel_summation_identity N
    (fun k => gMoebiusSqTotient k - 1 / (k : ℝ))
    (fun m => F (Real.log m / Real.log N))
  -- replace the target numerator by the Abel RHS, then simplify
  rw [hAbel]
  simp only [div_self hLpos.ne']
  rw [sum_sub_eq_Bdisc N, sub_div, mul_comm (Bdisc N) (F 1), mul_div_assoc]
  congr 1
  -- tail terms: ∑ (Bdisc k)·(F(log(k+1)/logN) − F(log k/logN))
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sum_sub_eq_Bdisc k]
  push_cast
  ring

/-! ## The weighted Mertens asymptotic (modulo the Riemann-sum model limit) -/

/-- **Weighted Mertens, conditional on the `1/n` Riemann-sum model limit.** For `F` Lipschitz
on `[0,1]`, IF the model average converges,
`(∑_{2≤n≤N} F(log n/log N)/n) / log N → ∫₀¹ F` (the pure analysis statement
`WMertens.riemann_sum_log_weight`, on Aristotle), THEN the full weighted Mertens holds:
`(∑_{1≤n≤N} (μ²(n)/φ(n))·F(log n/log N)) / log N → ∫₀¹ F`.

Proof: `g·F = (1/n)·F + (g − 1/n)·F`. The `(1/n)` part is the model average (plus the bounded
`n=1` term `F 0 / log N → 0`); the discrepancy part `→ 0` by `discrepancy_weighted_tendsto_zero`. -/
theorem weighted_mertens_of_riemann {F : ℝ → ℝ} {M : ℝ}
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ M * |x - y|)
    (hRiemann : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, F (Real.log n / Real.log N) / (n : ℝ)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u))) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n * F (Real.log n / Real.log N)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the bounded n=1 boundary term vanishes
  have hF0 : Tendsto (fun N : ℕ => F 0 / Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  -- the `1/n` model average → ∫₀¹ F
  have hModel : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) * F (Real.log n / Real.log N)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u)) := by
    have hsum := hF0.add hRiemann
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp), add_div]
    congr 1
    · simp
    · rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [one_div_mul_eq_div]
  -- discrepancy part → 0
  have hDisc := discrepancy_weighted_tendsto_zero (F := F) (M := M) hLip
  -- combine
  have := hModel.add hDisc
  rw [add_zero] at this
  refine this.congr (fun N => ?_)
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

/-! ## The capstone, modulo the single Riemann-sum analytic axiom -/

/-- **The `1/n` Riemann-sum model limit** (pure real analysis, no number theory):
`(∑_{2≤n≤N} F(log n/log N)/n) / log N → ∫₀¹ F` for `F` continuous on `[0,1]`.

The substitution `u = log n/log N` turns the log-weighted sum into a Riemann sum of `F` over
`[0,1]`. This is the single analytic ingredient of the weighted Mertens asymptotic (front #4).
**PROVED** (was a disclosed axiom): proof produced by Aristotle (`930e468a`), verified
`#print axioms` clean in our v4.29.1 kernel and ported to `BoundedGaps.WeightedMertens.Riemann`
(`BoundedGaps/RiemannSumLogWeight.lean`). So `weighted_mertens` is now fully axiom-clean. -/
theorem riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, F (Real.log n / Real.log N) / (n : ℝ)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u)) :=
  Riemann.riemann_sum_log_weight F hF

/-- **Consistency check for `riemann_sum_log_weight` (the `F ≡ 1` case), proved axiom-free.**
`(∑_{2≤n≤N} 1/n) / log N → 1 = ∫₀¹ 1`. Since `∑_{2≤n≤N} 1/n = harmonic N − 1`, this is
`harmonic_div_log_tendsto_one` minus `1/log N → 0`. Validates that the disclosed axiom's statement
is not vacuous / mis-stated at its simplest instance. -/
theorem riemann_sum_const_one :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n : ℝ)) / Real.log N) atTop (nhds 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heq : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n : ℝ)) = (harmonic N : ℝ) - 1 := by
    intro N hN
    have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hH : (harmonic N : ℝ) = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    rw [hH, hins, Finset.sum_insert (by simp)]; simp
  have hbase : Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N - 1 / Real.log N)
      atTop (nhds 1) := by
    have h := harmonic_div_log_tendsto_one.sub ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
    simpa using h
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← sub_div, ← heq N hN]

/-- **Weighted Mertens asymptotic** (GPY/Maynard sieve main term, 1-D, sub-step (c)).
For `F` Lipschitz and continuous on `[0,1]` (in particular any `ContDiff` `F`),
`(∑_{1≤n≤N} (μ²(n)/φ(n))·F(log n/log N)) / log N → ∫₀¹ F`.

Rests on the single analytic axiom `riemann_sum_log_weight` (Aristotle); the arithmetic content
— the Abel-summation reduction against sharp Mertens — is axiom-free
(`weighted_mertens_of_riemann`). -/
theorem weighted_mertens {F : ℝ → ℝ} {M : ℝ}
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ M * |x - y|)
    (hCont : ContinuousOn F (Set.Icc (0 : ℝ) 1)) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n * F (Real.log n / Real.log N)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u)) :=
  weighted_mertens_of_riemann hLip (riemann_sum_log_weight F hCont)

/-- **Weighted Mertens for a `C¹` weight** (the form the GPY/Maynard sieve actually uses, where
the cutoff `F` is smooth). For `ContDiff ℝ 1 F`,
`(∑_{1≤n≤N} (μ²(n)/φ(n))·F(log n/log N)) / log N → ∫₀¹ F`. The Lipschitz constant comes from the
mean-value theorem with the derivative bounded on the compact `[0,1]`. -/
theorem weighted_mertens_of_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n * F (Real.log n / Real.log N)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u)) := by
  have hCont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := hF.continuous.continuousOn
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hF.continuous_deriv_one.continuousOn)
  have hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |F x - F y| ≤ C * |x - y| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Icc (0 : ℝ) 1) (C := C)
      (fun z _ => (hF.differentiable (by norm_num)).differentiableAt) hC (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using h
  exact weighted_mertens hLip hCont

/-- **Path-Y leaf-1 analytic core (1-D, `W = 1`, singular series `𝔖 = 1`).** Maynard's diagonal
Selberg main term in `y_r`-space (`S1Summation2`): for `F` of class `C¹`, the `(μ²/φ)`-weighted sum
of `F²` over `r ≤ N` has the sharp asymptotic
`(∑_{r≤N} (μ²(r)/φ(r))·F(log r/log N)²) / log N → ∫₀¹ F²`.

This is the **`∫₀¹ F²` constant** the `s1` axiom advertises (`mkF_denominator` at `k = 1`), obtained
**contour-free** by `weighted_mertens` (itself `SharpMertens.sharp_mertens_unconditional` ⊗ the
`1/n`-Riemann model) applied to the `C¹` weight `F²`. Per the harvested GPY findings (Path Y), the
`(r,W)=1` restriction / `φ(W)/W` factor of the general `W`-trick is sieve-normalisation bookkeeping
(folded into `B = (φ(W)/W)·log x`), NOT part of this analytic core. The `y_r`-space `∫F²` (vs the
`d`-space `∫F'²`) is exactly the convention under which the `s1` constant is correct as stated. -/
theorem weighted_mertens_sq {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n * F (Real.log n / Real.log N) ^ 2) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u ^ 2)) :=
  weighted_mertens_of_contDiff (hF.pow 2)

end BoundedGaps.WeightedMertens
