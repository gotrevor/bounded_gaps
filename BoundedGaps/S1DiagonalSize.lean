/-
# The diagonal divisor-sum size is `o(main)` (the unconditional half of the s1 correction bound)

The `s1` correction `correction = o(main)` splits (`SieveExpansion.correction_abs_bound_offdiag`)
into a **diagonal** half `∑_{diag}|coeff|` and an **off-diagonal** half (the BV-gated singular-series
discrepancy). The diagonal half is controlled by the k-D Dirichlet hyperbola count
`Dₖ(N) = #{d ∈ [1,N]^k : ∏ᵢ dᵢ ≤ N}` (via `Sieve.diagonal_weight_le_count`), whose explicit upper
bound `Dₖ(N) ≤ N·(1+log N)^{k-1}` is `Sieve.hyperbola_count_le`.

This file supplies the missing analytic step: `Dₖ(N) = o(N·(log N)^k)` — **unconditional, no BV** —
so that at the level `R = N` with density `M ≍ N`, the diagonal error is `o(M·(log N)^k) = o(main)`.
The proof squeezes `Dₖ(N)/(N·(log N)^k)` between `0` and `(1+log N)^{k-1}/(log N)^k → 0`. The count
is a convention-independent combinatorial object, so this serves both the d-space and y-space
constructions. (The off-diagonal half remains the BV-gated obligation.)
-/
import BoundedGaps.SieveExpansion

open Filter Topology
open scoped BigOperators

namespace BoundedGaps.S1DiagonalSize

/-- The pure real-analysis core: `(1+L)^{k-1}/L^k → 0` as `L → ∞`, for `k ≥ 1`. Writing it as
`(1+1/L)^{k-1}·(1/L)`, the first factor `→ 1` and the second `→ 0`. -/
theorem ratio_log_pow_tendsto_zero {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun L : ℝ => (1 + L) ^ (k - 1) / L ^ k) atTop (nhds 0) := by
  have hinv : Tendsto (fun L : ℝ => 1 / L) atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero
  have hbase : Tendsto (fun L : ℝ => 1 + 1 / L) atTop (nhds 1) := by
    have := hinv.const_add (1 : ℝ); simpa using this
  have hpow : Tendsto (fun L : ℝ => (1 + 1 / L) ^ (k - 1)) atTop (nhds 1) := by
    have := hbase.pow (k - 1); simpa using this
  have hmul : Tendsto (fun L : ℝ => (1 + 1 / L) ^ (k - 1) * (1 / L)) atTop (nhds 0) := by
    have := hpow.mul hinv; simpa using this
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hLne : L ≠ 0 := ne_of_gt hL
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  rw [Nat.add_sub_cancel]
  rw [show (1 + 1 / L) = (L + 1) / L by field_simp, div_pow, pow_succ]
  rw [show (1 + L) = (L + 1) by ring]
  field_simp

/-- The level-indexed form: `(1+log N)^{k-1}/(log N)^k → 0`. Compose `ratio_log_pow_tendsto_zero`
with `log N → ∞`. -/
theorem ratio_loglog_tendsto_zero {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (1 + Real.log N) ^ (k - 1) / (Real.log N) ^ k) atTop (nhds 0) :=
  (ratio_log_pow_tendsto_zero hk).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **The k-D Dirichlet hyperbola count is `o(N·(log N)^k)`.** The diagonal divisor-sum size
`#{d ∈ [1,N]^k : ∏dᵢ ≤ N}`, normalised by `N·(log N)^k`, tends to `0`. Squeeze between `0` and
`(1+log N)^{k-1}/(log N)^k` via `Sieve.hyperbola_count_le` (count `≤ N·(1+log N)^{k-1}`).
This is the convention-independent analytic heart of the **diagonal half** of the `s1` correction
bound `correction = o(main)`: the diagonal weight `∑_{diag}|coeff|` is `≤ C²·count`, and the main
term is `≍ M·(log N)^k` with `M ≍ N` at the level `R = N`, so the diagonal error is `o(main)` —
**unconditional, no BV**. (The off-diagonal half is the BV-gated singular-series discrepancy.) -/
theorem hyperbola_count_div_tendsto_zero {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ =>
        (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
            (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ) / ((N : ℝ) * (Real.log N) ^ k))
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (ratio_loglog_tendsto_zero hk)
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : 1 ≤ N := by omega
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hNR
    have hlogk : (0 : ℝ) < (Real.log N) ^ k := pow_pos hlogN k
    have hcount := Sieve.hyperbola_count_le k hk N hN1
    calc (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
              (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ) / ((N : ℝ) * (Real.log N) ^ k)
        ≤ ((N : ℝ) * (1 + Real.log N) ^ (k - 1)) / ((N : ℝ) * (Real.log N) ^ k) := by
          gcongr
      _ = (1 + Real.log N) ^ (k - 1) / (Real.log N) ^ k :=
          mul_div_mul_left _ _ (ne_of_gt hNpos)

/-- **The hyperbola count is `o(N·(log N)^k)`** (`IsLittleO` form). The `Asymptotics`-flavoured
restatement of `hyperbola_count_div_tendsto_zero`, the form the `s1` correction assembly
(`Sieve.alphaBound_of_heuristic_correction`'s `hcorr` leg) consumes. -/
theorem hyperbola_count_isLittleO {k : ℕ} (hk : 1 ≤ k) :
    Asymptotics.IsLittleO atTop
      (fun N : ℕ =>
        (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
            (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ))
      (fun N : ℕ => (N : ℝ) * (Real.log N) ^ k) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · exact hyperbola_count_div_tendsto_zero hk
  · filter_upwards [eventually_ge_atTop 2] with N hN2 hg
    exfalso
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos hNR
    have : (0 : ℝ) < (N : ℝ) * (Real.log N) ^ k := by positivity
    rw [hg] at this; exact lt_irrefl 0 this

/-- **The scale-trick engine: a fixed polynomial over a super-polynomial scale tends to 0.** If the
scale `M N` eventually dominates `N^{p+1}` (and `c > 0`, `0 ≤ K`), then
`K·N^p / (c·(log N)^k·M N) → 0` — for `N ≥ 3` the `(log N)^k ≥ 1` factor only helps and the ratio is
`≤ K·N^p/(c·N^{p+1}) = (K/c)·(1/N) → 0`. This is the analytic core of the **diagonal leg** of the s1
correction: with the diagonal weight bounded by a fixed polynomial `((C·N³)²)^k = K·N^{6k}`
(`S1Correction.diag_weight_yLambda_le_poly`, independent of the sieve scale `x`) and the lattice
density `M = M(N)` taken `≥ N^{6k+1}` (a polynomially-large scale `x`, permitted by the main-term
chain's free `hcov : (W·N)+2 ≤ x`), the diagonal correction ratio
`(diag weight)/(sieveB^k·M) = (diag weight)/((φW/W)^k·(log N)^k·M) → 0` — **PNT-free, no Möbius
cancellation**. -/
theorem poly_over_scale_tendsto_zero (K c : ℝ) (p k : ℕ) (hc : 0 < c) (hK : 0 ≤ K) {M : ℕ → ℝ}
    (hM : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (p + 1) ≤ M N) :
    Tendsto (fun N : ℕ => K * (N : ℝ) ^ p / (c * (Real.log N) ^ k * M N)) atTop (nhds 0) := by
  have hbound : Tendsto (fun N : ℕ => (K / c) * (1 / (N : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.const_mul (K / c)
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop 3, hM] with N hN3 hMN
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hMpos : (0 : ℝ) < M N := lt_of_lt_of_le (by positivity) hMN
    positivity
  · filter_upwards [eventually_ge_atTop 3, hM] with N hN3 hMN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlogN : (1 : ℝ) ≤ Real.log N := by
      have hmono : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN3)
      have h3 : (1 : ℝ) ≤ Real.log 3 := by
        rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
        exact Real.log_le_log (by positivity) (by have := Real.exp_one_lt_d9; linarith)
      linarith
    have hlogk : (1 : ℝ) ≤ (Real.log N) ^ k := one_le_pow₀ hlogN
    have hMpos : (0 : ℝ) < M N := lt_of_lt_of_le (by positivity) hMN
    have hden_pos : (0 : ℝ) < c * (Real.log N) ^ k * M N := by positivity
    rw [div_le_iff₀ hden_pos]
    have hcalc : (K / c) * (1 / (N : ℝ)) * (c * (Real.log N) ^ k * M N)
        = K * (Real.log N) ^ k * (M N / (N : ℝ)) := by field_simp
    rw [hcalc]
    have hMdiv : (N : ℝ) ^ p ≤ M N / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      calc (N : ℝ) ^ p * (N : ℝ) = (N : ℝ) ^ (p + 1) := by rw [pow_succ]
        _ ≤ M N := hMN
    calc K * (N : ℝ) ^ p
        ≤ K * (Real.log N) ^ k * (M N / (N : ℝ)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hK
          calc (N : ℝ) ^ p ≤ M N / (N : ℝ) := hMdiv
            _ = 1 * (M N / (N : ℝ)) := (one_mul _).symm
            _ ≤ (Real.log N) ^ k * (M N / (N : ℝ)) :=
                mul_le_mul_of_nonneg_right hlogk (div_nonneg (le_of_lt hMpos) (le_of_lt hNpos))
        _ = K * (Real.log N) ^ k * (M N / (N : ℝ)) := rfl

/-- **Leg-1 ratio engine (usable form).** If the diagonal correction `g N` is bounded by a fixed
polynomial `|g N| ≤ K·N^p` (independent of the sieve scale `x`) and the lattice density `M N`
dominates `N^{p+1}` (a polynomially-large scale `x`), then the `B^{+k}·M`-normalised correction
`g N / (c·(log N)^k·M N) → 0`. Squeezes `‖g N / D‖ ≤ K·N^p / D` against `poly_over_scale_tendsto_zero`.
This is the analytic capstone of the **PNT-free diagonal leg** of `hcorr`: instantiate `g` with the
diagonal correction sum (`|g| ≤ ((C·N³)²)^k` via `S1Correction.abs_diag_correction_le_diag_weight` +
`diag_weight_yLambda_le_poly`, `p = 6k`), `c = (φW/W)^k`, and `M N = (⌊2x⌋−(⌈x⌉−1))/W ≥ N^{6k+1}`. No
PNT, no Möbius cancellation. (The off-diagonal leg, where `M` cancels, needs a growing modulus `W`.) -/
theorem diag_ratio_tendsto_zero (K c : ℝ) (p k : ℕ) (hc : 0 < c) (hK : 0 ≤ K)
    {g M : ℕ → ℝ}
    (hg : ∀ᶠ N : ℕ in atTop, |g N| ≤ K * (N : ℝ) ^ p)
    (hM : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (p + 1) ≤ M N) :
    Tendsto (fun N : ℕ => g N / (c * (Real.log N) ^ k * M N)) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (poly_over_scale_tendsto_zero K c p k hc hK hM)
  filter_upwards [hg, hM, eventually_ge_atTop 3] with N hgN hMN hN3
  have hMpos : (0 : ℝ) < M N := lt_of_lt_of_le (by positivity) hMN
  have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hDpos : (0 : ℝ) < c * (Real.log N) ^ k * M N := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hDpos]
  gcongr

end BoundedGaps.S1DiagonalSize
