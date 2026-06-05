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

end BoundedGaps.S1DiagonalSize
