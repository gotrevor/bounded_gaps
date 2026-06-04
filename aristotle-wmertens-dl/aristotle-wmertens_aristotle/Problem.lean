import Mathlib

open scoped BigOperators

/-!
# Riemann-sum convergence for the `1/n` log-weight (analytic heart of GPY sub-step (c))

The GPY/Maynard sieve main term needs the WEIGHTED Mertens asymptotic
`∑_{d≤R} (μ²(d)/φ(d))·F(log d / log R) ∼ (∫₀¹ F)·log R`. By Abel summation against the
sharp Mertens asymptotic `∑_{d≤t} μ²/φ ∼ log t` (already proved, axiom-clean), this reduces
to the **model case** where the arithmetic weight is replaced by its average `1/n`:

  `(1 / log R) · ∑_{n=2}^{⌊R⌋} (1/n)·F(log n / log R)  →  ∫₀¹ F(u) du`   as `R → ∞`.

This is a pure real-analysis Riemann-sum statement (no number theory): with the substitution
`u = log n / log R` (so `Δu ≈ 1/(n log R)`), the sum is a Riemann sum of `F` over `[0,1]`.

## Strategy
Compare the sum to the integral `∫_2^R (1/t) F(log t / log R) dt`. Substitute `u = log t/log R`
(`du = dt/(t log R)`): the integral equals `log R · ∫_{log 2/log R}^{1} F(u) du`, and dividing by
`log R` gives `∫_{log2/logR}^1 F → ∫₀¹ F` (lower limit → 0). The sum-vs-integral error is
`O(1/log R) → 0` because `t ↦ (1/t)F(log t/log R)` has bounded variation on `[2,R]`
(`F` continuous on the compact `[0,1]`, so bounded and uniformly continuous; the monotone
`1/t` factor controls the comparison — `AntitoneOn.sum_le_integral_Ico` / `MonotoneOn` sandwich,
plus uniform continuity of `F` to absorb the sample-point error). Keep `#print axioms` clean
(only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
-/

namespace WMertens

set_option maxHeartbeats 800000 in

/-
**Riemann-sum convergence for the `1/n` log-weight.** For `F` continuous on `[0,1]`,
`(∑_{n=2}^{R} (1/n)·F(log n/log R)) / log R → ∫₀¹ F`.
-/
theorem riemann_sum_log_weight (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc (0:ℝ) 1)) :
    Filter.Tendsto
      (fun R : ℕ =>
        (∑ n ∈ Finset.Icc 2 R, F (Real.log n / Real.log R) / (n : ℝ)) / Real.log R)
      Filter.atTop (nhds (∫ u in (0:ℝ)..1, F u)) := by
  -- Write S_R = T_R + E_R where:
  -- - T_R = ∑_{n=2}^R F(logn/logR) · (logn - log(n-1))/logR  (this is a Riemann sum for ∫₀¹ F)
  -- - E_R = (1/logR) · ∑_{n=2}^R F(logn/logR) · (1/n - (logn - log(n-1)))
  set S := fun R : ℕ => (∑ n ∈ Finset.Icc 2 R, F (Real.log (n : ℝ) / Real.log R) / (n : ℝ)) / Real.log R
  set T := fun R : ℕ => (∑ n ∈ Finset.Icc 2 R, F (Real.log (n : ℝ) / Real.log R) * (Real.log n - Real.log (n - 1)) / Real.log R)
  set E := fun R : ℕ => (1 / Real.log R) * (∑ n ∈ Finset.Icc 2 R, F (Real.log (n : ℝ) / Real.log R) * (1 / (n : ℝ) - (Real.log n - Real.log (n - 1))));
  -- Show that |E_R| → 0 as R → ∞.
  have hE : Filter.Tendsto E Filter.atTop (nhds 0) := by
    -- For n ≥ 2: 1/n ≤ log(n/(n-1)) ≤ 1/(n-1), so |1/n - log(n/(n-1))| ≤ 1/(n(n-1))
    have h_bound : ∀ n : ℕ, 2 ≤ n → |(1 / (n : ℝ)) - (Real.log n - Real.log (n - 1))| ≤ 1 / (n * (n - 1) : ℝ) := by
      intro n hn
      have h_log_bound : Real.log n - Real.log (n - 1) ≤ 1 / (n - 1 : ℝ) ∧ Real.log n - Real.log (n - 1) ≥ 1 / (n : ℝ) := by
        constructor;
        · rw [ ← Real.log_div ( by positivity ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] ) ];
          exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by positivity ) ( by norm_num; linarith ) ) ) ( by rw [ div_sub_one, div_le_div_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast ] );
        · -- By the Mean Value Theorem, there exists some $c \in (n-1, n)$ such that $\log n - \log (n-1) = \frac{1}{c}$.
          obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (n - 1 : ℝ) n, Real.log n - Real.log (n - 1) = 1 / c := by
            have := exists_deriv_eq_slope Real.log ( show ( n : ℝ ) - 1 < n by norm_num );
            exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by norm_num at *; linarith ⟩;
          exact hc.2.symm ▸ one_div_le_one_div_of_le ( by linarith [ hc.1.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( by linarith [ hc.1.2 ] );
      rw [ abs_le ] ; constructor <;> rcases n with ( _ | _ | n ) <;> norm_num at *; all_goals nlinarith [ inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 + 1 ), mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 + 1 ≠ 0 ) ];
    -- Since $\sum_{n=2}^R \frac{1}{n(n-1)}$ is a telescoping series, it converges to $1$.
    have h_telescope : ∀ R : ℕ, 2 ≤ R → ∑ n ∈ Finset.Icc 2 R, (1 / (n * (n - 1) : ℝ)) ≤ 1 := by
      -- Notice that $\sum_{n=2}^R \frac{1}{n(n-1)}$ is a telescoping series.
      have h_telescope : ∀ R : ℕ, 2 ≤ R → ∑ n ∈ Finset.Icc 2 R, (1 / (n * (n - 1) : ℝ)) = 1 - 1 / (R : ℝ) := by
        intro R hR; induction hR <;> simp_all +decide [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring;
        rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Finset.Ioc 1 _, _ = _› ] ; norm_num ; ring;
        -- Combine and simplify the terms on the left-hand side.
        field_simp
        ring;
      exact fun R hR => h_telescope R hR ▸ sub_le_self _ ( by positivity );
    -- Since $|F(x)| \leq M$ for some $M$ and all $x \in [0, 1]$, we have $|E_R| \leq \frac{M}{\log R}$.
    obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Icc 0 1, |F x| ≤ M := by
      exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) hF
    have hE_bound : ∀ R : ℕ, 2 ≤ R → |E R| ≤ M / Real.log R := by
      intros R hR
      have hE_bound_step : |∑ n ∈ Finset.Icc 2 R, F (Real.log (n : ℝ) / Real.log R) * (1 / (n : ℝ) - (Real.log n - Real.log (n - 1)))| ≤ M * ∑ n ∈ Finset.Icc 2 R, (1 / (n * (n - 1) : ℝ)) := by
        rw [ Finset.mul_sum _ _ _ ];
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rw [ abs_mul ] ; exact mul_le_mul ( hM _ ⟨ div_nonneg ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ), div_le_one_of_le₀ ( Real.log_le_log ( by norm_num; linarith [ Finset.mem_Icc.mp hi ] ) ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ⟩ ) ( h_bound i ( Finset.mem_Icc.mp hi |>.1 ) ) ( by positivity ) ( by linarith [ abs_le.mp ( hM ( Real.log i / Real.log R ) ⟨ div_nonneg ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ), div_le_one_of_le₀ ( Real.log_le_log ( by norm_num; linarith [ Finset.mem_Icc.mp hi ] ) ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ) ⟩ ) ] ) );
      simp +zetaDelta at *;
      rw [ abs_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ; exact mul_le_mul_of_nonneg_left ( hE_bound_step.trans ( mul_le_of_le_one_right ( show 0 ≤ M by exact le_trans ( abs_nonneg _ ) ( hM 0 ( by norm_num ) ( by norm_num ) ) ) ( h_telescope R hR ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) ) |> le_trans <| by ring_nf; norm_num;
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, hE_bound ⟩ ) ( tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
  -- Show that T_R → ∫₀¹ F as R → ∞.
  have hT : Filter.Tendsto T Filter.atTop (nhds (∫ u in (0 : ℝ)..1, F u)) := by
    -- By uniform continuity, for each n: |F(u_n)(u_n-u_{n-1}) - ∫_{u_{n-1}}^{u_n} F| ≤ ε(u_n-u_{n-1})
    have h_uniform : ∀ ε > 0, ∃ N : ℕ, ∀ R ≥ N, ∀ n ∈ Finset.Icc 2 R, |F (Real.log n / Real.log R) * (Real.log n - Real.log (n - 1)) / Real.log R - ∫ u in (Real.log (n - 1) / Real.log R)..Real.log n / Real.log R, F u| ≤ ε * (Real.log n - Real.log (n - 1)) / Real.log R := by
      -- By uniform continuity, for each n: |F(u_n)(u_n-u_{n-1}) - ∫_{u_{n-1}}^{u_n} F| ≤ ε(u_n-u_{n-1}) for sufficiently large R.
      intros ε hεpos
      obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| < δ → |F x - F y| < ε := by
        have := Metric.uniformContinuousOn_iff.mp ( isCompact_Icc.uniformContinuousOn_of_continuous hF ) ε hεpos; aesop;
      -- Choose N such that for all R ≥ N, the mesh of the partition is less than δ.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ R ≥ N, ∀ n ∈ Finset.Icc 2 R, |Real.log n / Real.log R - Real.log (n - 1) / Real.log R| < δ := by
        -- Choose N such that for all R ≥ N, the mesh of the partition is less than δ. This follows from the fact that $\frac{\log n - \log (n-1)}{\log R} \leq \frac{\log 2}{\log R}$.
        have h_mesh : ∀ R : ℕ, R ≥ 2 → ∀ n ∈ Finset.Icc 2 R, |Real.log n / Real.log R - Real.log (n - 1) / Real.log R| ≤ Real.log 2 / Real.log R := by
          intros R hR n hn
          have h_log_diff : Real.log n - Real.log (n - 1) ≤ Real.log 2 := by
            rw [ ← Real.log_div ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ] ; exact Real.log_le_log ( div_pos ( by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ) ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ) ( by rw [ div_le_iff₀ ] <;> linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Icc.mp hn ] ] ) ;
          rw [ ← sub_div, abs_div, abs_of_nonneg ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) ] ; exact div_le_div_of_nonneg_right ( abs_le.mpr ⟨ by linarith [ Real.log_nonneg <| show ( n :ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hn ], Real.log_le_log ( by norm_num; linarith [ Finset.mem_Icc.mp hn ] ) <| show ( n :ℝ ) - 1 ≤ n by linarith ], by linarith [ Real.log_nonneg <| show ( n :ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hn ], Real.log_le_log ( by norm_num; linarith [ Finset.mem_Icc.mp hn ] ) <| show ( n :ℝ ) - 1 ≤ n by linarith ] ⟩ ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith;
        -- Choose N such that for all R ≥ N, $\frac{\log 2}{\log R} < \delta$.
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ R ≥ N, Real.log 2 / Real.log R < δ := by
          exact Filter.eventually_atTop.mp ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) |> fun h => h.eventually ( gt_mem_nhds hδpos ) );
        exact ⟨ N + 2, fun R hR n hn => lt_of_le_of_lt ( h_mesh R ( by linarith ) n hn ) ( hN R ( by linarith ) ) ⟩;
      use N + 2; intros R hR n hn; specialize hN R ( by linarith ) n hn; simp_all +decide [ mul_div_assoc ] ;
      -- Apply the uniform continuity bound to each term in the sum.
      have h_term_bound : ∀ u ∈ Set.Icc (Real.log (n - 1) / Real.log R) (Real.log n / Real.log R), |F (Real.log n / Real.log R) - F u| ≤ ε := by
        intros u hu; exact le_of_lt (hδ (Real.log n / Real.log R) u (by
        exact div_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) )) (by
        exact div_le_one_of_le₀ ( Real.log_le_log ( by norm_cast; linarith ) ( by norm_cast; linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) )) (by
        exact le_trans ( div_nonneg ( Real.log_nonneg ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) hu.1) (by
        exact hu.2.trans ( div_le_one_of_le₀ ( Real.log_le_log ( by norm_num; linarith ) ( by norm_cast; linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) )) (by
        exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hN, hu.1, hu.2 ], by linarith [ abs_lt.mp hN, hu.1, hu.2 ] ⟩)) ;
      -- Apply the uniform continuity bound to the integral.
      have h_integral_bound : |∫ u in (Real.log (n - 1) / Real.log R)..Real.log n / Real.log R, F (Real.log n / Real.log R) - F u| ≤ ε * ((Real.log n - Real.log (n - 1)) / Real.log R) := by
        rw [ intervalIntegral.integral_of_le ];
        · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
          refine' fun u => ε;
          · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · norm_num;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using h_term_bound u <| Set.Ioc_subset_Icc_self hu;
          · norm_num [ mul_comm, sub_div ];
            rw [ max_eq_left ( sub_nonneg_of_le <| by gcongr <;> linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ) ];
        · gcongr <;> norm_num ; linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ;
      convert h_integral_bound using 1 ; rw [ intervalIntegral.integral_sub ] <;> norm_num ; ring;
      apply_rules [ ContinuousOn.intervalIntegrable, hF ];
      refine' hF.mono _;
      rw [ Set.uIcc_of_le ( div_le_div_of_nonneg_right ( Real.log_le_log ( by norm_num; linarith ) ( by linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ] ; exact Set.Icc_subset_Icc ( div_nonneg ( Real.log_nonneg ( by linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( div_le_one_of_le₀ ( Real.log_le_log ( by norm_num; linarith ) ( by norm_cast; linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ;
    -- Summing these inequalities over n gives |T_R - ∫₀¹ F| ≤ ε.
    have h_sum_uniform : ∀ ε > 0, ∃ N : ℕ, ∀ R ≥ N, |T R - ∫ u in (0 : ℝ)..1, F u| ≤ ε := by
      intros ε hε_pos
      obtain ⟨N, hN⟩ := h_uniform ε hε_pos
      use N + 2
      intro R hR
      have h_sum : ∑ n ∈ Finset.Icc 2 R, ∫ u in (Real.log (n - 1) / Real.log R)..Real.log n / Real.log R, F u = ∫ u in (0 : ℝ)..1, F u := by
        erw [ Finset.sum_Ico_eq_sum_range ];
        convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
        · ring;
        · rw [ eq_div_iff ] <;> norm_num [ show R ≥ 2 by linarith ];
          · rw [ Nat.cast_sub ] <;> push_cast <;> ring ; linarith;
          · exact ⟨ by linarith, by linarith, by linarith ⟩;
        · intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' hF.mono _;
          rw [ Set.uIcc_of_le ( div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ];
          exact Set.Icc_subset_Icc ( div_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( div_le_one_of_le₀ ( Real.log_le_log ( by linarith ) ( by linarith [ show ( R : ℝ ) ≥ k + 2 by norm_cast; omega ] ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) );
      have h_sum_uniform : |T R - ∑ n ∈ Finset.Icc 2 R, ∫ u in (Real.log (n - 1) / Real.log R)..Real.log n / Real.log R, F u| ≤ ε * (∑ n ∈ Finset.Icc 2 R, (Real.log n - Real.log (n - 1))) / Real.log R := by
        rw [ Finset.mul_sum _ _ _, Finset.sum_div ];
        exact le_trans ( by rw [ ← Finset.sum_sub_distrib ] ) ( Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun n hn => hN R ( by linarith ) n hn );
      -- Notice that $\sum_{n=2}^R (\log n - \log (n-1)) = \log R$.
      have h_sum_log : ∑ n ∈ Finset.Icc 2 R, (Real.log n - Real.log (n - 1)) = Real.log R := by
        erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
        · simpa using Finset.sum_range_sub ( fun x => Real.log x ) R;
        · linarith;
      simp_all +decide [ mul_div_assoc ];
      exact h_sum_uniform.trans ( mul_le_of_le_one_right hε_pos.le ( div_self_le_one _ ) );
    exact Metric.tendsto_atTop.mpr fun ε hε => by obtain ⟨ N, hN ⟩ := h_sum_uniform ( ε / 2 ) ( half_pos hε ) ; exact ⟨ N, fun R hR => abs_lt.mpr ⟨ by linarith [ abs_le.mp ( hN R hR ) ], by linarith [ abs_le.mp ( hN R hR ) ] ⟩ ⟩ ;
  convert hT.add hE using 2 <;> norm_num [ div_eq_inv_mul, Finset.mul_sum _ _ _ ] ; ring;
  simp +zetaDelta at *;
  rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_div ] ; congr ; ext ; ring;

end WMertens