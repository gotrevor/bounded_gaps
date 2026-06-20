import BoundedGaps.WeightedRiemann2D
import BoundedGaps.PolyaUniform
import BoundedGaps.Mertens
import BoundedGaps.RiemannSumLogWeight
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Reducing the GPY inner-uniform convergence to the pointwise scale-change limit

The 2-D simplex limit `WeightedRiemann2D.weighted_riemann_2d_of_inner` consumes the *inner uniform*
convergence (`huni`): the inner log-sum `(∑_{n≤R/m} G(log n/log R)/n)/log R`, normalized by `log R`,
converges to `Phi G (log m/log R) = ∫₀^{1-log m/log R} G` UNIFORMLY in `m ∈ [2,R]`.

This file reduces that uniform statement to the much cleaner **pointwise** scale-change limit, via
`PolyaUniform.polya_uniform`. The key reparametrisation: with `t = 1 - log m/log R` one has
`m = R^{log m/log R}`, hence the truncation `⌊R/m⌋ = ⌊R^t⌋` *exactly* (`floor_rpow_one_sub`), so the
inner sum is `Ψ G R t` (`Psi` below) at `t = 1 - log m/log R`, and `Phi G (log m/log R) = ∫₀^t G`.
For `G ≥ 0` the `Ψ G R ·` are monotone step functions of `t`, and `t ↦ ∫₀^t G` is continuous, so
Pólya upgrades pointwise to uniform — dodging the hard "boundary regime" (`m` near `R`) entirely.

The single remaining analytic input is the pointwise limit `Ψ G R t → ∫₀^t G` for each fixed
`t ∈ [0,1]` (the classical "fixed-`m` scale change"); everything else is discharged here.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.InnerUniformReduction

open BoundedGaps.WeightedRiemann2D (Phi)

/-- The inner Riemann partial sum truncated at `⌊R^t⌋`, normalized by `log R`. -/
noncomputable def Psi (G : ℝ → ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 ⌊(R : ℝ) ^ t⌋₊, G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R

/-- **Truncation identity.** At the reparametrising exponent `t = 1 - log m/log R`, the real power
`R^t` lands exactly on `R/m`, so its floor is the natural-division truncation `R/m` used by the
inner sum. (For `m = 1`: `t = 1`, `R^1 = R`, `R/1 = R`.) -/
lemma floor_rpow_one_sub (R m : ℕ) (hR : 2 ≤ R) (hm : 1 ≤ m) :
    ⌊(R : ℝ) ^ (1 - Real.log m / Real.log R)⌋₊ = R / m := by
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogR : Real.log R ≠ 0 := ne_of_gt (Real.log_pos hR1)
  have key : (R : ℝ) ^ (1 - Real.log m / Real.log R) = (R : ℝ) / (m : ℝ) := by
    rw [Real.rpow_sub hR0, Real.rpow_one]
    congr 1
    rw [Real.rpow_def_of_pos hR0, mul_comm, div_mul_cancel₀ (Real.log m) hlogR, Real.exp_log hm0]
  rw [key, Nat.floor_div_natCast, Nat.floor_natCast]

/-- **The log-ratio limit `c_R → t`.** For fixed `t > 0`, `log⌊R^t⌋ / log R → t` as `R → ∞`. This is
the scale factor in the pointwise scale-change limit `psi_tendsto` (still on Aristotle): writing
`N = ⌊R^t⌋`, the inner sum normalises by `log R` while the 1-D Riemann limit normalises by `log N`,
and `log N / log R = c_R → t`. Squeeze: `⌊R^t⌋ ≤ R^t` gives `c_R ≤ t`, while `R^t - 1 ≤ ⌊R^t⌋` and
`log(R^t - 1) = t·log R + log(1 - R^{-t})` give the lower bound `t + log(1-R^{-t})/log R → t`
(the error term `→ 0` since the numerator `→ log 1 = 0` and `log R → ∞`). A reusable analysis brick
toward closing leaf 1 in-kernel. -/
lemma tendsto_logFloor_rpow_div (t : ℝ) (ht : 0 < t) :
    Tendsto (fun R : ℕ => Real.log (⌊(R : ℝ) ^ t⌋₊ : ℝ) / Real.log (R : ℝ)) atTop (𝓝 t) := by
  have hlogR_atTop : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun R : ℕ => Real.log (1 - (R : ℝ) ^ (-t)) / Real.log (R : ℝ))
      atTop (𝓝 0) := by
    have hnum : Tendsto (fun R : ℕ => Real.log (1 - (R : ℝ) ^ (-t))) atTop (𝓝 0) := by
      have hpow0 : Tendsto (fun R : ℕ => (R : ℝ) ^ (-t)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop ht).comp tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun R : ℕ => 1 - (R : ℝ) ^ (-t)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub hpow0
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
      simpa [Real.log_one, Function.comp_def] using this
    exact hnum.div_atTop hlogR_atTop
  have hlower : Tendsto
      (fun R : ℕ => t + Real.log (1 - (R : ℝ) ^ (-t)) / Real.log (R : ℝ)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add herr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with R hR2
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
    have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
    have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hR1
    have hRt1 : (1 : ℝ) < (R : ℝ) ^ t :=
      (Real.one_lt_rpow_iff_of_pos hRpos).mpr (Or.inl ⟨hR1, ht⟩)
    have hRtpos : (0 : ℝ) < (R : ℝ) ^ t := by linarith
    have hRneg1 : (R : ℝ) ^ (-t) < 1 := by
      rw [Real.rpow_neg (le_of_lt hRpos)]; exact inv_lt_one_of_one_lt₀ hRt1
    have hRneg_pos : (0 : ℝ) < 1 - (R : ℝ) ^ (-t) := by linarith
    have hfloor_ge : (R : ℝ) ^ t - 1 ≤ (⌊(R : ℝ) ^ t⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((R : ℝ) ^ t); linarith
    have hpos1 : (0 : ℝ) < (R : ℝ) ^ t - 1 := by linarith
    have hfac : (R : ℝ) ^ t * (1 - (R : ℝ) ^ (-t)) = (R : ℝ) ^ t - 1 := by
      rw [mul_sub, mul_one, ← Real.rpow_add hRpos]; simp
    have hlogeq : t * Real.log (R : ℝ) + Real.log (1 - (R : ℝ) ^ (-t))
        = Real.log ((R : ℝ) ^ t - 1) := by
      rw [← Real.log_rpow hRpos t, ← Real.log_mul (ne_of_gt hRtpos) (ne_of_gt hRneg_pos), hfac]
    have hlog_le : Real.log ((R : ℝ) ^ t - 1) ≤ Real.log (⌊(R : ℝ) ^ t⌋₊ : ℝ) :=
      Real.log_le_log hpos1 hfloor_ge
    have hcombine : t + Real.log (1 - (R : ℝ) ^ (-t)) / Real.log (R : ℝ)
        = Real.log ((R : ℝ) ^ t - 1) / Real.log (R : ℝ) := by
      rw [← hlogeq]; field_simp
    rw [hcombine]
    exact div_le_div_of_nonneg_right hlog_le (le_of_lt hlogRpos)
  · filter_upwards [eventually_ge_atTop 2] with R hR2
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
    have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
    have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hR1
    have hRt1 : (1 : ℝ) < (R : ℝ) ^ t :=
      (Real.one_lt_rpow_iff_of_pos hRpos).mpr (Or.inl ⟨hR1, ht⟩)
    have hfloor_pos : (0 : ℝ) < (⌊(R : ℝ) ^ t⌋₊ : ℝ) := by
      have h1 : 1 ≤ ⌊(R : ℝ) ^ t⌋₊ := Nat.le_floor (by exact_mod_cast le_of_lt hRt1)
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have hle : (⌊(R : ℝ) ^ t⌋₊ : ℝ) ≤ (R : ℝ) ^ t := Nat.floor_le (by linarith)
    have hlog_le : Real.log (⌊(R : ℝ) ^ t⌋₊ : ℝ) ≤ Real.log ((R : ℝ) ^ t) :=
      Real.log_le_log hfloor_pos hle
    rw [Real.log_rpow hRpos] at hlog_le
    rw [div_le_iff₀ hlogRpos]
    linarith [hlog_le]

/-- **Harmonic normalisation `(∑_{2≤n≤N} 1/n)/log N → 1`.** The other ingredient of the
`psi_tendsto` drift bound: the harmonic tail over `log N` tends to `1`. From the Euler–Mascheroni
asymptotic `harmonic N - log N → γ` (mathlib `tendsto_harmonic_sub_log`) and
`∑_{2≤n≤N} 1/n = harmonic N - 1`. A reusable analysis brick toward closing leaf 1 in-kernel. -/
lemma tendsto_harmonic_icc2_div_log :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hsum_eq : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n) = (harmonic N : ℝ) - 1 := by
    intro N hN
    have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [BoundedGaps.Mertens.harmonic_eq_icc_sum, hins, Finset.sum_insert (by simp)]; norm_num
  have hden : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log N - 1) / Real.log (N : ℝ))
      atTop (𝓝 0) := (Real.tendsto_harmonic_sub_log.sub tendsto_const_nhds).div_atTop hden
  have hkey : (fun N : ℕ => (∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n) / Real.log (N : ℝ))
      =ᶠ[atTop] (fun N : ℕ => 1 + ((harmonic N : ℝ) - Real.log N - 1) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hne : Real.log (N : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
    rw [hsum_eq N (by omega)]; field_simp; ring
  rw [tendsto_congr' hkey]
  simpa using tendsto_const_nhds.add herr

/-- For `G ≥ 0`, `Ψ G R ·` is monotone on `[0,1]`: increasing `t` only enlarges the truncation
`⌊R^t⌋`, adding nonnegative terms; division by `log R ≥ 0` preserves the order. For `R ≤ 1` the map
is identically `0` (`log R = 0`), hence trivially monotone. -/
lemma psi_monotoneOn (G : ℝ → ℝ) (hG : ∀ x, 0 ≤ G x) (R : ℕ) :
    MonotoneOn (Psi G R) (Set.Icc (0 : ℝ) 1) := by
  rcases Nat.lt_or_ge R 2 with hRlt | hR2
  · -- `R ∈ {0,1}`: `log R = 0`, so `Ψ ≡ 0`.
    have hlog0 : Real.log (R : ℝ) = 0 := by interval_cases R <;> simp
    intro a _ b _ _
    simp [Psi, hlog0]
  · -- `R ≥ 2`.
    have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    have hlogpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    intro a _ b _ hab
    have hpow : (R : ℝ) ^ a ≤ (R : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hR1' hab
    have hsub : Finset.Icc 2 ⌊(R : ℝ) ^ a⌋₊ ⊆ Finset.Icc 2 ⌊(R : ℝ) ^ b⌋₊ :=
      Finset.Icc_subset_Icc_right (Nat.floor_mono hpow)
    have hsum : (∑ n ∈ Finset.Icc 2 ⌊(R : ℝ) ^ a⌋₊, G (Real.log n / Real.log R) / (n : ℝ))
        ≤ (∑ n ∈ Finset.Icc 2 ⌊(R : ℝ) ^ b⌋₊, G (Real.log n / Real.log R) / (n : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => div_nonneg (hG _) (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right hsum (le_of_lt hlogpos)

/-- **Inner-uniform convergence from the pointwise scale-change limit (`G ≥ 0` core).** Given the
*pointwise* limit `Ψ G R t → ∫₀^t G` for every `t ∈ [0,1]` (the classical fixed-`m` scale change),
the inner log-sum converges to `Phi G (log m/log R)` UNIFORMLY in `m ∈ [2,R]` — exactly the `huni`
hypothesis of `WeightedRiemann2D.weighted_riemann_2d_of_inner`.

Proof: `PolyaUniform.polya_uniform` (monotone `Ψ G R ·` + continuous limit `t ↦ ∫₀^t G`) gives
uniformity in the reparametrising variable `t`; instantiate at `t = 1 - log m/log R ∈ [0,1]` and
rewrite via `floor_rpow_one_sub` (`⌊R^t⌋ = R/m`) and `Phi G (log m/log R) = ∫₀^{1-log m/log R} G`.
-/
theorem inner_uniform_of_pointwise_nonneg (G : ℝ → ℝ)
    (hG : ∀ x, 0 ≤ G x) (hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (hptw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => Psi G R t) atTop (𝓝 (∫ y in (0 : ℝ)..t, G y))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
      |(∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R
        - Phi G (Real.log m / Real.log R)| ≤ ε := by
  -- The limit `Φ t = ∫₀^t G` is continuous on the compact `[0,1]`.
  have hΦcont : ContinuousOn (fun t => ∫ y in (0 : ℝ)..t, G y) (Set.Icc (0 : ℝ) 1) := by
    have hint : IntegrableOn G (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hGcont.integrableOn_compact isCompact_Icc
    have := intervalIntegral.continuousOn_primitive_interval hint
    rwa [Set.uIcc_of_le (zero_le_one)] at this
  -- Pólya: uniform convergence in the reparametrising variable `t`.
  have hpoly := BoundedGaps.PolyaUniform.polya_uniform
    (fun t => ∫ y in (0 : ℝ)..t, G y) (Psi G) hΦcont
    (fun R => psi_monotoneOn G hG R) hptw
  intro ε hε
  filter_upwards [hpoly ε hε, eventually_ge_atTop 2] with R hR hR2 m hm
  obtain ⟨hm2, hmR⟩ := Finset.mem_Icc.mp hm
  have hm1 : 1 ≤ m := by omega
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR2)
  have hlogm_nonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hlogm_le : Real.log (m : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hmR)
  -- `t = 1 - log m/log R ∈ [0,1]`.
  have htm_mem : (1 - Real.log m / Real.log R) ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : Real.log m / Real.log R ≤ 1 := by rw [div_le_one hlogRpos]; exact hlogm_le
    have h0 : 0 ≤ Real.log m / Real.log R := div_nonneg hlogm_nonneg (le_of_lt hlogRpos)
    exact ⟨by linarith, by linarith⟩
  -- Rewrite the inner sum / `Phi` into `Ψ` / `Φ` form, then apply the uniform bound.
  have hpsi_eq : Psi G R (1 - Real.log m / Real.log R)
      = (∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R := by
    unfold Psi; rw [floor_rpow_one_sub R m hR2 hm1]
  have hphi_eq : (∫ y in (0 : ℝ)..(1 - Real.log m / Real.log R), G y)
      = Phi G (Real.log m / Real.log R) := rfl
  rw [← hpsi_eq, ← hphi_eq]
  exact hR (1 - Real.log m / Real.log R) htm_mem

/-- **Inner-uniform convergence for arbitrary continuous `G`.** Dropping the `G ≥ 0` restriction of
`inner_uniform_of_pointwise_nonneg` via the positive/negative-part split `G = G⁺ - G⁻` (both
continuous and `≥ 0`). Assumes the pointwise scale-change limit `Ψ H R t → ∫₀^t H` for every
continuous `H` on `[0,1]` (the single remaining analytic input — supplied to `G⁺` and `G⁻`). The
inner sum and `Phi` are linear in the integrand, so the two part-bounds (each `≤ ε/2`) combine by
the triangle inequality. This is exactly `weighted_riemann_2d_of_inner`'s `huni` for general `G`. -/
theorem inner_uniform_of_pointwise (G : ℝ → ℝ) (hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (hptw : ∀ H : ℝ → ℝ, ContinuousOn H (Set.Icc (0 : ℝ) 1) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => Psi H R t) atTop (𝓝 (∫ y in (0 : ℝ)..t, H y))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ m ∈ Finset.Icc 2 R,
      |(∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R
        - Phi G (Real.log m / Real.log R)| ≤ ε := by
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -|a| ≤ a := neg_abs_le a
      have h2 : b ≤ |b| := le_abs_self b
      linarith
    · have h1 : a ≤ |a| := le_abs_self a
      have h2 : -|b| ≤ b := neg_abs_le b
      linarith
  have hGp_cont : ContinuousOn (fun x => max (G x) 0) (Set.Icc (0 : ℝ) 1) :=
    hGcont.sup continuousOn_const
  have hGm_cont : ContinuousOn (fun x => max (-(G x)) 0) (Set.Icc (0 : ℝ) 1) :=
    hGcont.neg.sup continuousOn_const
  have hp := inner_uniform_of_pointwise_nonneg (fun x => max (G x) 0)
    (fun _ => le_max_right _ _) hGp_cont (hptw _ hGp_cont)
  have hm := inner_uniform_of_pointwise_nonneg (fun x => max (-(G x)) 0)
    (fun _ => le_max_right _ _) hGm_cont (hptw _ hGm_cont)
  intro ε hε
  filter_upwards [hp (ε/2) (by linarith), hm (ε/2) (by linarith), eventually_ge_atTop 2]
    with R hRp hRm hR2 m hmem
  obtain ⟨hm2, hmR⟩ := Finset.mem_Icc.mp hmem
  have hboundp := hRp m hmem
  have hboundm := hRm m hmem
  -- `x₀ = 1 - log m/log R ∈ [0,1]`
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hlogm_le : Real.log (m : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmR)
  have hx0_nn : 0 ≤ 1 - Real.log m / Real.log R := by
    have : Real.log m / Real.log R ≤ 1 := by rw [div_le_one hlogRpos]; exact hlogm_le
    linarith
  have hx0_le1 : 1 - Real.log m / Real.log R ≤ 1 := by
    have : 0 ≤ Real.log m / Real.log R := div_nonneg hlogm_nn (le_of_lt hlogRpos)
    linarith
  -- inner sum splits `S = Sp - Sm`
  have hS_split : (∑ n ∈ Finset.Icc 2 (R / m), G (Real.log n / Real.log R) / (n : ℝ))
      = (∑ n ∈ Finset.Icc 2 (R / m), max (G (Real.log n / Real.log R)) 0 / (n : ℝ))
        - (∑ n ∈ Finset.Icc 2 (R / m), max (-(G (Real.log n / Real.log R))) 0 / (n : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← sub_div]
    congr 1
    rcases le_total 0 (G (Real.log n / Real.log R)) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  -- `Phi` splits `Phi G = Phi G⁺ - Phi G⁻`
  have hsub : Set.uIcc (0 : ℝ) (1 - Real.log m / Real.log R) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hx0_nn]; exact Set.Icc_subset_Icc_right hx0_le1
  have hGp_ii : IntervalIntegrable (fun x => max (G x) 0) MeasureTheory.volume 0
      (1 - Real.log m / Real.log R) := (hGp_cont.mono hsub).intervalIntegrable
  have hGm_ii : IntervalIntegrable (fun x => max (-(G x)) 0) MeasureTheory.volume 0
      (1 - Real.log m / Real.log R) := (hGm_cont.mono hsub).intervalIntegrable
  have hPhi_split : Phi G (Real.log m / Real.log R)
      = Phi (fun x => max (G x) 0) (Real.log m / Real.log R)
        - Phi (fun x => max (-(G x)) 0) (Real.log m / Real.log R) := by
    unfold Phi
    rw [← intervalIntegral.integral_sub hGp_ii hGm_ii]
    apply intervalIntegral.integral_congr
    intro y _
    show G y = max (G y) 0 - max (-G y) 0
    rcases le_total 0 (G y) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  -- combine via the triangle inequality (abbreviate the four atomic pieces)
  rw [hS_split, hPhi_split, sub_div]
  set Sp :=
    (∑ n ∈ Finset.Icc 2 (R / m), max (G (Real.log n / Real.log R)) 0 / (n : ℝ)) / Real.log R
  set Sm :=
    (∑ n ∈ Finset.Icc 2 (R / m), max (-(G (Real.log n / Real.log R))) 0 / (n : ℝ)) / Real.log R
  set Pp := Phi (fun x => max (G x) 0) (Real.log m / Real.log R)
  set Pm := Phi (fun x => max (-(G x)) 0) (Real.log m / Real.log R)
  have hre : Sp - Sm - (Pp - Pm) = (Sp - Pp) - (Sm - Pm) := by ring
  rw [hre]
  exact (htri _ _).trans (by linarith [hboundp, hboundm])

/-- **GPY/Maynard 2-D simplex limit, reduced in-kernel to the 1-D pointwise scale-change limit.**
Composing `inner_uniform_of_pointwise` (uniform ⇐ pointwise) with
`WeightedRiemann2D.weighted_riemann_2d_of_inner` (2-D limit ⇐ uniform): the coupled double
log-weighted Riemann sum converges to the iterated simplex integral `∫₀¹ F·(∫₀^{1-x} G)`, assuming
ONLY the 1-D pointwise limit `Ψ H R t → ∫₀^t H` for every continuous `H`. This is exactly the
statement of the deep axiom `WeightedRiemann2D.weighted_riemann_2d` (the Aristotle target), now
reduced — axiom-clean, in our kernel — to a single one-dimensional limit. -/
theorem weighted_riemann_2d_of_psi_pointwise (F G : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (hptw : ∀ H : ℝ → ℝ, ContinuousOn H (Set.Icc (0 : ℝ) 1) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => Psi H R t) atTop (𝓝 (∫ y in (0 : ℝ)..t, H y))) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
            F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log R) ^ 2)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * ∫ y in (0 : ℝ)..(1 - x), G y)) :=
  BoundedGaps.WeightedRiemann2D.weighted_riemann_2d_of_inner F G hF hG
    (inner_uniform_of_pointwise G hG hptw)

/-- **The pointwise scale-change limit.** For `G` continuous on `[0,1]` and fixed `t ∈ [0,1]`, the
truncated log-weighted sum `Ψ G R t → ∫₀^t G` as `R → ∞`. This is the classical "fixed-`m` scale
change", proven here in-kernel from the 1-D limit `riemann_sum_log_weight`. With `N = ⌊R^t⌋` and
`c_R = log N/log R`: `Ψ G R t = c_R · B R`, where `B R → ∫₀¹ G(t·u)du` (the `c_R`-drifted Riemann
sum, equal to the `t`-scaled one up to an error `→ 0` by uniform continuity of `G` plus the bounded
harmonic ratio), and `c_R → t`; finally `t·∫₀¹ G(t·u)du = ∫₀^t G`. Assembles
`tendsto_logFloor_rpow_div` (`c_R → t`) + `tendsto_harmonic_icc2_div_log` + the drift bound. -/
theorem psi_tendsto (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => Psi G R t) atTop (𝓝 (∫ y in (0 : ℝ)..t, G y)) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with hteq | htpos
  · subst hteq
    simp only [Psi]
    have : (fun R : ℕ => (∑ n ∈ Finset.Icc 2 ⌊(R : ℝ) ^ (0:ℝ)⌋₊,
        G (Real.log n / Real.log R) / (n : ℝ)) / Real.log R) = fun _ => 0 := by
      funext R; rw [Real.rpow_zero]; simp
    rw [this]; simpa using tendsto_const_nhds
  · set Ft : ℝ → ℝ := fun u => G (t * u) with hFt
    have hmaps : MapsTo (fun u => t * u) (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
      intro u hu; obtain ⟨hu0, hu1⟩ := hu
      exact ⟨by positivity, by nlinarith⟩
    have hFt_cont : ContinuousOn Ft (Icc (0:ℝ) 1) :=
      hG.comp ((continuous_const.mul continuous_id).continuousOn) hmaps
    set N : ℕ → ℕ := fun R => ⌊(R : ℝ) ^ t⌋₊ with hN
    have hNtop : Tendsto N atTop atTop := by
      have : Tendsto (fun R : ℕ => (R : ℝ) ^ t) atTop atTop :=
        (tendsto_rpow_atTop htpos).comp tendsto_natCast_atTop_atTop
      exact tendsto_nat_floor_atTop.comp this
    have hcR : Tendsto (fun R : ℕ => Real.log (N R : ℝ) / Real.log (R : ℝ)) atTop (𝓝 t) :=
      tendsto_logFloor_rpow_div t htpos
    have hriem : Tendsto (fun R : ℕ =>
        (∑ n ∈ Finset.Icc 2 (N R), Ft (Real.log n / Real.log (N R : ℝ)) / (n : ℝ))
          / Real.log (N R : ℝ)) atTop (𝓝 (∫ u in (0:ℝ)..1, Ft u)) :=
      (BoundedGaps.WeightedMertens.Riemann.riemann_sum_log_weight Ft hFt_cont).comp hNtop
    have hdrift : Tendsto (fun R : ℕ =>
        (∑ n ∈ Finset.Icc 2 (N R),
            (G (Real.log n / Real.log R) - Ft (Real.log n / Real.log (N R : ℝ))) / (n : ℝ))
          / Real.log (N R : ℝ)) atTop (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      have huc : UniformContinuousOn G (Icc (0:ℝ) 1) :=
        isCompact_Icc.uniformContinuousOn_of_continuous hG
      obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1 huc (ε/4) (by linarith)
      have hcR' : ∀ᶠ R : ℕ in atTop, |Real.log (N R : ℝ) / Real.log (R : ℝ) - t| ≤ δ := by
        have := (Metric.tendsto_nhds.1 hcR δ hδ0)
        filter_upwards [this] with R hR; rw [Real.dist_eq] at hR; linarith
      have hharm : ∀ᶠ R : ℕ in atTop,
          (∑ n ∈ Finset.Icc 2 (N R), (1:ℝ)/n) / Real.log (N R : ℝ) ≤ 2 := by
        have h2 := Metric.tendsto_nhds.1 (tendsto_harmonic_icc2_div_log.comp hNtop) 1 (by norm_num)
        filter_upwards [h2] with R hR
        simp only [Function.comp, Real.dist_eq] at hR
        have := abs_lt.1 hR; linarith [this.2]
      filter_upwards [hcR', hharm, hNtop.eventually_ge_atTop 2,
        eventually_ge_atTop 2] with R hcRδ hharmR hNR2 hR2
      have hNR1 : (1:ℝ) < (N R : ℝ) := by exact_mod_cast (by omega : 1 < N R)
      have hlogNRpos : 0 < Real.log (N R : ℝ) := Real.log_pos hNR1
      have hR1 : (1:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 1 < R)
      have hlogRpos : 0 < Real.log (R:ℝ) := Real.log_pos hR1
      have hNRleR : (N R : ℝ) ≤ (R:ℝ) := by
        have h1 : (N R : ℝ) ≤ (R:ℝ)^t := Nat.floor_le (by positivity)
        have h2 : (R:ℝ)^t ≤ (R:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_lt hR1) ht1
        rw [Real.rpow_one] at h2; linarith
      have hterm : ∀ n ∈ Finset.Icc 2 (N R),
          |G (Real.log n / Real.log R) - Ft (Real.log n / Real.log (N R:ℝ))| ≤ ε/4 := by
        intro n hn
        rw [Finset.mem_Icc] at hn; obtain ⟨hn2, hnNR⟩ := hn
        have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
        have hvn0 : 0 ≤ Real.log n / Real.log (N R:ℝ) := by positivity
        have hvn1 : Real.log n / Real.log (N R:ℝ) ≤ 1 := by
          rw [div_le_one hlogNRpos]
          exact Real.log_le_log (by positivity) (by exact_mod_cast hnNR)
        have hcR1 : Real.log (N R:ℝ)/Real.log (R:ℝ) ≤ 1 := by
          rw [div_le_one hlogRpos]; exact Real.log_le_log (by positivity) hNRleR
        have hcR0 : 0 ≤ Real.log (N R:ℝ)/Real.log (R:ℝ) := by positivity
        have hrw : Real.log (n:ℝ)/Real.log (R:ℝ)
            = (Real.log (N R:ℝ)/Real.log (R:ℝ)) * (Real.log n/Real.log (N R:ℝ)) := by
          field_simp
        set cR := Real.log (N R:ℝ)/Real.log (R:ℝ)
        set vn := Real.log (n:ℝ)/Real.log (N R:ℝ)
        have hmemx : cR * vn ∈ Icc (0:ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul hcR1 hvn1 hvn0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        have hmemy : t * vn ∈ Icc (0:ℝ) 1 :=
          ⟨by positivity, by nlinarith [mul_le_mul ht1 hvn1 hvn0 (by norm_num : (0:ℝ) ≤ 1)]⟩
        have hdist : dist (cR * vn) (t * vn) ≤ δ := by
          rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg hvn0]
          calc |cR - t| * vn ≤ δ * 1 :=
                mul_le_mul hcRδ hvn1 hvn0 (le_of_lt hδ0)
            _ = δ := by ring
        have hgg := hδ _ hmemx _ hmemy hdist
        rw [Real.dist_eq] at hgg
        rw [hrw]; exact hgg
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogNRpos, div_lt_iff₀ hlogNRpos]
      have hsum_abs :
          |∑ n ∈ Finset.Icc 2 (N R),
              (G (Real.log n/Real.log R) - Ft (Real.log n/Real.log (N R:ℝ)))/(n:ℝ)|
            ≤ (ε/4) * (∑ n ∈ Finset.Icc 2 (N R), (1:ℝ)/n) := by
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        rw [abs_div, Nat.abs_cast]
        rw [show (ε/4)*((1:ℝ)/n) = (ε/4)/n by ring]
        exact div_le_div_of_nonneg_right (hterm n hn) (by positivity)
      have hharm' : (∑ n ∈ Finset.Icc 2 (N R), (1:ℝ)/n) ≤ 2 * Real.log (N R:ℝ) := by
        rw [← div_le_iff₀ hlogNRpos]; exact hharmR
      calc |∑ n ∈ Finset.Icc 2 (N R),
              (G (Real.log n/Real.log R) - Ft (Real.log n/Real.log (N R:ℝ)))/(n:ℝ)|
            ≤ (ε/4) * (∑ n ∈ Finset.Icc 2 (N R), (1:ℝ)/n) := hsum_abs
        _ ≤ (ε/4) * (2 * Real.log (N R:ℝ)) :=
            mul_le_mul_of_nonneg_left hharm' (by linarith)
        _ = (ε/2) * Real.log (N R:ℝ) := by ring
        _ < ε * Real.log (N R:ℝ) := by
            apply mul_lt_mul_of_pos_right (by linarith) hlogNRpos
    have hBlim : Tendsto (fun R : ℕ =>
        (∑ n ∈ Finset.Icc 2 (N R), G (Real.log n / Real.log R) / (n:ℝ)) / Real.log (N R:ℝ))
        atTop (𝓝 (∫ u in (0:ℝ)..1, Ft u)) := by
      have hsplit : (fun R : ℕ =>
          (∑ n ∈ Finset.Icc 2 (N R), G (Real.log n / Real.log R) / (n:ℝ)) / Real.log (N R:ℝ))
          = (fun R : ℕ =>
              (∑ n ∈ Finset.Icc 2 (N R), Ft (Real.log n / Real.log (N R:ℝ)) / (n:ℝ))
                / Real.log (N R:ℝ)
              + (∑ n ∈ Finset.Icc 2 (N R),
                  (G (Real.log n / Real.log R) - Ft (Real.log n / Real.log (N R:ℝ))) / (n:ℝ))
                / Real.log (N R:ℝ)) := by
        funext R; rw [← add_div, ← Finset.sum_add_distrib]
        congr 1; apply Finset.sum_congr rfl; intro n _; ring
      rw [hsplit]; simpa using hriem.add hdrift
    have hPsiEq : (fun R : ℕ => Psi G R t) =ᶠ[atTop]
        (fun R : ℕ => (Real.log (N R:ℝ) / Real.log (R:ℝ)) *
          ((∑ n ∈ Finset.Icc 2 (N R), G (Real.log n / Real.log R) / (n:ℝ))
            / Real.log (N R:ℝ))) := by
      filter_upwards [hNtop.eventually_ge_atTop 2, eventually_ge_atTop 2] with R hNR2 hR2
      have hlogNRne : Real.log (N R:ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N R)))
      show (∑ n ∈ Finset.Icc 2 (N R), G (Real.log n / Real.log R) / (n:ℝ)) / Real.log (R:ℝ) = _
      field_simp
    rw [tendsto_congr' hPsiEq]
    have hsubst : ∫ y in (0:ℝ)..t, G y = t * ∫ u in (0:ℝ)..1, Ft u := by
      have h := intervalIntegral.mul_integral_comp_mul_left (f := G) (c := t) (a := 0) (b := 1)
      simp only [mul_zero, mul_one] at h
      rw [hFt]; exact h.symm
    rw [hsubst]
    exact hcR.mul hBlim

/-- **GPY/Maynard 2-D simplex limit — UNCONDITIONAL.** The coupled double log-weighted Riemann sum
converges to the iterated simplex integral `∫₀¹ F·(∫₀^{1-x} G)`. This is the deep axiom
`WeightedRiemann2D.weighted_riemann_2d` (the Aristotle target `3e2b6a8d`), now PROVEN in-kernel and
axiom-clean — obtained by feeding the fully-proven 1-D `psi_tendsto` into
`weighted_riemann_2d_of_psi_pointwise`. Closes leaf 1's smooth core. -/
theorem weighted_riemann_2d (F G : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1)) (hG : ContinuousOn G (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc 2 R, ∑ n ∈ Finset.Icc 2 (R / m),
            F (Real.log m / Real.log R) * G (Real.log n / Real.log R) / ((m : ℝ) * (n : ℝ)))
          / (Real.log R) ^ 2)
      atTop (nhds (∫ x in (0 : ℝ)..1, F x * ∫ y in (0 : ℝ)..(1 - x), G y)) :=
  weighted_riemann_2d_of_psi_pointwise F G hF hG (fun H hH t ht => psi_tendsto H hH t ht)

end BoundedGaps.InnerUniformReduction
