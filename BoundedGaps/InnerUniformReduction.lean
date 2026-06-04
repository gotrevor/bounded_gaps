import BoundedGaps.WeightedRiemann2D
import BoundedGaps.PolyaUniform

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

end BoundedGaps.InnerUniformReduction
