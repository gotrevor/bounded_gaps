import Mathlib

/-!
# Pólya's theorem: uniform convergence of monotone functions

This file proves **Pólya's theorem**: if for each `R` the function `Φn R` is monotone on the compact
interval `[0,1]`, the limit `Φ` is continuous on `[0,1]`, and `Φn R t → Φ t` pointwise for every
`t ∈ [0,1]`, then the convergence is **uniform** on `[0,1]`.

This is distinct from Dini's theorem (`Mathlib/Topology/UniformSpace/Dini.lean`), where the
monotonicity is in the *sequence index* `R` and the `Φn R` must be continuous. Here the monotonicity
is in the *function argument* `t`, and the `Φn R` need NOT be continuous — they may be step
functions. That is exactly the situation of the GPY/Maynard inner Riemann partial sums
`Ψ(R,t) = (∑_{n≤⌊R^t⌋} G(log n/log R)/n)/log R`, which are monotone step functions of `t` (for
`G ≥ 0`) converging pointwise to the continuous `t ↦ ∫₀^t G`. Pólya then upgrades to the *uniform*
convergence in `t` that the 2-D simplex limit (`WeightedRiemann2D.weighted_riemann_2d_of_inner`)
consumes — collapsing the hard "boundary regime" of the inner-uniform decomposition into a single
clean abstract argument.

## Proof
Standard finite-grid argument. Given `ε`, uniform continuity of `Φ` gives `δ`; take a grid of mesh
`1/K < δ`. Pointwise convergence at the *finitely many* grid points is simultaneous eventually. For
arbitrary `t`, bracket it between two adjacent grid points `a ≤ t ≤ b` with `b - a ≤ 1/K`. Monotone
sandwich `Φn R a ≤ Φn R t ≤ Φn R b` plus the grid bound plus `|Φ b - Φ t|, |Φ a - Φ t| ≤ ε/4`
(uniform continuity, `|b-t|,|a-t| ≤ 1/K ≤ δ`) give `|Φn R t - Φ t| ≤ ε/2 ≤ ε`.
-/

open Filter Topology Set

namespace BoundedGaps.PolyaUniform

/-- **Pólya's theorem (uniform convergence of monotone functions).** If for each `R` the function
`Φn R` is monotone on `[0,1]`, the limit `Φ` is continuous on `[0,1]`, and `Φn R t → Φ t` pointwise
for every `t ∈ [0,1]`, then the convergence is uniform on `[0,1]`. No continuity of the `Φn R` is
required. -/
theorem polya_uniform
    (Φ : ℝ → ℝ) (Φn : ℕ → ℝ → ℝ)
    (hΦ_cont : ContinuousOn Φ (Icc (0 : ℝ) 1))
    (hmono_n : ∀ R, MonotoneOn (Φn R) (Icc (0 : ℝ) 1))
    (hptw : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun R => Φn R t) atTop (𝓝 (Φ t))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) 1, |Φn R t - Φ t| ≤ ε := by
  intro ε hε
  -- Uniform continuity of `Φ` on the compact `[0,1]`.
  have huc : UniformContinuousOn Φ (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hΦ_cont
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1 huc (ε/4) (by linarith)
  -- Pick `K ≥ 1` with `1/K < δ`, i.e. `K > 1/δ`.
  obtain ⟨K, hKgt⟩ := exists_nat_gt (1/δ)
  have hKposR : (0 : ℝ) < (K:ℝ) := lt_trans (by positivity) hKgt
  have hKnat : 0 < K := by exact_mod_cast hKposR
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKposR
  have hKinv : 1 / (K:ℝ) ≤ δ := by
    have h1 : 1 < (K:ℝ) * δ := by rw [div_lt_iff₀ hδ0] at hKgt; exact hKgt
    rw [div_le_iff₀ hKposR]; nlinarith [h1]
  -- Grid points `j/K` for `j ≤ K` all lie in `[0,1]`.
  have hgrid_mem : ∀ j : ℕ, j ≤ K → ((j:ℝ)/K) ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hKposR]; exact_mod_cast hj
  -- Eventually (in `R`) all `K+1` grid points are within `ε/4`.
  have hfin : ∀ᶠ R : ℕ in atTop,
      ∀ j ∈ Finset.range (K+1), |Φn R ((j:ℝ)/K) - Φ ((j:ℝ)/K)| ≤ ε/4 := by
    rw [eventually_all_finset]
    intro j hj
    have hjK : j ≤ K := by rw [Finset.mem_range] at hj; omega
    have hmem := hgrid_mem j hjK
    filter_upwards [Metric.tendsto_nhds.1 (hptw _ hmem) (ε/4) (by linarith)] with R hR
    rw [Real.dist_eq] at hR; linarith [hR]
  filter_upwards [hfin] with R hR t ht
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · -- `t = 1`: it is the grid point `K/K = 1`.
    have hKgridmem : K ∈ Finset.range (K+1) := by rw [Finset.mem_range]; omega
    have hb := hR K hKgridmem
    have hKK : (K:ℝ)/K = 1 := div_self hKne
    rw [hKK] at hb
    rw [ht1]; linarith [hb]
  · -- `t < 1`: bracket `t ∈ [j/K, (j+1)/K]` with `j = ⌊t·K⌋₊`.
    have htK0 : (0 : ℝ) ≤ t * K := mul_nonneg ht.1 (le_of_lt hKposR)
    set j := ⌊t * (K:ℝ)⌋₊ with hjdef
    have htK_lt : t * (K:ℝ) < K := by
      nlinarith [mul_pos hKposR (show (0 : ℝ) < 1 - t by linarith)]
    have hjlt : j < K := by rw [hjdef, Nat.floor_lt htK0]; exact htK_lt
    have hj_mem : j ∈ Finset.range (K+1) := by rw [Finset.mem_range]; omega
    have hj1_mem : j+1 ∈ Finset.range (K+1) := by rw [Finset.mem_range]; omega
    have ha_mem : ((j:ℝ)/K) ∈ Icc (0 : ℝ) 1 := hgrid_mem j (by omega)
    have hb_mem : (((j+1:ℕ):ℝ)/K) ∈ Icc (0 : ℝ) 1 := hgrid_mem (j+1) (by omega)
    -- `a ≤ t ≤ b`
    have ha_le : (j:ℝ)/K ≤ t := by
      rw [div_le_iff₀ hKposR]
      have hfl := Nat.floor_le htK0
      rw [← hjdef] at hfl; linarith [hfl]
    have hb_ge : t ≤ ((j+1:ℕ):ℝ)/K := by
      rw [le_div_iff₀ hKposR]
      have hlt := Nat.lt_floor_add_one (t * (K:ℝ))
      rw [← hjdef] at hlt; push_cast; linarith [hlt]
    -- mesh `b - a = 1/K ≤ δ`
    have hba : ((j+1:ℕ):ℝ)/K - (j:ℝ)/K = 1/K := by
      rw [div_sub_div_same]; push_cast; ring_nf
    have hbt_le : dist (((j+1:ℕ):ℝ)/K) t ≤ δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      have hstep : ((j+1:ℕ):ℝ)/K - t ≤ ((j+1:ℕ):ℝ)/K - (j:ℝ)/K := by linarith [ha_le]
      rw [hba] at hstep; linarith [hKinv]
    have hat_le : dist ((j:ℝ)/K) t ≤ δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have hstep : t - (j:ℝ)/K ≤ ((j+1:ℕ):ℝ)/K - (j:ℝ)/K := by linarith [hb_ge]
      rw [hba] at hstep; linarith [hKinv]
    -- `Φ` oscillation
    have hΦb : |Φ (((j+1:ℕ):ℝ)/K) - Φ t| ≤ ε/4 := by
      have := hδ _ hb_mem _ ht hbt_le; rwa [Real.dist_eq] at this
    have hΦa : |Φ ((j:ℝ)/K) - Φ t| ≤ ε/4 := by
      have := hδ _ ha_mem _ ht hat_le; rwa [Real.dist_eq] at this
    -- grid pointwise bounds
    have hGb := hR (j+1) hj1_mem
    have hGa := hR j hj_mem
    -- monotone sandwich
    have hle1 : Φn R ((j:ℝ)/K) ≤ Φn R t := hmono_n R ha_mem ht ha_le
    have hle2 : Φn R t ≤ Φn R (((j+1:ℕ):ℝ)/K) := hmono_n R ht hb_mem hb_ge
    rw [abs_le] at hΦb hΦa hGb hGa ⊢
    refine ⟨?_, ?_⟩
    · linarith [hle1, hΦa.1, hGa.1]
    · linarith [hle2, hΦb.2, hGb.2]

end BoundedGaps.PolyaUniform
