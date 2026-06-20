/-
# The `Mk_eps` polynomial bridge: DCT over the ε-enlarged / shrunken geometry.

`EpsScaling.lean` reduced both sides of the `Mk_eps` Rayleigh ratio to closed
forms for a polynomial sieve weight (the denominator dilation + the affine-slack
numerator keystone). This file supplies the remaining analytic chunk: the
**cutoff/dominated-convergence bridge** `Mk_eps_ge_MkF_eps`, the ε-analog of
`SievePolynomial.Mk_ge_polynomialMkF`.

`Mk_eps k ε = sSup (MkSet_eps k ε)` ranges over *smooth* `F` supported on the
`(1+ε)`-enlarged simplex, but a polynomial has full support, so `MkF_eps P.toFun`
is not directly in the set. As in the plain case we multiply `P` by a smooth
cutoff `χ_n` supported in `simplex_eps` that → 1 on its interior, then send
`n → ∞`: `MkF_eps (χ_n·P) ∈ MkSet_eps` and `MkF_eps (χ_n·P) → MkF_eps P` by
dominated convergence, giving `sSup (MkSet_eps k ε) ≥ MkF_eps P`.

The denominator lives over `simplex_eps = (1+ε)R_k`; the numerator's outer
integral over `simplex_shrunk = (1-ε)R_k` with inner bound `1+ε-∑s`. Both are
`B`-truncated simplices `{t ≥ 0 : ∑ t ≤ B}`, so the geometry (convexity,
interior, conull) and the cutoff are developed once for a general `B` and
instantiated at `B = 1+ε` (denominator + inner-integral target) and `B = 1-ε`
(numerator outer domain).
-/
import BoundedGaps.EpsScaling

namespace BoundedGaps.EpsBridge

open BoundedGaps BoundedGaps.SievePolynomial BoundedGaps.EpsScaling
open MeasureTheory Filter Topology
open Sieve
open scoped ContDiff

variable {k : ℕ}

/-! ## The `B`-truncated simplex and its geometry -/

/-- The `B`-truncated simplex `{t ≥ 0 : ∑ t ≤ B}`. Both `simplex_eps k ε`
(`B = 1+ε`) and `simplex_shrunk k ε` (`B = 1-ε`) are instances. -/
def simplexLE (k : ℕ) (B : ℝ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ B }

lemma simplex_eps_eq_LE (k : ℕ) (ε : ℝ) : simplex_eps k ε = simplexLE k (1 + ε) := rfl
lemma simplex_shrunk_eq_LE (k : ℕ) (ε : ℝ) : simplex_shrunk k ε = simplexLE k (1 - ε) := rfl

lemma isClosed_simplexLE (k : ℕ) (B : ℝ) : IsClosed (simplexLE k B) := by
  have h_eq : simplexLE k B =
      (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ B} := by
    ext t; simp [simplexLE, Set.mem_iInter]
  rw [h_eq]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
  · exact isClosed_Iic.preimage
      (continuous_finset_sum Finset.univ (fun i _ => continuous_apply i))

lemma convex_simplexLE (k : ℕ) (B : ℝ) : Convex ℝ (simplexLE k B) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have hxi := hx.1 i; have hyi := hy.1 i
    have : 0 ≤ a * x i + b * y i := by positivity
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · have hxs := hx.2; have hys := hy.2
    calc ∑ i, (a • x + b • y) i
        = a * ∑ i, x i + b * ∑ i, y i := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ a * B + b * B := by gcongr
      _ = B := by rw [← add_mul, hab, one_mul]

/-- Interior points of the `B`-simplex have all coordinates strictly positive
and sum strictly below `B` (the open `B`-simplex). -/
lemma interior_simplexLE_subset (k : ℕ) {B : ℝ} (hB : 0 < B) :
    interior (simplexLE k B) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < B} := by
  intro t ht
  have htmem : t ∈ simplexLE k B := interior_subset ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht)
  refine ⟨fun i => ?_, ?_⟩
  · rcases (htmem.1 i).lt_or_eq with h | h
    · exact h
    · exfalso
      set t' := Function.update t i (t i - r/2) with ht'
      have hd : dist t' t < r := by
        rw [dist_pi_lt_iff hr]
        intro j
        by_cases hj : j = i
        · rw [hj, ht', Function.update_self, Real.dist_eq,
            show t i - r/2 - t i = -(r/2) by ring, abs_neg, abs_of_pos (by positivity)]
          linarith
        · rw [ht', Function.update_of_ne hj, dist_self]; exact hr
      have hmem : t' ∈ simplexLE k B := hball (by rwa [Metric.mem_ball])
      have hi := hmem.1 i
      rw [ht', Function.update_self] at hi
      linarith
  · rcases isEmpty_or_nonempty (Fin k) with he | hne
    · simp only [Fintype.sum_empty]; exact hB
    · obtain ⟨i₀⟩ := hne
      by_contra h
      push_neg at h
      set t' := Function.update t i₀ (t i₀ + r/2) with ht'
      have hd : dist t' t < r := by
        rw [dist_pi_lt_iff hr]
        intro j
        by_cases hj : j = i₀
        · rw [hj, ht', Function.update_self, Real.dist_eq,
            show t i₀ + r/2 - t i₀ = r/2 by ring, abs_of_pos (by positivity)]
          linarith
        · rw [ht', Function.update_of_ne hj, dist_self]; exact hr
      have hmem : t' ∈ simplexLE k B := hball (by rwa [Metric.mem_ball])
      have hsum : (∑ j, t' j) - (∑ j, t j) = r/2 := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i₀]
        · rw [ht', Function.update_self]; ring
        · intro j _ hj; rw [ht', Function.update_of_ne hj]; ring
        · intro hcon; exact (hcon (Finset.mem_univ i₀)).elim
      have hle := hmem.2
      linarith

/-- The boundary of the `B`-simplex is null. -/
lemma simplexLE_diff_open_null (k : ℕ) {B : ℝ} (hB : 0 < B) :
    volume (simplexLE k B \ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < B}) = 0 := by
  apply measure_mono_null _ ((convex_simplexLE k B).addHaar_frontier volume)
  rw [(isClosed_simplexLE k B).frontier_eq]
  exact Set.diff_subset_diff_right (interior_simplexLE_subset k hB)

/-- a.e. (over the restricted measure) a `B`-simplex point lies in the open `B`-simplex. -/
lemma ae_open_simplexLE (k : ℕ) {B : ℝ} (hB : 0 < B) :
    ∀ᵐ t ∂(volume.restrict (simplexLE k B)), (∀ i, 0 < t i) ∧ ∑ i, t i < B := by
  rw [ae_iff, Measure.restrict_apply' (isClosed_simplexLE k B).measurableSet]
  apply measure_mono_null _ (simplexLE_diff_open_null k hB)
  rintro t ⟨hnp, hts⟩
  exact ⟨hts, hnp⟩

/-! ## The smooth cutoff `χ_n` for the `B`-simplex -/

/-- Explicit smooth cutoff for the `B`-simplex at scale `n`:
`χ_n(t) = (∏_i σ(n·t_i)) · σ(n·(B - ∑_j t_j))`, `σ = Real.smoothTransition`. -/
noncomputable def chiB (k n : ℕ) (B : ℝ) (t : Fin k → ℝ) : ℝ :=
  (∏ i : Fin k, Real.smoothTransition (n * t i)) *
    Real.smoothTransition (n * (B - ∑ j, t j))

lemma chiB_nonneg (k n : ℕ) (B : ℝ) (t : Fin k → ℝ) : 0 ≤ chiB k n B t :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

lemma chiB_le_one (k n : ℕ) (B : ℝ) (t : Fin k → ℝ) : chiB k n B t ≤ 1 := by
  apply mul_le_one₀
  · exact Finset.prod_le_one (fun i _ => Real.smoothTransition.nonneg _)
      (fun i _ => Real.smoothTransition.le_one _)
  · exact Real.smoothTransition.nonneg _
  · exact Real.smoothTransition.le_one _

lemma chiB_smooth (k n : ℕ) (B : ℝ) : ContDiff ℝ ∞ (chiB k n B) := by
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_apply ℝ ℝ i))
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_const.sub
        (ContDiff.sum fun j _ => contDiff_apply ℝ ℝ j)))

/-- The cutoff is supported in the `B`-simplex. -/
lemma chiB_support_subset (k n : ℕ) (B : ℝ) :
    Function.support (chiB k n B) ⊆ simplexLE k B := by
  intro t ht
  simp only [Function.mem_support, chiB, ne_eq, mul_eq_zero, not_or,
    Finset.prod_eq_zero_iff, not_exists, not_and] at ht
  obtain ⟨hprod, hlast⟩ := ht
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨fun i => ?_, ?_⟩
  · by_contra hneg
    push_neg at hneg
    exact hprod i (Finset.mem_univ i)
      (Real.smoothTransition.zero_of_nonpos (by nlinarith))
  · by_contra hneg
    push_neg at hneg
    exact hlast (Real.smoothTransition.zero_of_nonpos (by nlinarith))

/-- On the interior of the `B`-simplex (all coords positive, sum `< B`) the
cutoff is eventually `= 1`. -/
lemma chiB_eventually_eq_one (k : ℕ) {B : ℝ} {t : Fin k → ℝ}
    (ht : ∀ i, 0 < t i) (hsum : ∑ j, t j < B) :
    ∀ᶠ n : ℕ in atTop, chiB k n B t = 1 := by
  have key : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n * c := fun c hc =>
    (Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hslack : 0 < B - ∑ j, t j := by linarith
  have hall : ∀ᶠ n : ℕ in atTop, (∀ i, (1 : ℝ) ≤ n * t i) ∧ (1 : ℝ) ≤ n * (B - ∑ j, t j) := by
    rw [eventually_and]
    exact ⟨eventually_all.2 fun i => key _ (ht i), key _ hslack⟩
  filter_upwards [hall] with n hn
  unfold chiB
  rw [Real.smoothTransition.one_of_one_le hn.2, mul_one]
  exact Finset.prod_eq_one fun i _ => Real.smoothTransition.one_of_one_le (hn.1 i)

lemma chiB_tendsto_one (k : ℕ) {B : ℝ} {t : Fin k → ℝ}
    (ht : ∀ i, 0 < t i) (hsum : ∑ j, t j < B) :
    Tendsto (fun n => chiB k n B t) atTop (𝓝 1) :=
  tendsto_const_nhds.congr'
    (Filter.EventuallyEq.symm (chiB_eventually_eq_one k ht hsum))

/-! ## The cutoff-times-polynomial approximant and its `MkSet_eps` membership -/

/-- `F_n := χ_n^{(1+ε)} · P`, the ε-analog of `SievePolynomial.Fapprox`. -/
noncomputable def FapproxEps (P : PolynomialSieveWeight k) (ε : ℝ) (n : ℕ) :
    (Fin k → ℝ) → ℝ :=
  fun t => chiB k n (1 + ε) t * P.toFun t

lemma FapproxEps_support (P : PolynomialSieveWeight k) (ε : ℝ) (n : ℕ) :
    Function.support (FapproxEps P ε n) ⊆ simplex_eps k ε :=
  (Function.support_mul_subset_left _ _).trans (chiB_support_subset k n (1 + ε))

lemma FapproxEps_contDiff (P : PolynomialSieveWeight k) (ε : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (FapproxEps P ε n) :=
  (chiB_smooth k n (1 + ε)).mul (toFun_contDiff P)

lemma FapproxEps_mem_MkSet_eps (P : PolynomialSieveWeight k) (ε : ℝ) (n : ℕ)
    (hden : mkF_eps_denominator k ε (FapproxEps P ε n) > 0) :
    MkF_eps k ε (FapproxEps P ε n) ∈ MkSet_eps k ε :=
  ⟨FapproxEps P ε n, FapproxEps_contDiff P ε n, FapproxEps_support P ε n, hden, rfl⟩

/-! ## `MkF_eps` / `Mk_eps` nonnegativity -/

lemma MkF_eps_nonneg {ε : ℝ} (F : (Fin k → ℝ) → ℝ)
    (h : mkF_eps_denominator k ε F > 0) : 0 ≤ MkF_eps k ε F := by
  rw [MkF_eps]
  refine div_nonneg ?_ h.le
  rw [mkF_eps_numerator_eq_sum_J_i_eps]
  exact Finset.sum_nonneg fun i _ => J_i_eps_nonneg k ε F i

lemma MkSet_eps_nonneg (k : ℕ) (ε : ℝ) : ∀ v ∈ MkSet_eps k ε, 0 ≤ v := by
  rintro v ⟨F, _, _, hden, rfl⟩
  exact MkF_eps_nonneg F hden

lemma Mk_eps_nonneg (k : ℕ) (ε : ℝ) : 0 ≤ Mk_eps k ε :=
  Real.sSup_nonneg (MkSet_eps_nonneg k ε)

/-! ## Bound for `P.toFun` over the enlarged simplex + `insertNth` transport -/

lemma zero_mem_simplex_eps {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    (0 : Fin m → ℝ) ∈ simplex_eps m ε :=
  ⟨fun _ => le_refl 0, by simp only [Pi.zero_apply, Finset.sum_const_zero]; linarith⟩

lemma toFun_bounded_eps {ε : ℝ} (P : PolynomialSieveWeight k) :
    ∃ C : ℝ, ∀ t ∈ simplex_eps k ε, |P.toFun t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_simplex_eps k ε).exists_bound_of_continuousOn
    (toFun_continuous P).continuousOn
  exact ⟨C, fun t ht => by rw [← Real.norm_eq_abs]; exact hC t ht⟩

/-- For `s` in the shrunken simplex and `ti ∈ [0, 1+ε-∑s]`, the insertion lands
in the enlarged simplex. -/
lemma insertNth_mem_simplex_eps {n : ℕ} {ε : ℝ} (i : Fin (n + 1)) {ti : ℝ} {s : Fin n → ℝ}
    (hs : s ∈ simplex_shrunk n ε) (hti : ti ∈ Set.Icc (0:ℝ) (1 + ε - ∑ j, s j)) :
    i.insertNth ti s ∈ simplex_eps (n + 1) ε := by
  obtain ⟨hsnn, _⟩ := hs
  obtain ⟨hti0, hti1⟩ := hti
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Fin.insertNth_apply_same]; exact hti0
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Fin.insertNth_apply_succAbove]; exact hsnn j'
  · rw [insertNth_sum]; linarith

/-- Open version: strict interior of the shrunken simplex ⟹ strict interior of
the enlarged simplex. -/
lemma insertNth_mem_open_eps {n : ℕ} {ε : ℝ} (i : Fin (n + 1)) {ti : ℝ} {s : Fin n → ℝ}
    (hs : (∀ j, 0 < s j) ∧ ∑ j, s j < 1 - ε) (hti : ti ∈ Set.Ioo (0:ℝ) (1 + ε - ∑ j, s j)) :
    i.insertNth ti s ∈ {t : Fin (n + 1) → ℝ | (∀ j, 0 < t j) ∧ ∑ j, t j < 1 + ε} := by
  obtain ⟨hti0, hti1⟩ := hti
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Fin.insertNth_apply_same]; exact hti0
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Fin.insertNth_apply_succAbove]; exact hs.1 j'
  · rw [insertNth_sum]; linarith

/-! ## Denominator DCT -/

/-- Denominator DCT: `∫_{simplex_eps} (χ_n·P)² → ∫_{simplex_eps} P²`. -/
lemma denomEps_tendsto {ε : ℝ} (hε : 0 ≤ ε) (P : PolynomialSieveWeight k) :
    Tendsto (fun n => mkF_eps_denominator k ε (FapproxEps P ε n)) atTop
      (𝓝 (mkF_eps_denominator k ε P.toFun)) := by
  simp only [mkF_eps_denominator, FapproxEps]
  apply tendsto_integral_of_dominated_convergence (fun t => (P.toFun t) ^ 2)
  · intro n
    exact (((chiB_smooth k n (1 + ε)).continuous.mul (toFun_continuous P)).pow 2).aestronglyMeasurable
  · exact ((toFun_continuous P).pow 2).continuousOn.integrableOn_compact (isCompact_simplex_eps k ε)
  · intro n
    refine ae_of_all _ (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (chiB k n (1 + ε) t) ^ 2 ≤ 1 := by
      nlinarith [chiB_nonneg k n (1 + ε) t, chiB_le_one k n (1 + ε) t]
    nlinarith [sq_nonneg (P.toFun t), mul_pow (chiB k n (1 + ε) t) (P.toFun t) 2]
  · have hB : (0:ℝ) < 1 + ε := by linarith
    filter_upwards [ae_open_simplexLE k hB] with t ht
    have hchi : Tendsto (fun n => chiB k n (1 + ε) t) atTop (𝓝 1) := chiB_tendsto_one k ht.1 ht.2
    have h2 : Tendsto (fun n => chiB k n (1 + ε) t * P.toFun t) atTop (𝓝 (1 * P.toFun t)) :=
      hchi.mul_const _
    simpa using h2.pow 2

/-! ## Inner-layer convergence (the `ti`-integral) -/

lemma innerIntEps_tendsto {n : ℕ} {ε : ℝ} (_hε : 0 ≤ ε) (P : PolynomialSieveWeight (n + 1))
    (i : Fin (n + 1)) {s : Fin n → ℝ} (hs : (∀ j, 0 < s j) ∧ ∑ j, s j < 1 - ε) :
    Tendsto (fun m => ∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j),
        FapproxEps P ε m (i.insertNth ti s)) atTop
      (𝓝 (∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j), P.toFun (i.insertNth ti s))) := by
  obtain ⟨Cp, hCp⟩ := toFun_bounded_eps (ε := ε) P
  have hsmem : s ∈ simplex_shrunk n ε := ⟨fun j => (hs.1 j).le, hs.2.le⟩
  have hc : Continuous (fun ti : ℝ => (i.insertNth ti s : Fin (n + 1) → ℝ)) :=
    continuous_insertNth_right i s
  simp only [FapproxEps]
  apply tendsto_integral_of_dominated_convergence (fun _ => Cp)
  · intro m
    exact (((chiB_smooth (n + 1) m (1 + ε)).continuous.comp hc).mul
      ((toFun_continuous P).comp hc)).aestronglyMeasurable
  · exact integrableOn_const (hs := measure_Icc_lt_top.ne)
  · intro m
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ti hti
    have hins : i.insertNth ti s ∈ simplex_eps (n + 1) ε := insertNth_mem_simplex_eps i hsmem hti
    rw [Real.norm_eq_abs, abs_mul]
    calc |chiB (n + 1) m (1 + ε) (i.insertNth ti s)| * |P.toFun (i.insertNth ti s)|
        ≤ 1 * Cp := by
          apply mul_le_mul _ (hCp _ hins) (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (chiB_nonneg _ _ _ _)]; exact chiB_le_one _ _ _ _
      _ = Cp := one_mul _
  · rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ti hti
    have hopen := insertNth_mem_open_eps i hs hti
    have := (chiB_tendsto_one (n + 1) hopen.1 hopen.2).mul_const (P.toFun (i.insertNth ti s))
    simpa using this

/-! ## Outer-layer convergence and assembly -/

/-- Outer-layer convergence for a single coordinate `i` (`J_{i,1-ε}`). -/
lemma J_i_eps_tendsto {n : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (P : PolynomialSieveWeight (n + 1)) (i : Fin (n + 1)) :
    Tendsto (fun m => J_i_eps (n + 1) ε (FapproxEps P ε m) i) atTop
      (𝓝 (J_i_eps (n + 1) ε P.toFun i)) := by
  obtain ⟨Cp, hCp⟩ := toFun_bounded_eps (ε := ε) P
  have hCp0 : 0 ≤ Cp := le_trans (abs_nonneg _) (hCp 0 (zero_mem_simplex_eps hε0 (n + 1)))
  have hD0 : (0:ℝ) ≤ Cp * (1 + ε) := mul_nonneg hCp0 (by linarith)
  show Tendsto (fun m => ∫ s in simplex_shrunk n ε,
      (∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j), FapproxEps P ε m (i.insertNth ti s)) ^ 2) atTop
    (𝓝 (∫ s in simplex_shrunk n ε,
      (∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j), P.toFun (i.insertNth ti s)) ^ 2))
  apply tendsto_integral_of_dominated_convergence (fun _ => (Cp * (1 + ε)) ^ 2)
  · intro m
    have hins : Continuous
        (fun p : (Fin n → ℝ) × ℝ => (i.insertNth p.2 p.1 : Fin (n + 1) → ℝ)) := by
      apply continuous_pi; intro j
      by_cases hj : j = i
      · subst hj; simp only [Fin.insertNth_apply_same]; exact continuous_snd
      · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
        simp only [Fin.insertNth_apply_succAbove]; exact (continuous_apply j').comp continuous_fst
    have hcont : Continuous (Function.uncurry (fun (s : Fin n → ℝ) (ti : ℝ) =>
        FapproxEps P ε m (i.insertNth ti s))) := (FapproxEps_contDiff P ε m).continuous.comp hins
    have hg : Continuous (fun s : Fin n → ℝ =>
        ∫ ti in (0:ℝ)..(1 + ε - ∑ j, s j), FapproxEps P ε m (i.insertNth ti s)) := by
      have key := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := (volume : Measure ℝ)) (a₀ := (0:ℝ))
        (f := fun (s : Fin n → ℝ) (ti : ℝ) => FapproxEps P ε m (i.insertNth ti s)) hcont
      exact key.comp (continuous_id.prodMk
        (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j)))
    refine AEStronglyMeasurable.pow ?_ 2
    refine (hg.aestronglyMeasurable).congr ?_
    refine (ae_restrict_iff' (isClosed_simplex_shrunk n ε).measurableSet).mpr
      (ae_of_all _ fun s hs => ?_)
    have hnn : (0:ℝ) ≤ 1 + ε - ∑ j, s j := by
      obtain ⟨_, hsum⟩ := hs; linarith
    dsimp only
    rw [intervalIntegral.integral_of_le hnn, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  · exact integrableOn_const (hs := (isCompact_simplex_shrunk hε0).measure_lt_top.ne)
  · intro m
    filter_upwards [ae_restrict_mem (isClosed_simplex_shrunk n ε).measurableSet] with s hs
    have hsnn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs.1 j
    have hnn : (0:ℝ) ≤ 1 + ε - ∑ j, s j := by obtain ⟨_, hsum⟩ := hs; linarith
    have hbound : ‖∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j),
        FapproxEps P ε m (i.insertNth ti s)‖ ≤ Cp * (1 + ε) := by
      calc ‖∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j), FapproxEps P ε m (i.insertNth ti s)‖
          ≤ Cp * (volume (Set.Icc (0:ℝ) (1 + ε - ∑ j, s j))).toReal := by
            apply norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
            intro ti hti
            have hins : i.insertNth ti s ∈ simplex_eps (n + 1) ε :=
              insertNth_mem_simplex_eps i hs hti
            rw [FapproxEps, Real.norm_eq_abs, abs_mul]
            calc |chiB (n + 1) m (1 + ε) (i.insertNth ti s)| * |P.toFun (i.insertNth ti s)|
                ≤ 1 * Cp := by
                  apply mul_le_mul _ (hCp _ hins) (abs_nonneg _) (by norm_num)
                  rw [abs_of_nonneg (chiB_nonneg _ _ _ _)]; exact chiB_le_one _ _ _ _
              _ = Cp := one_mul _
        _ ≤ Cp * (1 + ε) := by
            apply mul_le_mul_of_nonneg_left _ hCp0
            rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 + ε - ∑ j, s j - 0)]
            linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs] at hbound
    nlinarith [abs_nonneg (∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j),
        FapproxEps P ε m (i.insertNth ti s)),
      sq_abs (∫ ti in Set.Icc (0:ℝ) (1 + ε - ∑ j, s j), FapproxEps P ε m (i.insertNth ti s))]
  · have hB : (0:ℝ) < 1 - ε := by linarith
    filter_upwards [ae_open_simplexLE n hB] with s hs
    exact (innerIntEps_tendsto hε0 P i hs).pow 2

/-- Numerator DCT (two-layer): `mkF_eps_numerator k ε (χ_n·P) → mkF_eps_numerator k ε P`. -/
lemma numerEps_tendsto {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (P : PolynomialSieveWeight k) :
    Tendsto (fun n => mkF_eps_numerator k ε (FapproxEps P ε n)) atTop
      (𝓝 (mkF_eps_numerator k ε P.toFun)) := by
  cases k with
  | zero => simp only [mkF_eps_numerator]; exact tendsto_const_nhds
  | succ m =>
    simp only [mkF_eps_numerator_eq_sum_J_i_eps]
    exact tendsto_finset_sum _ fun i _ => J_i_eps_tendsto hε0 hε1 P i

/-! ## `Mk_eps ≥ MkF_eps P.toFun` -/

/-- The ε-analog of `Mk_ge_polynomialMkF`: the enlarged-support Maynard
quantity dominates the (full-support) polynomial Rayleigh ratio. -/
theorem Mk_eps_ge_MkF_eps {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (P : PolynomialSieveWeight k) :
    Mk_eps k ε ≥ MkF_eps k ε P.toFun := by
  by_cases hden : mkF_eps_denominator k ε P.toFun = 0
  · have hz : MkF_eps k ε P.toFun = 0 := by rw [MkF_eps, hden, div_zero]
    rw [ge_iff_le, hz]; exact Mk_eps_nonneg k ε
  · have hpos : mkF_eps_denominator k ε P.toFun > 0 := by
      refine lt_of_le_of_ne ?_ (Ne.symm hden)
      rw [mkF_eps_denominator]; exact integral_nonneg fun _ => sq_nonneg _
    have hMkF : Tendsto (fun n => MkF_eps k ε (FapproxEps P ε n)) atTop
        (𝓝 (MkF_eps k ε P.toFun)) := by
      simp only [MkF_eps]
      exact (numerEps_tendsto hε0 hε1 P).div (denomEps_tendsto hε0 P) (ne_of_gt hpos)
    have hden_ev : ∀ᶠ n in atTop, mkF_eps_denominator k ε (FapproxEps P ε n) > 0 :=
      (denomEps_tendsto hε0 P).eventually (eventually_gt_nhds hpos)
    refine ge_iff_le.mpr (le_of_tendsto hMkF ?_)
    filter_upwards [hden_ev] with n hn
    exact le_csSup (MkSet_eps_bddAbove k ε) (FapproxEps_mem_MkSet_eps P ε n hn)

/-! ## The rational `Mk_eps` ratio and its bridge to `MkF_eps P.toFun`

With both Rayleigh sides in closed form (`EpsScaling`), a *rational* `ε` makes
every `(1±ε)`-power rational, so the whole `MkF_eps P.toFun` is a single rational
`polynomialMkF_eps P ε`. This is the ε-analog of `polynomialMkF` and feeds the
eventual `native_decide` degree-50 witness. -/

/-- The rational affine-slack closed form (the ε-numerator kernel as a rational):
`(1-ε)^{n+|a|} · Σ_m C(β,m)(2ε)^m(1-ε)^{β-m} · dirichletIntegralWithSlack(a, β-m)`. -/
noncomputable def affineSlackRat {n : ℕ} (a : Fin n → ℕ) (β : ℕ) (ε : ℚ) : ℚ :=
  (1 - ε) ^ (n + ∑ j, a j) *
    ∑ m ∈ Finset.range (β + 1),
      (2 * ε) ^ m * (1 - ε) ^ (β - m) * ((β.choose m : ℚ)) *
        dirichletIntegralWithSlack a (β - m)

/-- The real affine-slack integral over the shrunken simplex is the cast of
`affineSlackRat` (for rational `ε < 1`). Real-izes `dirichlet_affine_slack`. -/
lemma affineSlack_cast {n : ℕ} (a : Fin n → ℕ) (β : ℕ) {ε : ℚ} (hε1 : (ε : ℝ) < 1) :
    (∫ s in simplex_shrunk n (ε : ℝ), (∏ j, s j ^ a j) * (1 + (ε : ℝ) - ∑ j, s j) ^ β)
      = (affineSlackRat a β ε : ℝ) := by
  rw [dirichlet_affine_slack a β hε1, affineSlackRat]
  push_cast
  ring

/-- The rational `Mk_eps` denominator: `Σ_{p,q} c_p c_q (1+ε)^{k+|p+q|} monomialIntegral(p+q)`. -/
noncomputable def polynomialMaynardDenominator_eps {k : ℕ}
    (P : PolynomialSieveWeight k) (ε : ℚ) : ℚ :=
  ∑ p ∈ P.terms, ∑ q ∈ P.terms,
    p.2 * q.2 * ((1 + ε) ^ (k + ∑ i, (p.1 + q.1) i) * monomialIntegral (p.1 + q.1))

/-- The rational `Mk_eps` numerator: a triple sum of `affineSlackRat` kernels. -/
noncomputable def polynomialMaynardNumerator_eps {k : ℕ}
    (P : PolynomialSieveWeight k) (ε : ℚ) : ℚ :=
  match k, P with
  | 0, _ => 0
  | n + 1, P =>
      ∑ i : Fin (n + 1), ∑ p ∈ P.terms, ∑ q ∈ P.terms,
        (p.2 * q.2 / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ))) *
          affineSlackRat (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2) ε

/-- The rational `Mk_eps(P)` ratio. -/
noncomputable def polynomialMkF_eps {k : ℕ} (P : PolynomialSieveWeight k) (ε : ℚ) : ℚ :=
  polynomialMaynardNumerator_eps P ε / polynomialMaynardDenominator_eps P ε

/-- **Denominator bridge for `Mk_eps`.** -/
lemma denomEps_bridge {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ} (hε : 0 ≤ (ε : ℝ)) :
    mkF_eps_denominator k (ε : ℝ) P.toFun = (polynomialMaynardDenominator_eps P ε : ℝ) := by
  rw [mkF_eps_denominator_poly hε, polynomialMaynardDenominator_eps]
  push_cast
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by push_cast; ring))

/-- **Numerator bridge for `Mk_eps`.** -/
lemma numerEps_bridge {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ}
    (hε0 : 0 ≤ (ε : ℝ)) (hε1 : (ε : ℝ) < 1) :
    mkF_eps_numerator k (ε : ℝ) P.toFun = (polynomialMaynardNumerator_eps P ε : ℝ) := by
  cases k with
  | zero => simp [mkF_eps_numerator, polynomialMaynardNumerator_eps]
  | succ n =>
    rw [mkF_eps_numerator_poly hε0, polynomialMaynardNumerator_eps]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun p _ => Finset.sum_congr rfl (fun q _ => ?_)))
    rw [affineSlack_cast _ _ hε1]

/-- **The `Mk_eps` rational bridge.** -/
theorem polynomialMkF_eps_eq_MkF_eps {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ}
    (hε0 : 0 ≤ (ε : ℝ)) (hε1 : (ε : ℝ) < 1) :
    MkF_eps k (ε : ℝ) P.toFun = (polynomialMkF_eps P ε : ℝ) := by
  rw [MkF_eps, numerEps_bridge P hε0 hε1, denomEps_bridge P hε0, polynomialMkF_eps, Rat.cast_div]

/-- The polynomial Rayleigh ratio is a lower bound for `Mk_eps` (rational
`0 ≤ ε < 1`): `(polynomialMkF_eps P ε : ℝ) ≤ Mk_eps k ε`. The ε-analog of
`Mk_ge_polynomialMkF`. -/
theorem Mk_eps_ge_polynomialMkF_eps {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ}
    (hε0 : 0 ≤ (ε : ℝ)) (hε1 : (ε : ℝ) < 1) :
    (polynomialMkF_eps P ε : ℝ) ≤ Mk_eps k (ε : ℝ) := by
  have h1 := Mk_eps_ge_MkF_eps hε0 hε1 P
  rwa [polynomialMkF_eps_eq_MkF_eps P hε0 hε1] at h1

/-- **The ε-discharge lemma (general threshold).** A polynomial witness with a
verified rational `polynomialMkF_eps P ε > c` proves `Mk_eps k ε > c` (rational
`0 ≤ ε < 1`), the ε-analog of `Mk_gt_four_of_polynomial_witness`. The flagship
`H₁ ≤ 246` routes through this with `c = 2/ϑ` (ϑ in the Bombieri-Vinogradov
range). -/
theorem Mk_eps_gt_of_polynomial_witness {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ} {c : ℝ}
    (hε0 : 0 ≤ (ε : ℝ)) (hε1 : (ε : ℝ) < 1)
    (hP : (polynomialMkF_eps P ε : ℝ) > c) :
    Mk_eps k (ε : ℝ) > c :=
  lt_of_lt_of_le hP (Mk_eps_ge_polynomialMkF_eps P hε0 hε1)

/-- The `> 4` special case. -/
theorem Mk_eps_gt_four_of_polynomial_witness {k : ℕ} (P : PolynomialSieveWeight k) {ε : ℚ}
    (hε0 : 0 ≤ (ε : ℝ)) (hε1 : (ε : ℝ) < 1)
    (hP : (polynomialMkF_eps P ε : ℝ) > 4) :
    Mk_eps k (ε : ℝ) > 4 :=
  Mk_eps_gt_of_polynomial_witness P hε0 hε1 hP

/-- **Wiring to `Polymath8b.mk_eps_50_witness`.** Given a concrete degree-50
polynomial sieve weight and rational `(ε, ϑ)` meeting the witness side
conditions plus the rational Rayleigh bound `polynomialMkF_eps P ε > 2/ϑ`, the
`mk_eps_50_witness` existential holds **as a theorem**. This reduces that axiom
to a single `native_decide`-able rational inequality (the remaining degree-50
ε-witness). The statement is verbatim the body of `Polymath8b.mk_eps_50_witness`. -/
theorem mk_eps_50_witness_of_poly (P : PolynomialSieveWeight 50) {ε ϑ : ℚ}
    (hε0 : 0 < (ε : ℝ)) (hε1 : (ε : ℝ) < 1)
    (hϑ0 : 0 < (ϑ : ℝ)) (hϑ2 : (ϑ : ℝ) < 1 / 2)
    (hcoup : 1 + (ε : ℝ) < 1 / (ϑ : ℝ))
    (hwit : (polynomialMkF_eps P ε : ℝ) > 2 / (ϑ : ℝ)) :
    ∃ ε ϑ : ℝ, 0 < ε ∧ (0 < ϑ ∧ ϑ < 1 / 2) ∧
      1 + ε < 1 / ϑ ∧ Sieve.Mk_eps 50 ε > 2 / ϑ :=
  ⟨(ε : ℝ), (ϑ : ℝ), hε0, ⟨hϑ0, hϑ2⟩, hcoup,
    Mk_eps_gt_of_polynomial_witness P (le_of_lt hε0) hε1 hwit⟩

end BoundedGaps.EpsBridge
