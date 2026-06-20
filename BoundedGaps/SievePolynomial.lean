/-
# Polynomial sieve weights (Polymath8b §6 basis).

The variational problem $M_k$ asks for the supremum of a Rayleigh-style ratio
over smooth $F$ on the $k$-simplex. Polymath8b §6 chooses $F$ from a **polynomial
basis** — specifically, symmetric polynomials in the coordinates $t_1, \ldots, t_k$,
with rational coefficients.

The reason this matters: when $F$ is polynomial, the integrals defining the
numerator and denominator of $M_k(F)$ are computable in closed form (sums of
beta functions evaluated at integers), and the ratio is a **rational function
of the coefficients**. So $M_k(F) > 4$ becomes a polynomial inequality that
can in principle be verified exactly — no floating-point — by interval
arithmetic or rational normalization.

This file is now **sorry-free** (51 defs/lemmas): the polynomial Rayleigh
machinery (`polynomialMkF`, the Dirichlet/Beta keystone, `denom_bridge`,
`Mk_ge_polynomialMkF`, `polynomialMkF_eq_MkF`) is fully proven. It makes the
`Sieve.Mk k > 4` hypothesis in `Targets.lean` dischargeable by exhibiting an
explicit polynomial witness with rational Rayleigh ratio > threshold (done for
`M₅ > 2` in `Mk5Witness.lean`; the larger `k` need a symmetric-orbit reduction —
see `tools/mk/SYMMETRIC_REDUCTION.md`).

Polymath8b §7 ("Additional remarks", item 2) explicitly identifies a richer
basis — piecewise polynomials with carefully placed polytope supports — as
the natural next step. That richer class is what would push $M_{49}$ or
$M_{48}$ past 4.

Reference: [../papers/pdf/polymath8b-2014-variants.pdf](../papers/pdf/polymath8b-2014-variants.pdf) §6 ("The case of small and medium dimension").
-/
import Mathlib
import BoundedGaps.Sieve
import BoundedGaps.SimplexCutoff

namespace BoundedGaps.SievePolynomial

open BoundedGaps
open MeasureTheory Filter Topology
open Sieve
open scoped ContDiff

/-! ## Polynomial functions on the $k$-simplex -/

/-- A multi-index over $k$ variables: a tuple of non-negative integer exponents. -/
abbrev MultiIndex (k : ℕ) := Fin k → ℕ

/-- The total degree of a multi-index. -/
def MultiIndex.degree {k : ℕ} (α : MultiIndex k) : ℕ := ∑ i, α i

/-- A polynomial sieve weight on the $k$-simplex: a finite sum of monomial
terms $c_\alpha \prod_i t_i^{\alpha_i}$ with rational coefficients.

Represented as a `Finset` of `(MultiIndex k × ℚ)` pairs. -/
structure PolynomialSieveWeight (k : ℕ) where
  /-- The finite list of (multi-index, coefficient) pairs. -/
  terms : Finset (MultiIndex k × ℚ)

/-- Evaluate a polynomial sieve weight as a real-valued function on $\mathbb{R}^k$. -/
noncomputable def PolynomialSieveWeight.toFun {k : ℕ} (P : PolynomialSieveWeight k) :
    (Fin k → ℝ) → ℝ :=
  fun t => ∑ p ∈ P.terms, (p.2 : ℝ) * ∏ i, (t i) ^ (p.1 i)

/-! ## Integrals over the simplex — closed-form rational values -/

/-- The integral of a single monomial $\prod_i t_i^{\alpha_i}$ over the
standard $k$-simplex $\{t : t_i \ge 0, \sum t_i \le 1\}$ is the Dirichlet
integral

$$\int_{\Delta_k} \prod_i t_i^{\alpha_i} \, dt = \frac{\prod_i \alpha_i!}{(k + |\alpha|)!}$$

where $|\alpha| = \sum_i \alpha_i$.

A closed-form rational value; cheap to compute. -/
noncomputable def monomialIntegral {k : ℕ} (α : MultiIndex k) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) / ((k + α.degree).factorial : ℚ)

/-- Integral of the polynomial $P$ over the standard $k$-simplex, as a
rational number. -/
noncomputable def polynomialSimplexIntegral {k : ℕ} (P : PolynomialSieveWeight k) : ℚ :=
  ∑ p ∈ P.terms, p.2 * monomialIntegral p.1

/-! ## The Maynard ratio for polynomial $F$

For $F$ polynomial, both numerator and denominator of $M_k(F)$ are
polynomial-integral expressions; their ratio is computable rationally. -/

/-- Generalized Dirichlet integral with a "slack" exponent: the integral
of $\prod_i t_i^{\alpha_i} \cdot (1 - \sum_i t_i)^\beta$ over the standard
$n$-simplex in $\mathbb{R}^n$ has closed form

$$\int_{\Delta_n} \prod_i t_i^{\alpha_i} (1 - \sum)^\beta \, dt
  = \frac{\prod_i \alpha_i! \cdot \beta!}{(n + |\alpha| + \beta)!}$$

Specialises to `monomialIntegral` when $\beta = 0$. Used in the numerator
of the polynomial Maynard ratio: after the "drop-i" antiderivative, the
inner term's square produces a power of $(1 - \sum_{j \ne i} t_j)$. -/
noncomputable def dirichletIntegralWithSlack {n : ℕ}
    (α : Fin n → ℕ) (β : ℕ) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) * (β.factorial : ℚ) /
    ((n + (∑ i, α i) + β).factorial : ℚ)

/-- Numerator of the Maynard ratio for a polynomial sieve weight (Polymath8b
§5, modulo §6 polynomial substitution).

For $F = \sum_p c_p \prod_j t_j^{p_j}$, the inner antiderivative in $t_i$
from $0$ to $T = 1 - \sum_{j \ne i} s_j$ is
$\sum_p c_p \prod_{j \ne i} s_j^{p_j} \cdot T^{p_i + 1} / (p_i + 1)$.
Squaring and integrating over the $(k-1)$-simplex in $s_{j \ne i}$ gives

$$J_i(F) = \sum_{p, q} \frac{c_p c_q}{(p_i+1)(q_i+1)} \cdot
  \int_{\Delta_{k-1}} \prod_{j \ne i} s_j^{p_j + q_j} (1 - \sum_{j \ne i} s_j)^{p_i + q_i + 2} ds.$$

The inner integral is `dirichletIntegralWithSlack` applied to the
removed-$i$ multi-index `Fin.removeNth i (p + q)` and slack exponent
$p_i + q_i + 2$.

For $k = 0$, `Fin 0` is empty so the numerator is $0$. -/
noncomputable def polynomialMaynardNumerator {k : ℕ}
    (P : PolynomialSieveWeight k) : ℚ :=
  match k, P with
  | 0, _ => 0
  | n + 1, P =>
      ∑ i : Fin (n + 1),
        ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          (p.2 * q.2 : ℚ) /
            (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack
            (Fin.removeNth i (p.1 + q.1))
            (p.1 i + q.1 i + 2)

/-- Denominator: integral of $F^2$ against Lebesgue on the $k$-simplex.

For $F = \sum_p c_p \prod_i t_i^{p_i}$,
$F^2 = \sum_{p, q} c_p c_q \prod_i t_i^{p_i + q_i}$, so
$\int_{\Delta_k} F^2 = \sum_{p, q} c_p c_q \cdot \mathrm{monomialIntegral}(p + q)$
by termwise integration. -/
noncomputable def polynomialMaynardDenominator {k : ℕ}
    (P : PolynomialSieveWeight k) : ℚ :=
  ∑ p ∈ P.terms, ∑ q ∈ P.terms, p.2 * q.2 * monomialIntegral (p.1 + q.1)

/-- The Maynard ratio $M_k(F) = N / D$ for polynomial $F$, as a rational. -/
noncomputable def polynomialMkF {k : ℕ} (P : PolynomialSieveWeight k) : ℚ :=
  polynomialMaynardNumerator P / polynomialMaynardDenominator P

/-! ## The bridge from polynomial ratio to abstract $M_k$

The bridge `polynomialMkF_eq_MkF` (`Sieve.MkF k P.toFun = polynomialMkF P`) is
proven below in the `## Dirichlet integral bridge` section — it needs the
`insertNth` simplex helpers (defined later in this file), so it is placed just
before its sole user `Mk_gt_four_of_polynomial_witness`. The core is the
$k$-dimensional Dirichlet integral $\int_{\Delta_k} \prod t_i^{\alpha_i}
(1-\sum t)^\beta = \frac{\prod \alpha_i!\,\beta!}{(k+|\alpha|+\beta)!}$, which
`Mathlib` lacks; we build it from the 1-D Beta integral + a simplex Fubini step. -/

/-! ## Discharge of `Mk_ge_polynomialMkF` via the smooth simplex cutoff

`F_n := χ_n · P` lands in `MkSet k`, and `MkF F_n → MkF P` by dominated
convergence, so `Mk k = sSup (MkSet k) ≥ MkF P`. Proved axiom-clean.
(Two-layer DCT + geometry-of-the-simplex conull argument.) -/

/-- The cutoff-times-polynomial approximant `F_n := χ_n · P`. -/
noncomputable def Fapprox (P : PolynomialSieveWeight k) (n : ℕ) : (Fin k → ℝ) → ℝ :=
  fun t => Sieve.chi k n t * P.toFun t

/-! ## `P.toFun` is smooth and bounded on the simplex -/

lemma toFun_contDiff (P : PolynomialSieveWeight k) : ContDiff ℝ ∞ P.toFun := by
  unfold PolynomialSieveWeight.toFun
  apply ContDiff.sum
  intro p _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (contDiff_apply ℝ ℝ i).pow _

lemma toFun_continuous (P : PolynomialSieveWeight k) : Continuous P.toFun :=
  (toFun_contDiff P).continuous

/-- `P.toFun` is bounded on the (compact) simplex. -/
lemma toFun_bounded (P : PolynomialSieveWeight k) :
    ∃ C : ℝ, ∀ t ∈ simplex k, |P.toFun t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_simplex k).exists_bound_of_continuousOn
    (toFun_continuous P).continuousOn
  exact ⟨C, fun t ht => by rw [← Real.norm_eq_abs]; exact hC t ht⟩

/-! ## Basic facts about the denominator and `MkSet` -/

lemma denom_nonneg (F : (Fin k → ℝ) → ℝ) : 0 ≤ mkF_denominator k F := by
  unfold mkF_denominator
  exact integral_nonneg fun _ => sq_nonneg _

lemma numer_nonneg (F : (Fin k → ℝ) → ℝ) : 0 ≤ mkF_numerator k F := by
  rw [mkF_numerator_eq_sum_J_i]
  exact Finset.sum_nonneg fun i _ => J_i_nonneg k F i

lemma MkF_nonneg_of_denom_pos {F : (Fin k → ℝ) → ℝ}
    (h : mkF_denominator k F > 0) : 0 ≤ MkF k F := by
  rw [MkF]
  exact div_nonneg (numer_nonneg F) (le_of_lt h)

lemma MkSet_nonneg (k : ℕ) : ∀ v ∈ MkSet k, 0 ≤ v := by
  rintro v ⟨F, _, _, hden, rfl⟩
  exact MkF_nonneg_of_denom_pos hden

lemma Mk_nonneg (k : ℕ) : 0 ≤ Mk k :=
  Real.sSup_nonneg (MkSet_nonneg k)

/-! ## The approximant lands in `MkSet` -/

lemma Fapprox_support (P : PolynomialSieveWeight k) (n : ℕ) :
    Function.support (Fapprox P n) ⊆ simplex k :=
  (Function.support_mul_subset_left _ _).trans (chi_support_subset k n)

lemma Fapprox_contDiff (P : PolynomialSieveWeight k) (n : ℕ) :
    ContDiff ℝ ∞ (Fapprox P n) :=
  (chi_smooth k n).mul (toFun_contDiff P)

lemma Fapprox_mem_MkSet (P : PolynomialSieveWeight k) (n : ℕ)
    (hden : mkF_denominator k (Fapprox P n) > 0) :
    MkF k (Fapprox P n) ∈ MkSet k :=
  ⟨Fapprox P n, Fapprox_contDiff P n, Fapprox_support P n, hden, rfl⟩

/-! ## Geometry: the open simplex is conull -/

lemma convex_simplex (k : ℕ) : Convex ℝ (simplex k) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have hxi := hx.1 i; have hyi := hy.1 i
    have : 0 ≤ a * x i + b * y i := by positivity
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · have hxs := hx.2; have hys := hy.2
    calc ∑ i, (a • x + b • y) i
        = a * ∑ i, x i + b * ∑ i, y i := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by linarith

/-- Every interior point of the simplex has all coordinates strictly positive
and sum strictly below `1` (the open simplex). -/
lemma interior_simplex_subset (k : ℕ) :
    interior (simplex k) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1} := by
  intro t ht
  have htmem : t ∈ simplex k := interior_subset ht
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht)
  refine ⟨fun i => ?_, ?_⟩
  · rcases (htmem.1 i).lt_or_eq with h | h
    · exact h
    · exfalso
      set t' := Function.update t i (t i - ε/2) with ht'
      have hd : dist t' t < ε := by
        rw [dist_pi_lt_iff hε]
        intro j
        by_cases hj : j = i
        · rw [hj, ht', Function.update_self, Real.dist_eq,
            show t i - ε/2 - t i = -(ε/2) by ring, abs_neg, abs_of_pos (by positivity)]
          linarith
        · rw [ht', Function.update_of_ne hj, dist_self]; exact hε
      have hmem : t' ∈ simplex k := hball (by rwa [Metric.mem_ball])
      have hi := hmem.1 i
      rw [ht', Function.update_self] at hi
      linarith
  · rcases isEmpty_or_nonempty (Fin k) with he | hne
    · simp [Finset.sum_empty, Fintype.sum_empty]
    · obtain ⟨i₀⟩ := hne
      by_contra h
      push_neg at h
      set t' := Function.update t i₀ (t i₀ + ε/2) with ht'
      have hd : dist t' t < ε := by
        rw [dist_pi_lt_iff hε]
        intro j
        by_cases hj : j = i₀
        · rw [hj, ht', Function.update_self, Real.dist_eq,
            show t i₀ + ε/2 - t i₀ = ε/2 by ring, abs_of_pos (by positivity)]
          linarith
        · rw [ht', Function.update_of_ne hj, dist_self]; exact hε
      have hmem : t' ∈ simplex k := hball (by rwa [Metric.mem_ball])
      have hsum : (∑ j, t' j) - (∑ j, t j) = ε/2 := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i₀]
        · rw [ht', Function.update_self]; ring
        · intro j _ hj; rw [ht', Function.update_of_ne hj]; ring
        · intro hcon; exact (hcon (Finset.mem_univ i₀)).elim
      have hle := hmem.2
      linarith

/-- The boundary of the simplex (the part outside the open simplex) is null. -/
lemma simplex_diff_open_null (k : ℕ) :
    volume (simplex k \ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1}) = 0 := by
  apply measure_mono_null _ ((convex_simplex k).addHaar_frontier volume)
  rw [(isCompact_simplex k).isClosed.frontier_eq]
  exact Set.diff_subset_diff_right (interior_simplex_subset k)

/-- a.e. (over the restricted measure) a simplex point lies in the open simplex. -/
lemma ae_open_simplex (k : ℕ) :
    ∀ᵐ t ∂(volume.restrict (simplex k)), (∀ i, 0 < t i) ∧ ∑ i, t i < 1 := by
  rw [ae_iff, Measure.restrict_apply' (isCompact_simplex k).isClosed.measurableSet]
  apply measure_mono_null _ (simplex_diff_open_null k)
  rintro t ⟨hnp, hts⟩
  exact ⟨hts, hnp⟩

/-! ## Denominator DCT -/

/-- Denominator DCT: `∫_simplex (χ_n·P)² → ∫_simplex P²`. -/
lemma denom_tendsto (P : PolynomialSieveWeight k) :
    Tendsto (fun n => mkF_denominator k (Fapprox P n)) atTop
      (𝓝 (mkF_denominator k P.toFun)) := by
  simp only [mkF_denominator, Fapprox]
  apply tendsto_integral_of_dominated_convergence (fun t => (P.toFun t) ^ 2)
  · intro n
    exact (((chi_smooth k n).continuous.mul (toFun_continuous P)).pow 2).aestronglyMeasurable
  · exact ((toFun_continuous P).pow 2).continuousOn.integrableOn_compact (isCompact_simplex k)
  · intro n
    refine ae_of_all _ (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (Sieve.chi k n t) ^ 2 ≤ 1 := by nlinarith [chi_nonneg k n t, chi_le_one k n t]
    nlinarith [sq_nonneg (P.toFun t), mul_pow (Sieve.chi k n t) (P.toFun t) 2]
  · filter_upwards [ae_open_simplex k] with t ht
    have hchi : Tendsto (fun n => Sieve.chi k n t) atTop (𝓝 1) := chi_tendsto_one k ht.1 ht.2
    have h2 : Tendsto (fun n => Sieve.chi k n t * P.toFun t) atTop (𝓝 (1 * P.toFun t)) :=
      hchi.mul_const _
    simpa using h2.pow 2

/-! ## `insertNth` transport into the simplex -/

/-- `∑_j (insertNth i ti s)_j = ti + ∑_j s_j`. -/
lemma insertNth_sum {m : ℕ} (i : Fin (m+1)) (ti : ℝ) (s : Fin m → ℝ) :
    ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
  rw [Fin.sum_univ_succAbove (fun j => (i.insertNth ti s) j) i]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- The fiber map `ti ↦ insertNth i ti s` is continuous. -/
lemma continuous_insertNth_right {m : ℕ} (i : Fin (m+1)) (s : Fin m → ℝ) :
    Continuous (fun ti : ℝ => (i.insertNth ti s : Fin (m+1) → ℝ)) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst hj; simp only [Fin.insertNth_apply_same]; exact continuous_id
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    simp only [Fin.insertNth_apply_succAbove]; exact continuous_const

/-- For `s` in the `m`-simplex and `ti ∈ [0, 1-∑s]`, the insertion lands in
the `(m+1)`-simplex. -/
lemma insertNth_mem_simplex {m : ℕ} (i : Fin (m+1)) {ti : ℝ} {s : Fin m → ℝ}
    (hs : s ∈ simplex m) (hti : ti ∈ Set.Icc (0:ℝ) (1 - ∑ j, s j)) :
    i.insertNth ti s ∈ simplex (m+1) := by
  obtain ⟨hsnn, _hssum⟩ := hs
  obtain ⟨hti0, hti1⟩ := hti
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Fin.insertNth_apply_same]; exact hti0
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Fin.insertNth_apply_succAbove]; exact hsnn j'
  · rw [insertNth_sum]; linarith

/-- The open version: strict interior of the source ⟹ strict interior of the target. -/
lemma insertNth_mem_open {m : ℕ} (i : Fin (m+1)) {ti : ℝ} {s : Fin m → ℝ}
    (hs : (∀ j, 0 < s j) ∧ ∑ j, s j < 1) (hti : ti ∈ Set.Ioo (0:ℝ) (1 - ∑ j, s j)) :
    i.insertNth ti s ∈ {t : Fin (m+1) → ℝ | (∀ j, 0 < t j) ∧ ∑ j, t j < 1} := by
  obtain ⟨hti0, hti1⟩ := hti
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Fin.insertNth_apply_same]; exact hti0
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Fin.insertNth_apply_succAbove]; exact hs.1 j'
  · rw [insertNth_sum]; linarith

/-! ## Inner-layer convergence (the `ti`-integral) -/

/-- For `s` in the open `m`-simplex, the inner `ti`-integral of `χ_n·P` over the
fiber converges to that of `P`. -/
lemma innerInt_tendsto {m : ℕ} (P : PolynomialSieveWeight (m+1)) (i : Fin (m+1))
    {s : Fin m → ℝ} (hs : (∀ j, 0 < s j) ∧ ∑ j, s j < 1) :
    Tendsto (fun n => ∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j),
        Fapprox P n (i.insertNth ti s)) atTop
      (𝓝 (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), P.toFun (i.insertNth ti s))) := by
  obtain ⟨Cp, hCp⟩ := toFun_bounded P
  have hsmem : s ∈ simplex m := ⟨fun j => (hs.1 j).le, hs.2.le⟩
  have hc : Continuous (fun ti : ℝ => (i.insertNth ti s : Fin (m+1) → ℝ)) :=
    continuous_insertNth_right i s
  simp only [Fapprox]
  apply tendsto_integral_of_dominated_convergence (fun _ => Cp)
  · intro n
    exact (((chi_smooth (m+1) n).continuous.comp hc).mul
      ((toFun_continuous P).comp hc)).aestronglyMeasurable
  · exact integrableOn_const (hs := measure_Icc_lt_top.ne)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ti hti
    have hins : i.insertNth ti s ∈ simplex (m+1) := insertNth_mem_simplex i hsmem hti
    rw [Real.norm_eq_abs, abs_mul]
    calc |Sieve.chi (m+1) n (i.insertNth ti s)| * |P.toFun (i.insertNth ti s)|
        ≤ 1 * Cp := by
          apply mul_le_mul _ (hCp _ hins) (abs_nonneg _) (by norm_num)
          rw [abs_of_nonneg (chi_nonneg _ _ _)]; exact chi_le_one _ _ _
      _ = Cp := one_mul _
  · rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ti hti
    have hopen := insertNth_mem_open i hs hti
    have := (chi_tendsto_one (m+1) hopen.1 hopen.2).mul_const (P.toFun (i.insertNth ti s))
    simpa using this

/-! ## Outer-layer convergence and assembly -/

/-- `0 ∈ simplex m`, so the bound from `toFun_bounded` is nonnegative. -/
lemma zero_mem_simplex (m : ℕ) : (0 : Fin m → ℝ) ∈ simplex m :=
  ⟨fun _ => le_refl 0, by simp⟩

/-- Outer-layer convergence for a single coordinate `i` (`J_i`). -/
lemma J_i_tendsto {m : ℕ} (P : PolynomialSieveWeight (m+1)) (i : Fin (m+1)) :
    Tendsto (fun n => J_i (m+1) (Fapprox P n) i) atTop (𝓝 (J_i (m+1) P.toFun i)) := by
  obtain ⟨Cp, hCp⟩ := toFun_bounded P
  have hCp0 : 0 ≤ Cp := le_trans (abs_nonneg _) (hCp 0 (zero_mem_simplex (m+1)))
  show Tendsto (fun n => ∫ s in simplex m,
      (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), Fapprox P n (i.insertNth ti s)) ^ 2) atTop
    (𝓝 (∫ s in simplex m,
      (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), P.toFun (i.insertNth ti s)) ^ 2))
  apply tendsto_integral_of_dominated_convergence (fun _ => Cp ^ 2)
  · intro n
    have hins : Continuous (fun p : (Fin m → ℝ) × ℝ => (i.insertNth p.2 p.1 : Fin (m+1) → ℝ)) := by
      apply continuous_pi; intro j
      by_cases hj : j = i
      · subst hj; simp only [Fin.insertNth_apply_same]; exact continuous_snd
      · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
        simp only [Fin.insertNth_apply_succAbove]; exact (continuous_apply j').comp continuous_fst
    have hcont : Continuous (Function.uncurry (fun (s : Fin m → ℝ) (ti : ℝ) =>
        Fapprox P n (i.insertNth ti s))) := (Fapprox_contDiff P n).continuous.comp hins
    have hg : Continuous (fun s : Fin m → ℝ =>
        ∫ ti in (0:ℝ)..(1 - ∑ j, s j), Fapprox P n (i.insertNth ti s)) := by
      have key := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := (volume : Measure ℝ)) (a₀ := (0:ℝ))
        (f := fun (s : Fin m → ℝ) (ti : ℝ) => Fapprox P n (i.insertNth ti s)) hcont
      exact key.comp (continuous_id.prodMk
        (continuous_const.sub (continuous_finset_sum _ fun j _ => continuous_apply j)))
    refine AEStronglyMeasurable.pow ?_ 2
    refine (hg.aestronglyMeasurable).congr ?_
    refine (ae_restrict_iff' (isCompact_simplex m).isClosed.measurableSet).mpr
      (ae_of_all _ fun s hs => ?_)
    have hnn : (0:ℝ) ≤ 1 - ∑ j, s j := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hs.1 j)
      linarith [hs.2]
    dsimp only
    rw [intervalIntegral.integral_of_le hnn, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  · exact integrableOn_const (hs := (isCompact_simplex m).measure_lt_top.ne)
  · intro n
    filter_upwards [ae_restrict_mem (isCompact_simplex m).isClosed.measurableSet] with s hs
    have hbound : ‖∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), Fapprox P n (i.insertNth ti s)‖ ≤ Cp := by
      calc ‖∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), Fapprox P n (i.insertNth ti s)‖
          ≤ Cp * (volume (Set.Icc (0:ℝ) (1 - ∑ j, s j))).toReal := by
            apply norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
            intro ti hti
            have hins : i.insertNth ti s ∈ simplex (m+1) := insertNth_mem_simplex i hs hti
            rw [Fapprox, Real.norm_eq_abs, abs_mul]
            calc |Sieve.chi (m+1) n (i.insertNth ti s)| * |P.toFun (i.insertNth ti s)|
                ≤ 1 * Cp := by
                  apply mul_le_mul _ (hCp _ hins) (abs_nonneg _) (by norm_num)
                  rw [abs_of_nonneg (chi_nonneg _ _ _)]; exact chi_le_one _ _ _
              _ = Cp := one_mul _
        _ ≤ Cp * 1 := by
            apply mul_le_mul_of_nonneg_left _ hCp0
            have hsnn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs.1 j
            rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hs.2] : (0:ℝ) ≤ 1 - ∑ j, s j - 0)]
            linarith
        _ = Cp := mul_one _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs] at hbound
    nlinarith [abs_nonneg (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), Fapprox P n (i.insertNth ti s)),
      sq_abs (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), Fapprox P n (i.insertNth ti s))]
  · filter_upwards [ae_open_simplex m] with s hs
    exact (innerInt_tendsto P i hs).pow 2

/-- Numerator DCT (two-layer): `mkF_numerator k (χ_n·P) → mkF_numerator k P`. -/
lemma numer_tendsto (P : PolynomialSieveWeight k) :
    Tendsto (fun n => mkF_numerator k (Fapprox P n)) atTop
      (𝓝 (mkF_numerator k P.toFun)) := by
  cases k with
  | zero => simp only [mkF_numerator]; exact tendsto_const_nhds
  | succ m =>
    simp only [mkF_numerator_eq_sum_J_i]
    exact tendsto_finset_sum _ fun i _ => J_i_tendsto P i



/-! ## Reducing $M_k > 4$ to a rational inequality

The key target. Given a polynomial $P$ with `polynomialMkF P > 4` as a
**rational** inequality (decidable, exact), conclude `Sieve.Mk k > 4`. -/

/-- $\sup_F M_k(F) \ge$ any specific $M_k(F)$. -/
-- TRIAGE: ⚠️ NOT the easy `le_csSup` the old triage claimed. `Sieve.Mk k =
-- sSup (MkSet k)` ranges over **smooth functions with `support ⊆ simplex k`**,
-- but `P.toFun` (a polynomial) has FULL support, so `MkF P.toFun ∉ MkSet k`.
-- The honest proof is a cutoff/approximation argument: multiply `P` by the
-- smooth simplex cutoff `Sieve.chi k n` (see `BoundedGaps/SimplexCutoff.lean`,
-- which is built and axiom-clean), giving `F_n := chi k n · P.toFun` with
-- `F_n ∈ MkSet k` (smooth via `chi_smooth`·`P` smooth, support via
-- `chi_support_subset`); then `MkF F_n → MkF P.toFun` by dominated convergence
-- (`tendsto_integral_of_dominated_convergence` on `mkF_numerator` two-layer +
-- `mkF_denominator`, a.e. convergence from `chi_eventually_eq_one` + interior
-- conull via `Convex.μ_frontier = 0`), so `sSup (MkSet k) ≥ MkF P.toFun`.
-- All required mathlib lemmas confirmed present (v4.29.1); ~2-3 sessions.
-- Case `mkF_denominator k P.toFun = 0`: `MkF P.toFun = _/0 = 0 ≤ Mk` (Mk ≥ 0
-- since MkSet ⊆ [0,∞) and nonempty).
theorem Mk_ge_polynomialMkF {k : ℕ} (P : PolynomialSieveWeight k) :
    Sieve.Mk k ≥ Sieve.MkF k P.toFun := by
  by_cases hden : mkF_denominator k P.toFun = 0
  · have hz : MkF k P.toFun = 0 := by rw [MkF, hden, div_zero]
    rw [ge_iff_le, hz]; exact Mk_nonneg k
  · have hpos : mkF_denominator k P.toFun > 0 :=
      lt_of_le_of_ne (denom_nonneg _) (Ne.symm hden)
    have hMkF : Tendsto (fun n => MkF k (Fapprox P n)) atTop (𝓝 (MkF k P.toFun)) := by
      simp only [MkF]
      exact (numer_tendsto P).div (denom_tendsto P) (ne_of_gt hpos)
    have hden_ev : ∀ᶠ n in atTop, mkF_denominator k (Fapprox P n) > 0 :=
      (denom_tendsto P).eventually (eventually_gt_nhds hpos)
    refine ge_iff_le.mpr (le_of_tendsto hMkF ?_)
    filter_upwards [hden_ev] with n hn
    exact le_csSup (MkSet_bddAbove k) (Fapprox_mem_MkSet P n hn)


section DirichletBridge
open intervalIntegral

/-- The 1D Dirichlet/Beta keystone. -/
theorem dirichlet_1d (a b : ℕ) (c : ℝ) :
    ∫ t in (0:ℝ)..c, t ^ a * (c - t) ^ b
      = c ^ (a + b + 1) * ((a.factorial * b.factorial : ℝ) / (a + b + 1).factorial) := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [integral_pow, zero_pow (Nat.add_one_ne_zero a), sub_zero, Nat.factorial_succ]
    have hfa : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    push_cast
    field_simp
  | succ b ih =>
    have key :
        ∫ t in (0:ℝ)..c, t ^ a * (c - t) ^ (b + 1)
          = ((b : ℝ) + 1) / ((a : ℝ) + 1) *
              ∫ t in (0:ℝ)..c, t ^ (a + 1) * (c - t) ^ b := by
      have hu : ∀ x ∈ Set.uIcc (0:ℝ) c,
          HasDerivAt (fun x => (c - x) ^ (b + 1)) (-((b:ℝ) + 1) * (c - x) ^ b) x := by
        intro x _
        have h1 : HasDerivAt (fun x : ℝ => c - x) (-1) x := (hasDerivAt_id x).const_sub c
        have hp := h1.pow (b + 1)
        have hval : (↑(b + 1) * (c - x) ^ (b + 1 - 1) * (-1) : ℝ)
            = -((b : ℝ) + 1) * (c - x) ^ b := by
          rw [Nat.add_sub_cancel]; push_cast; ring
        rw [← hval]; exact hp
      have hv : ∀ x ∈ Set.uIcc (0:ℝ) c,
          HasDerivAt (fun x => x ^ (a + 1) / ((a:ℝ) + 1)) (x ^ a) x := by
        intro x _
        have hp := (hasDerivAt_pow (a + 1) x).div_const ((a:ℝ) + 1)
        have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
        have hval : (↑(a + 1) * x ^ (a + 1 - 1) / ((a : ℝ) + 1) : ℝ) = x ^ a := by
          rw [Nat.add_sub_cancel]; push_cast; field_simp
        rw [← hval]; exact hp
      have hu' : IntervalIntegrable (fun x => -((b:ℝ) + 1) * (c - x) ^ b) volume 0 c :=
        (Continuous.intervalIntegrable (by continuity) 0 c)
      have hv' : IntervalIntegrable (fun x => x ^ a) volume 0 c :=
        (continuous_pow a).intervalIntegrable 0 c
      have ibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      have comm : (∫ t in (0:ℝ)..c, t ^ a * (c - t) ^ (b + 1))
          = ∫ t in (0:ℝ)..c, (c - t) ^ (b + 1) * t ^ a := by
        apply intervalIntegral.integral_congr; intro x _; dsimp; ring
      have hconst :
          (∫ x in (0:ℝ)..c, -((b:ℝ) + 1) * (c - x) ^ b * (x ^ (a + 1) / ((a:ℝ) + 1)))
            = -(((b:ℝ) + 1) / ((a:ℝ) + 1)) *
                ∫ t in (0:ℝ)..c, t ^ (a + 1) * (c - t) ^ b := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr; intro x _; dsimp
        have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
        field_simp
      rw [comm, ibp, hconst]
      simp only [sub_self, sub_zero, zero_pow (Nat.add_one_ne_zero b),
        zero_pow (Nat.add_one_ne_zero a), zero_mul, mul_zero, zero_div]
      ring
    rw [key, ih (a + 1)]
    have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
    have e1 : a + 1 + b + 1 = a + (b + 1) + 1 := by ring
    rw [e1, Nat.factorial_succ a, Nat.factorial_succ b]
    have hfa : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    have hfb : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
    have hfd : ((a + (b + 1) + 1).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp

/-- Forward extraction from simplex membership of an `insertNth`. -/
lemma insertNth_mem_simplex_forward {n : ℕ} (i : Fin (n + 1)) {ti : ℝ} {s : Fin n → ℝ}
    (h : i.insertNth ti s ∈ simplex (n + 1)) :
    0 ≤ ti ∧ s ∈ simplex n ∧ ti ≤ 1 - ∑ j, s j := by
  obtain ⟨hnn, hsum⟩ := h
  have hti : 0 ≤ ti := by have := hnn i; rwa [Fin.insertNth_apply_same] at this
  have hsj : ∀ j, 0 ≤ s j := by
    intro j; have := hnn (i.succAbove j); rwa [Fin.insertNth_apply_succAbove] at this
  rw [insertNth_sum] at hsum
  exact ⟨hti, ⟨hsj, by linarith⟩, by linarith⟩

/-- **Simplex Fubini**: peel one coordinate of a simplex integral. -/
theorem simplex_fubini {n : ℕ} (i : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ)
    (hG : Continuous G) :
    (∫ t in simplex (n + 1), G t)
      = ∫ s in simplex n, ∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), G (i.insertNth ti s) := by
  classical
  have hSmeas : MeasurableSet (simplex (n + 1)) := (isClosed_simplex (n + 1)).measurableSet
  have hSnmeas : MeasurableSet (simplex n) := (isClosed_simplex n).measurableSet
  have hIntOn : IntegrableOn G (simplex (n + 1)) :=
    (hG.continuousOn).integrableOn_compact (isCompact_simplex (n + 1))
  have hint : Integrable ((simplex (n + 1)).indicator G) :=
    hIntOn.integrable_indicator hSmeas
  rw [← MeasureTheory.integral_indicator hSmeas, integral_insertNth_eq i _ hint,
      ← MeasureTheory.integral_indicator hSnmeas]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun s => ?_)
  by_cases hs : s ∈ simplex n
  · rw [Set.indicator_of_mem hs]
    have hiff : ∀ ti, (i.insertNth ti s ∈ simplex (n + 1))
        ↔ ti ∈ Set.Icc (0:ℝ) (1 - ∑ j, s j) := by
      intro ti
      constructor
      · intro hm
        obtain ⟨h0, _, hle⟩ := insertNth_mem_simplex_forward i hm
        exact ⟨h0, hle⟩
      · intro hti; exact insertNth_mem_simplex i hs hti
    have hfun : (fun ti => (simplex (n + 1)).indicator G (i.insertNth ti s))
        = (Set.Icc (0:ℝ) (1 - ∑ j, s j)).indicator (fun ti => G (i.insertNth ti s)) := by
      funext ti
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hti : ti ∈ Set.Icc (0:ℝ) (1 - ∑ j, s j)
      · rw [if_pos ((hiff ti).mpr hti), if_pos hti]
      · rw [if_neg (fun hm => hti ((hiff ti).mp hm)), if_neg hti]
    dsimp only
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc]
  · rw [Set.indicator_of_notMem hs]
    have hzero : ∀ ti, (simplex (n + 1)).indicator G (i.insertNth ti s) = 0 := by
      intro ti
      rw [Set.indicator_apply, if_neg]
      intro hm
      exact hs (insertNth_mem_simplex_forward i hm).2.1
    simp only [hzero, integral_zero]

/-- Continuity of the slack-monomial integrand. -/
lemma slackMonomial_continuous {k : ℕ} (α : Fin k → ℕ) (β : ℕ) :
    Continuous (fun t : Fin k → ℝ => (∏ i, t i ^ α i) * (1 - ∑ i, t i) ^ β) := by
  apply Continuous.mul
  · exact continuous_finset_prod _ (fun i _ => (continuous_apply i).pow _)
  · exact ((continuous_const.sub (continuous_finset_sum _
      (fun i _ => continuous_apply i))).pow _)

/-- **Master lemma**: the k-dim Dirichlet integral with slack. -/
theorem dirichlet_slack {k : ℕ} (α : Fin k → ℕ) (β : ℕ) :
    (∫ t in simplex k, (∏ i, t i ^ α i) * (1 - ∑ i, t i) ^ β)
      = (∏ i, ((α i).factorial : ℝ)) * (β.factorial : ℝ)
          / ((k + (∑ i, α i) + β).factorial : ℝ) := by
  induction k generalizing β with
  | zero =>
    have hsimp0 : simplex 0 = (Set.univ : Set (Fin 0 → ℝ)) := by
      ext t; simp [simplex]
    rw [hsimp0, Measure.restrict_univ, MeasureTheory.integral_unique]
    have hvol : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
      simp [measureReal_def, MeasureTheory.volume_pi]
    have hfb : (β.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero β)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, sub_zero, one_pow,
      mul_one, Nat.zero_add, smul_eq_mul, hvol, one_mul]
    field_simp
  | succ n ih =>
    set i : Fin (n + 1) := 0 with hi
    set α' : Fin n → ℕ := fun j => α (i.succAbove j) with hα'
    rw [simplex_fubini i _ (slackMonomial_continuous α β)]
    have hstep : Set.EqOn
        (fun s => ∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j),
            (∏ a, (i.insertNth ti s) a ^ α a) * (1 - ∑ a, (i.insertNth ti s) a) ^ β)
        (fun s => ((α i).factorial * β.factorial / (α i + β + 1).factorial : ℝ)
            * ((∏ j, s j ^ α' j) * (1 - ∑ j, s j) ^ (α i + β + 1)))
        (simplex n) := by
      intro s hs
      simp only
      have hT : (0:ℝ) ≤ 1 - ∑ j, s j := by obtain ⟨_, h2⟩ := hs; linarith
      have hpt : Set.EqOn
          (fun ti => (∏ a, (i.insertNth ti s) a ^ α a) * (1 - ∑ a, (i.insertNth ti s) a) ^ β)
          (fun ti => (∏ j, s j ^ α' j) * (ti ^ α i * (1 - ∑ j, s j - ti) ^ β))
          (Set.Icc (0:ℝ) (1 - ∑ j, s j)) := by
        intro ti _
        simp only
        rw [Fin.prod_univ_succAbove _ i, insertNth_sum]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        ring
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt,
          MeasureTheory.integral_const_mul]
      rw [show (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), ti ^ α i * (1 - ∑ j, s j - ti) ^ β)
            = ∫ ti in (0:ℝ)..(1 - ∑ j, s j), ti ^ α i * (1 - ∑ j, s j - ti) ^ β from by
        rw [intervalIntegral.integral_of_le hT, MeasureTheory.integral_Icc_eq_integral_Ioc],
        dirichlet_1d (α i) β (1 - ∑ j, s j)]
      ring
    rw [MeasureTheory.setIntegral_congr_fun (isClosed_simplex n).measurableSet hstep,
        MeasureTheory.integral_const_mul, ih α' (α i + β + 1)]
    -- algebra
    have hsum : (∑ a, α a) = α i + ∑ j, α' j := Fin.sum_univ_succAbove α i
    have hprod : (∏ a, ((α a).factorial : ℝ))
        = (α i).factorial * ∏ j, ((α' j).factorial : ℝ) :=
      Fin.prod_univ_succAbove (fun a => ((α a).factorial : ℝ)) i
    have eidx : n + (∑ j, α' j) + (α i + β + 1) = (n + 1) + (∑ a, α a) + β := by
      rw [hsum]; ring
    rw [eidx, hprod]
    have h1 : ((α i + β + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (((n + 1) + (∑ a, α a) + β).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

/-- The monomial integral closed form (β = 0 case), real-valued. -/
lemma monomialIntegral_eq {k : ℕ} (α : Fin k → ℕ) :
    (∫ t in simplex k, ∏ i, t i ^ α i) = (monomialIntegral α : ℝ) := by
  have h := dirichlet_slack α 0
  simp only [pow_zero, mul_one, Nat.add_zero, Nat.factorial_zero, Nat.cast_one] at h
  rw [monomialIntegral, MultiIndex.degree]
  push_cast
  rw [h]

/-- Each monomial term is integrable on the (compact) simplex. -/
lemma monomial_integrableOn {k : ℕ} (α : Fin k → ℕ) (c : ℝ) :
    Integrable (fun t : Fin k → ℝ => c * ∏ i, t i ^ α i) (volume.restrict (simplex k)) :=
  (Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_simplex k)

/-- **Denominator bridge.** -/
lemma denom_bridge {k : ℕ} (P : PolynomialSieveWeight k) :
    mkF_denominator k P.toFun = (polynomialMaynardDenominator P : ℝ) := by
  rw [mkF_denominator]
  have hsq : ∀ t : Fin k → ℝ, P.toFun t ^ 2
      = ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          ((p.2 : ℝ) * (q.2 : ℝ)) * ∏ i, t i ^ ((p.1 + q.1) i) := by
    intro t
    rw [sq, PolynomialSieveWeight.toFun, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [show (∏ i, t i ^ ((p.1 + q.1) i)) = (∏ i, t i ^ p.1 i) * ∏ i, t i ^ q.1 i from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [Pi.add_apply, pow_add])]
    ring
  simp_rw [hsq]
  rw [MeasureTheory.integral_finset_sum _ (fun p _ =>
    MeasureTheory.integrable_finset_sum _ (fun q _ =>
      monomial_integrableOn (p.1 + q.1) ((p.2 : ℝ) * (q.2 : ℝ))))]
  rw [polynomialMaynardDenominator]
  push_cast
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [MeasureTheory.integral_finset_sum _ (fun q _ =>
    monomial_integrableOn (p.1 + q.1) ((p.2 : ℝ) * (q.2 : ℝ)))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [MeasureTheory.integral_const_mul, monomialIntegral_eq]

/-- `∫_{[0,T]} ti^m = T^{m+1}/(m+1)` for `T ≥ 0`. -/
lemma int_pow_Icc (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ti in Set.Icc (0:ℝ) T, ti ^ m) = T ^ (m + 1) / (m + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
      integral_pow]
  simp

/-- The slack-Dirichlet integral closed form, real-valued. -/
lemma dirichletSlack_eq {n : ℕ} (α : Fin n → ℕ) (β : ℕ) :
    (∫ t in simplex n, (∏ i, t i ^ α i) * (1 - ∑ i, t i) ^ β)
      = (dirichletIntegralWithSlack α β : ℝ) := by
  rw [dirichlet_slack α β, dirichletIntegralWithSlack]
  push_cast
  ring

/-- The inner `ti`-integral of `P.toFun ∘ insertNth i`, factored. -/
lemma inner_eq {n : ℕ} (P : PolynomialSieveWeight (n + 1)) (i : Fin (n + 1))
    {s : Fin n → ℝ} (hs : s ∈ simplex n) :
    (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), P.toFun (i.insertNth ti s))
      = ∑ p ∈ P.terms, (p.2 : ℝ) * (∏ j, s j ^ p.1 (i.succAbove j))
          * ((1 - ∑ j, s j) ^ (p.1 i + 1) / (p.1 i + 1)) := by
  have hT : (0:ℝ) ≤ 1 - ∑ j, s j := by obtain ⟨_, h2⟩ := hs; linarith
  have hpt : Set.EqOn (fun ti => P.toFun (i.insertNth ti s))
      (fun ti => ∑ p ∈ P.terms,
        ((p.2 : ℝ) * (∏ j, s j ^ p.1 (i.succAbove j))) * ti ^ p.1 i)
      (Set.Icc (0:ℝ) (1 - ∑ j, s j)) := by
    intro ti _
    simp only [PolynomialSieveWeight.toFun]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt,
      MeasureTheory.integral_finset_sum _ (fun p _ =>
        ((Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [MeasureTheory.integral_const_mul, int_pow_Icc (p.1 i) _ hT]

/-- Continuous functions are integrable on the (compact) simplex. -/
lemma simplexIntegrable {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (simplex n)) :=
  (hf.continuousOn).integrableOn_compact (isCompact_simplex n)

/-- **Single Maynard marginal bridge** `J_i`. -/
lemma Ji_bridge {n : ℕ} (P : PolynomialSieveWeight (n + 1)) (i : Fin (n + 1)) :
    (∫ s in simplex n,
        (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), P.toFun (i.insertNth ti s)) ^ 2)
      = ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          ((p.2 * q.2 : ℚ) / ((p.1 i + 1) * (q.1 i + 1))
            * dirichletIntegralWithSlack (Fin.removeNth i (p.1 + q.1))
                (p.1 i + q.1 i + 2) : ℝ) := by
  have hsq_eq : Set.EqOn
      (fun s => (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), P.toFun (i.insertNth ti s)) ^ 2)
      (fun s => (∑ p ∈ P.terms, (p.2 : ℝ) * (∏ j, s j ^ p.1 (i.succAbove j))
          * ((1 - ∑ j, s j) ^ (p.1 i + 1) / (p.1 i + 1))) ^ 2)
      (simplex n) := fun s hs => by dsimp only; rw [inner_eq P i hs]
  rw [MeasureTheory.setIntegral_congr_fun (isClosed_simplex n).measurableSet hsq_eq]
  simp_rw [sq, Finset.sum_mul_sum]
  rw [MeasureTheory.integral_finset_sum _ (fun p _ =>
    MeasureTheory.integrable_finset_sum _ (fun q _ => simplexIntegrable (by fun_prop)))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [MeasureTheory.integral_finset_sum _ (fun q _ => simplexIntegrable (by fun_prop))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hp1 : ((p.1 i : ℝ) + 1) ≠ 0 := by positivity
  have hq1 : ((q.1 i : ℝ) + 1) ≠ 0 := by positivity
  have hBB : (fun s : Fin n → ℝ =>
        ((p.2 : ℝ) * (∏ j, s j ^ p.1 (i.succAbove j))
            * ((1 - ∑ j, s j) ^ (p.1 i + 1) / (p.1 i + 1)))
        * ((q.2 : ℝ) * (∏ j, s j ^ q.1 (i.succAbove j))
            * ((1 - ∑ j, s j) ^ (q.1 i + 1) / (q.1 i + 1))))
      = (fun s => ((p.2 : ℝ) * (q.2 : ℝ) / ((p.1 i + 1) * (q.1 i + 1)))
          * ((∏ j, s j ^ (Fin.removeNth i (p.1 + q.1)) j)
              * (1 - ∑ j, s j) ^ (p.1 i + q.1 i + 2))) := by
    funext s
    rw [show (∏ j, s j ^ (Fin.removeNth i (p.1 + q.1)) j)
          = (∏ j, s j ^ p.1 (i.succAbove j)) * ∏ j, s j ^ q.1 (i.succAbove j) from by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun j _ => by
          simp only [Fin.removeNth, Pi.add_apply]; rw [pow_add])]
    rw [show (1 - ∑ j, s j) ^ (p.1 i + q.1 i + 2)
          = (1 - ∑ j, s j) ^ (p.1 i + 1) * (1 - ∑ j, s j) ^ (q.1 i + 1) from by
        rw [← pow_add]; congr 1; omega]
    field_simp
  rw [hBB, MeasureTheory.integral_const_mul, dirichletSlack_eq]
  simp only [Rat.cast_mul]

/-- **Numerator bridge.** -/
lemma numer_bridge {k : ℕ} (P : PolynomialSieveWeight k) :
    mkF_numerator k P.toFun = (polynomialMaynardNumerator P : ℝ) := by
  cases k with
  | zero => simp [mkF_numerator, polynomialMaynardNumerator]
  | succ n =>
    rw [mkF_numerator, polynomialMaynardNumerator]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Ji_bridge P i]
    refine Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by push_cast; ring))

/-- **The bridge** (was the `sorry` at `SievePolynomial:155`). -/
theorem polynomialMkF_eq_MkF {k : ℕ} (P : PolynomialSieveWeight k) :
    Sieve.MkF k P.toFun = (polynomialMkF P : ℝ) := by
  rw [Sieve.MkF, numer_bridge, denom_bridge, polynomialMkF, Rat.cast_div]

end DirichletBridge

/-- **The discharge lemma**: a single polynomial witness with verified
rational ratio $> 4$ proves $\Sieve.Mk k > 4$.

This is the "plug in numerics here" target. To improve the bound to $H_1 \le
240$, one would:
1. Find a `P : PolynomialSieveWeight 49` (likely with terms of degree up to
   ~80, as in Polymath8b's Maple computation).
2. Compute `polynomialMkF P` as an explicit rational.
3. Prove the rational inequality `polynomialMkF P > 4` via `decide` /
   `native_decide` / interval arithmetic.
4. Apply this lemma to get `Sieve.Mk 49 > 4`.
5. Plug into `Targets.H1_le_240_if_Mk_49_witness`. -/
theorem Mk_gt_four_of_polynomial_witness {k : ℕ}
    (P : PolynomialSieveWeight k) (_hP : (polynomialMkF P : ℝ) > 4) :
    Sieve.Mk k > 4 := by
  have h1 := Mk_ge_polynomialMkF P
  rw [polynomialMkF_eq_MkF] at h1
  linarith

/-! ## Polynomial weights are separable (the provable coupling)

A `PolynomialSieveWeight` evaluates to a finite sum of monomials
$\sum_p c_p \prod_i t_i^{p_i}$, and each monomial $\prod_i t_i^{p_i}$ is a
product of 1D functions $\mathrm{Fs}_{p,i}(x) = x^{p_i}$. So `P.toFun` is
*literally* of the `Sieve.IsFiniteSeparable` shape — no separation-rank obstruction,
because we built it from a finite basis. This is the honest, **provable**
content backing the cited `Sieve.exists_separable_F_*` axioms: the §6
polynomial optimum lands inside the separable class. -/
theorem polynomialSieveWeight_isSeparable {k : ℕ} (P : PolynomialSieveWeight k) :
    Sieve.IsFiniteSeparable P.toFun := by
  classical
  refine ⟨P.terms.card,
    fun j => ((P.terms.equivFin.symm j).1.2 : ℝ),
    fun j i x => x ^ ((P.terms.equivFin.symm j).1.1 i),
    0, ?_⟩
  intro t
  simp only [PolynomialSieveWeight.toFun]
  rw [← Finset.sum_coe_sort P.terms
        (fun p => (p.2 : ℝ) * ∏ i, (t i) ^ (p.1 i))]
  rw [← Equiv.sum_comp P.terms.equivFin.symm
        (fun x : P.terms => ((x.1.2 : ℝ) * ∏ i, (t i) ^ (x.1.1 i)))]

end BoundedGaps.SievePolynomial
