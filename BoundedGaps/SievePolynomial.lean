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

This file lays the type-level groundwork. Bodies are mostly `sorry`; the
purpose is to make the `Sieve.Mk k > 4` hypothesis in `Targets.lean`
*structurally* dischargeable by future numerical work, without changing the
bridge.

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

/-! ## The bridge from polynomial ratio to abstract $M_k$ -/

/-- Bridge: the polynomial-evaluated ratio equals the abstract $M_k(F)$ value.

Cast from `ℚ` to `ℝ` is implicit. Currently `sorry`; the proof requires
showing that `PolynomialSieveWeight.toFun` is a valid smooth function on the
simplex (it is, as a polynomial) and that the closed-form integrals match
the abstract `Sieve.MkF` definition. -/
-- TRIAGE: NEEDS_SIEVE — depends on Sieve.MkF having a real body. Once both
-- numerator/denominator above are defined AND Sieve.MkF is defined, this is
-- ~30 lines (the closed-form integral matches the abstract integral
-- termwise, monomial-by-monomial).
theorem polynomialMkF_eq_MkF {k : ℕ} (P : PolynomialSieveWeight k) :
    Sieve.MkF k P.toFun = (polynomialMkF P : ℝ) := sorry

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
      simpa only [MkF] using
        (numer_tendsto P).div (denom_tendsto P) (ne_of_gt hpos)
    have hden_ev : ∀ᶠ n in atTop, mkF_denominator k (Fapprox P n) > 0 :=
      (denom_tendsto P).eventually (eventually_gt_nhds hpos)
    refine ge_iff_le.mpr (le_of_tendsto hMkF ?_)
    filter_upwards [hden_ev] with n hn
    exact le_csSup (MkSet_bddAbove k) (Fapprox_mem_MkSet P n hn)


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
