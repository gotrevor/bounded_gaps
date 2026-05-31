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

namespace BoundedGaps.SievePolynomial

open BoundedGaps

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
    Sieve.Mk k ≥ Sieve.MkF k P.toFun := sorry

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
