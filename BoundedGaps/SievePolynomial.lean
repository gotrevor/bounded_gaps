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

/-- Numerator of the Maynard ratio for a polynomial sieve weight (Polymath8b
§5, modulo §6 polynomial substitution). Body is a `sorry` placeholder —
the real definition is a sum of $k$ "drop-$i$" integrals against the squared
gradient of $F$. -/
-- TRIAGE: DEF BODY (~2-3h) — sum over i of ∫_{Δ_{k-1}} (drop-i partial
-- derivative of F)² over (k-1)-simplex. Decomposes into a sum of monomial
-- integrals via the gradient's polynomial structure. Pure ℚ arithmetic, no
-- analysis. Independent of BV (good standalone target).
noncomputable def polynomialMaynardNumerator {k : ℕ}
    (_P : PolynomialSieveWeight k) : ℚ := sorry

/-- Denominator: integral of $F^2$ against a specific measure over the simplex.
Computable in closed form from the monomial expansion of $F^2$. -/
-- TRIAGE: DEF BODY (~1-2h) — sister of polynomialMaynardNumerator. Expand
-- F² into a sum of monomials via PolynomialSieveWeight.terms convolution,
-- apply monomialIntegral termwise. Simpler than the numerator (no gradient).
noncomputable def polynomialMaynardDenominator {k : ℕ}
    (_P : PolynomialSieveWeight k) : ℚ := sorry

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
-- TRIAGE: NEEDS_SIEVE — `le_iSup`-style, ~5 lines, but needs Sieve.Mk to be
-- defined as `iSup` over admissible F (currently sorry def body). Trivial
-- once Mk has a real body.
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

end BoundedGaps.SievePolynomial
