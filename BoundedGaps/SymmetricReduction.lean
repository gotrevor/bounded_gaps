/-
# Symmetric reduction for the polynomial Maynard ratio — foundations

The plain `polynomialMkF` (Rayleigh ratio of a polynomial sieve weight) sums over
*explicit monomials*, so a witness for `Mk k > c` at large `k` is intractable: even a
single orbit like `t₁⋯t₇` contributes `C(k,7)` monomials. The remedy (Maynard/Polymath8b
§6) is to restrict the variational problem to **symmetric** test functions and compute the
Rayleigh ratio from the few *orbit* coefficients, with matrix entries closed-form in `k`.
See `tools/mk/SYMMETRIC_REDUCTION.md` (validated Python prototype + exact LDL verdict).

The bedrock that makes "restrict to symmetric `F`" legitimate is that the Rayleigh data is
**invariant under coordinate permutations**: the numerator and denominator of the Maynard
ratio are unchanged when the `k` variables are permuted. This file proves that invariance.
(The remaining piece — the matching/overlap closed form that collapses an orbit-pair sum to
falling factorials over a factorial — is the genuine multi-session combinatorial kernel,
stated in the design doc, not here.)
-/
import BoundedGaps.SievePolynomial

namespace BoundedGaps.SymmetricReduction

open BoundedGaps BoundedGaps.SievePolynomial

/-- The action of a coordinate permutation `σ` on a polynomial sieve weight:
precompose every monomial's exponent vector with `σ`, keeping its coefficient. -/
noncomputable def permWeight {k : ℕ} (σ : Equiv.Perm (Fin k))
    (P : PolynomialSieveWeight k) : PolynomialSieveWeight k :=
  ⟨P.terms.image (fun pc => ((fun i => pc.1 (σ i) : MultiIndex k), pc.2))⟩

/-- The exponent-permuting map on `(MultiIndex k × ℚ)` is injective (`σ` is a bijection). -/
lemma permTerm_injective {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Function.Injective
      (fun pc : MultiIndex k × ℚ => ((fun i => pc.1 (σ i) : MultiIndex k), pc.2)) := by
  rintro ⟨a, ca⟩ ⟨b, cb⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hfun, hc⟩ := h
  refine Prod.ext ?_ hc
  funext j
  have := congrFun hfun (σ.symm j)
  simpa using this

/-- `monomialIntegral` is invariant under permuting the exponent vector. -/
lemma monomialIntegral_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (α : MultiIndex k) :
    monomialIntegral (fun i => α (σ i)) = monomialIntegral α := by
  unfold monomialIntegral MultiIndex.degree
  rw [Equiv.prod_comp σ (fun i => ((α i).factorial : ℚ)), Equiv.sum_comp σ α]

/-- **Denominator permutation-invariance.** Permuting the `k` coordinates leaves the
denominator of the Maynard ratio (the simplex integral of `F²`) unchanged. -/
theorem polynomialMaynardDenominator_permWeight {k : ℕ} (σ : Equiv.Perm (Fin k))
    (P : PolynomialSieveWeight k) :
    polynomialMaynardDenominator (permWeight σ P) = polynomialMaynardDenominator P := by
  unfold polynomialMaynardDenominator permWeight
  rw [Finset.sum_image (fun x _ y _ h => permTerm_injective σ h)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_image (fun x _ y _ h => permTerm_injective σ h)]
  refine Finset.sum_congr rfl fun q _ => ?_
  change p.2 * q.2 * monomialIntegral (fun i => p.1 (σ i) + q.1 (σ i))
      = p.2 * q.2 * monomialIntegral (p.1 + q.1)
  rw [show (fun i => p.1 (σ i) + q.1 (σ i)) = (fun i => (p.1 + q.1) (σ i)) from rfl,
      monomialIntegral_comp_perm σ (p.1 + q.1)]

end BoundedGaps.SymmetricReduction
