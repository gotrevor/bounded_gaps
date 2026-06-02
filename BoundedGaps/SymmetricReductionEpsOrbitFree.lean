/-
# Orbit-free / computable ε-Rayleigh Gram assembly (`Mk_eps`)

The ε-analog of the cross/bilinear/computable layer in `SymmetricReductionOrbitFree`. Reuses the
disjoint-union double-sum engine `OrbitFree.symWeight_double_sum` and the computable non-ε
denominator entry `OrbitFree.gramDenEntry`.

**Denominator side: DONE.** The ε-denominator's per-pair weight `(1+ε)^{k+|p+q|}` is constant
over each orbit pair (degree is permutation-invariant), so the ε-denominator Gram entry is
`(1+ε)^{k+|a|+|b|}` times `gramDenEntry`, and the ε-Maynard denominator of a symmetric weight is
the orbit-basis quadratic form with those entries.

**Numerator side: TODO** — needs the orbit-free re-index of the `affineSlackRat` triple sum (the
ε-analog of `OrbitFree.numerator_orbitFree`). Harder than the non-ε case: `affineSlackRat` is an
`∑ₘ` of binomial-weighted `dirichletIntegralWithSlack` with the slack exponent `β-m` *varying*
with `m`, so `numerator_summand_factor` applies per-`m` with an `m`-dependent local factor.
-/
import BoundedGaps.SymmetricReductionOrbitFree
import BoundedGaps.EpsBridge

namespace BoundedGaps

open Finset
open scoped Nat
open SymmetricReduction SievePolynomial OrbitFree EpsBridge

namespace OrbitFree

/-- **Constant `(1+ε)`-factor of the ε-denominator orbit pair.** Since every orbit pair `(p,q)`
has `|p+q| = |a|+|b|` (degree is permutation-invariant), the weight `(1+ε)^{k+|p+q|}` is constant
over the pair and factors out, leaving the non-ε orbit-pair denominator sum. -/
lemma orbitPair_denominator_eps_const {k : ℕ} (a b : MultiIndex k) (ε : ℚ) :
    ∑ p ∈ monoOrbit a, ∑ q ∈ monoOrbit b,
        ((1 + ε) ^ (k + ∑ i, (p + q) i) * monomialIntegral (p + q))
      = (1 + ε) ^ (k + a.degree + b.degree) *
          ∑ p ∈ monoOrbit a, ∑ q ∈ monoOrbit b, monomialIntegral (p + q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hdeg : (∑ i, (p + q) i) = a.degree + b.degree := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [monoOrbit_mem_degree a hp, monoOrbit_mem_degree b hq]
  rw [hdeg, ← Nat.add_assoc]

/-- **Computable ε-denominator Gram entry** — `(1+ε)^{k+|a|+|b|}` times the non-ε computable
denominator entry `gramDenEntry`. -/
def gramDenEntryEps {k : ℕ} (a b : MultiIndex k) (ε : ℚ) : ℚ :=
  (1 + ε) ^ (k + a.degree + b.degree) * gramDenEntry a b

/-- **Bilinear (Gram) expansion of the ε-denominator.** The ε-Maynard denominator of a symmetric
weight is the orbit-basis quadratic form `∑_{a,b∈R} c_a c_b · gramDenEntryEps a b ε` with the
computable ε-denominator Gram entries. The ε-analog of
`polynomialMaynardDenominator_symWeight`. -/
theorem polynomialMaynardDenominator_eps_symWeight {k : ℕ} (R : Finset (MultiIndex k))
    (c : MultiIndex k → ℚ) (ε : ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMaynardDenominator_eps (symWeight R c) ε
      = ∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryEps a b ε := by
  classical
  unfold polynomialMaynardDenominator_eps
  rw [symWeight_double_sum R c hR]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  dsimp only
  rw [gramDenEntryEps, ← gramDenEntry_eq, crossDenominator_orbitSum,
      ← orbitPair_denominator_eps_const, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]

end OrbitFree

end BoundedGaps
