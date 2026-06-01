/-
# Symmetric reduction for the ε-enlarged Maynard ratio (`Mk_eps`)

The ε-trick Rayleigh data (`polynomialMaynardNumerator_eps` / `polynomialMaynardDenominator_eps`,
the rational forms feeding `Mk_eps`) has the *same* monomial double/triple-sum structure as the
plain ratio in `SievePolynomial`, so the orbit-sum reductions of `SymmetricReduction` transfer
almost verbatim. This matters because the **unconditional** flagship `H₁ ≤ 246` routes through
`Mk_eps 50` (the path the EH-conditional plain-`Mk` ladder cannot reach), and a concrete witness
there faces the same un-materializable monomial `Finset` (an orbit like `1⁹` on `k = 50` is
`C(50,9) ≈ 12·10⁹` monomials) — so it needs the orbit-level form too.

Two facts make the transfer mechanical:
* The denominator's `(1 + ε)^(k + |p+q|)` factor is **orbit-invariant**: `|p+q| = |α|+|β|` is
  constant over orbit pairs, so the ε-denominator factors as a pure power times the plain orbit
  form (`polynomialMaynardDenominator_eps_orbitSum`).
* The numerator's `affineSlackRat (removeNth i (p+q)) β ε` depends on `removeNth i (p+q)` exactly
  the way `dirichletIntegralWithSlack` does, so the `i`-summed constancy argument
  (`dirichletNum_orbitSum_const`) replays unchanged (`affineNum_orbitSum_const` →
  `polynomialMaynardNumerator_eps_orbitSum`).

The cross-orbit (off-diagonal) overlap-matching closed form — the genuine multi-session
combinatorial kernel that both the plain ladder and this ε-flagship ultimately need — is *not*
here; see `tools/mk/SYMMETRIC_REDUCTION.md`.
-/
import BoundedGaps.SymmetricReduction
import BoundedGaps.EpsBridge

namespace BoundedGaps.SymmetricReductionEps

open BoundedGaps BoundedGaps.SievePolynomial BoundedGaps.SymmetricReduction BoundedGaps.EpsBridge

/-- Every monomial of `orbitSum α` has total degree `α.degree` (a permutation of `α` preserves
the coordinate sum). -/
lemma orbitSum_term_degree {k : ℕ} (α : MultiIndex k) {p : MultiIndex k × ℚ}
    (hp : p ∈ (orbitSum α).terms) : (∑ i, p.1 i) = α.degree := by
  simp only [orbitSum, Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨σ, hσ⟩ := hp
  rw [← hσ]
  simpa [MultiIndex.degree] using (Equiv.sum_comp σ (fun i => α i))

/-- **ε-denominator reduction for an orbit sum.** The `(1 + ε)^(k + |p+q|)` factor is constant
over the orbit pair (`|p+q| = 2|α|`), so it pulls out and the rest is the plain denominator orbit
form `polynomialMaynardDenominator_orbitSum`. -/
theorem polynomialMaynardDenominator_eps_orbitSum {k : ℕ} (α : MultiIndex k) (ε : ℚ) :
    polynomialMaynardDenominator_eps (orbitSum α) ε
      = (1 + ε) ^ (k + 2 * α.degree) * polynomialMaynardDenominator (orbitSum α) := by
  unfold polynomialMaynardDenominator_eps polynomialMaynardDenominator
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hdeg : k + ∑ i, (p.1 + q.1) i = k + 2 * α.degree := by
    have hsum : (∑ i, (p.1 + q.1) i) = (∑ i, p.1 i) + (∑ i, q.1 i) := by
      simp only [Pi.add_apply]; exact Finset.sum_add_distrib
    rw [hsum, orbitSum_term_degree α hp, orbitSum_term_degree α hq]; ring
  rw [hdeg]; ring

/-- `affineSlackRat` is invariant under the value-preserving `removeNth` reindexing, exactly like
`dirichletIntegralWithSlack` (it is a `(1-ε)`-weighted `∑ₘ` of `dirichletIntegralWithSlack`s, plus a
`(1-ε)^(n+∑)` prefactor — and both the sum-of-coords and each `dirichletIntegralWithSlack` are
removeNth-perm-invariant). -/
lemma affineSlackRat_removeNth_perm_add {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (β : ℕ) (ε : ℚ) :
    affineSlackRat (Fin.removeNth i ((fun m => a (σ m)) + (fun m => b (σ m)))) β ε
      = affineSlackRat (Fin.removeNth (σ i) (a + b)) β ε := by
  unfold affineSlackRat
  have hsum : (∑ j, (Fin.removeNth i ((fun m => a (σ m)) + (fun m => b (σ m)))) j)
      = ∑ j, (Fin.removeNth (σ i) (a + b)) j := removeNth_sum_comp_perm σ (a + b) i
  rw [hsum]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [dirichletIntegralWithSlack_removeNth_perm_add σ a b i (β - m)]

/-- **ε-numerator orbit constancy** — the verbatim ε-analog of `dirichletNum_orbitSum_const`, with
`affineSlackRat` and `affineSlackRat_removeNth_perm_add` in place of the plain Dirichlet versions.
Individual `i`-terms are not orbit-invariant, but their `i`-sum is (reindex `q ↦ q ∘ σ`, then `i`
by `σ`). -/
lemma affineNum_orbitSum_const {n : ℕ} (α : MultiIndex (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (ε : ℚ) :
    (∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
        (1 : ℚ) / (((α (σ i) + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          affineSlackRat (Fin.removeNth i ((fun m => α (σ m)) + q))
            (α (σ i) + q i + 2) ε)
      = ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
        (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          affineSlackRat (Fin.removeNth i (α + q)) (α i + q i + 2) ε := by
  have hinj : ∀ x ∈ monoOrbit α, ∀ y ∈ monoOrbit α,
      (fun i => x (σ i) : MultiIndex (n + 1)) = (fun i => y (σ i)) → x = y := by
    intro x _ y _ h
    funext i
    have := congrFun h (σ.symm i)
    simpa using this
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  conv_lhs => rw [← monoOrbit_image_comp α σ]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [affineSlackRat_removeNth_perm_add σ α q i]

/-- **ε-numerator reduction for an orbit sum** — the ε-analog of
`polynomialMaynardNumerator_orbitSum`. -/
theorem polynomialMaynardNumerator_eps_orbitSum {n : ℕ} (α : MultiIndex (n + 1)) (ε : ℚ) :
    polynomialMaynardNumerator_eps (orbitSum α) ε
      = (monoOrbit α).card •
          ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
            (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
              affineSlackRat (Fin.removeNth i (α + q)) (α i + q i + 2) ε := by
  have hinj : ∀ a ∈ monoOrbit α, ∀ b ∈ monoOrbit α,
      ((a, (1 : ℚ)) : MultiIndex (n + 1) × ℚ) = (b, 1) → a = b :=
    fun a _ b _ h => ((Prod.mk.injEq _ _ _ _).mp h).1
  have hterms : (orbitSum α).terms
      = (monoOrbit α).image (fun m : MultiIndex (n + 1) => (m, (1 : ℚ))) := by
    unfold orbitSum monoOrbit
    rw [Finset.image_image]
    rfl
  have key : polynomialMaynardNumerator_eps (orbitSum α) ε
      = ∑ i : Fin (n + 1), ∑ pm ∈ monoOrbit α, ∑ qm ∈ monoOrbit α,
          (1 : ℚ) / (((pm i + 1 : ℕ) : ℚ) * ((qm i + 1 : ℕ) : ℚ)) *
            affineSlackRat (Fin.removeNth i (pm + qm)) (pm i + qm i + 2) ε := by
    simp only [polynomialMaynardNumerator_eps]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hterms, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun pm _ => ?_)
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun qm _ => ?_)
    simp
  rw [key, Finset.sum_comm]
  have hconst : ∀ pm ∈ monoOrbit α,
      (∑ i : Fin (n + 1), ∑ qm ∈ monoOrbit α,
          (1 : ℚ) / (((pm i + 1 : ℕ) : ℚ) * ((qm i + 1 : ℕ) : ℚ)) *
            affineSlackRat (Fin.removeNth i (pm + qm)) (pm i + qm i + 2) ε)
        = ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
          (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
            affineSlackRat (Fin.removeNth i (α + q)) (α i + q i + 2) ε := by
    intro pm hpm
    simp only [monoOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hpm
    obtain ⟨σ, hσ⟩ := hpm
    rw [← hσ]
    exact affineNum_orbitSum_const α σ ε
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]

end BoundedGaps.SymmetricReductionEps
