import BoundedGaps.SymmetricReductionOrbitFree

open Finset
open scoped Nat

namespace BoundedGaps
namespace OrbitFree

open SymmetricReduction SievePolynomial

/-- **Reindex: double `S_k`-sum collapses to `k!` copies of a single-permutation sum.** For a
jointly permutation-invariant `Ψ` (`Ψ (p∘ρ) (q∘ρ) = Ψ p q`), summing `Ψ (A∘σ) (B∘τ)` over all
`(σ,τ)` equals `k!` times the "permanent-shaped" sum `∑_π Ψ A (B∘π)`. (P3 step 2.) -/
theorem permSum_reindex {k : ℕ} {R : Type*} [AddCommMonoid R]
    (A B : MultiIndex k) (Ψ : MultiIndex k → MultiIndex k → R)
    (hinv : ∀ (p q : MultiIndex k) (ρ : Equiv.Perm (Fin k)),
        Ψ (fun i => p (ρ i)) (fun i => q (ρ i)) = Ψ p q) :
    (∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
        Ψ (fun i => A (σ i)) (fun i => B (τ i)))
      = (k)! • ∑ π : Equiv.Perm (Fin k), Ψ A (fun i => B (π i)) := by
  classical
  have hconst : ∀ σ : Equiv.Perm (Fin k),
      (∑ τ : Equiv.Perm (Fin k), Ψ (fun i => A (σ i)) (fun i => B (τ i)))
        = ∑ π : Equiv.Perm (Fin k), Ψ A (fun i => B (π i)) := by
    intro σ
    have step1 : ∀ τ : Equiv.Perm (Fin k),
        Ψ (fun i => A (σ i)) (fun i => B (τ i))
          = Ψ A (fun i => B ((τ * σ⁻¹) i)) := by
      intro τ
      have h := hinv A (fun i => B ((τ * σ⁻¹) i)) σ
      have heq : (fun i => B ((τ * σ⁻¹) (σ i))) = (fun i => B (τ i)) := by
        funext i
        simp [Equiv.Perm.mul_apply]
      rw [heq] at h
      exact h
    rw [Finset.sum_congr rfl (fun τ _ => step1 τ)]
    exact Equiv.sum_comp (Equiv.mulRight σ⁻¹) (fun π => Ψ A (fun i => B (π i)))
  rw [Finset.sum_congr rfl (fun σ _ => hconst σ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **Two-axis lift.** The orbit double-sum, scaled by the four combinatorial factors
`(k-|La|)!·autParts La·(k-|Lb|)!·autParts Lb`, equals the full `S_k × S_k` sum. (P3, both axes of
`ofParts_autParts_orbit_sum`.) -/
theorem orbitPair_to_permSum {k : ℕ} {R : Type*} [AddCommMonoid R]
    (La Lb : List ℕ) (hLa : La.length ≤ k) (hLb : Lb.length ≤ k)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x)
    (Ψ : MultiIndex k → MultiIndex k → R) :
    (∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k),
        Ψ (fun i => (ofParts La : MultiIndex k) (σ i)) (fun i => (ofParts Lb) (τ i)))
      = ((k - La.length)! * autParts La * ((k - Lb.length)! * autParts Lb)) •
          ∑ p ∈ monoOrbit (ofParts La : MultiIndex k),
            ∑ q ∈ monoOrbit (ofParts Lb), Ψ p q := by
  classical
  -- inner axis (τ): for every σ, collapse the τ-sum to the orbit-sum over q
  have hinner : ∀ σ : Equiv.Perm (Fin k),
      (∑ τ : Equiv.Perm (Fin k), Ψ (fun i => (ofParts La : MultiIndex k) (σ i))
          (fun i => (ofParts Lb) (τ i)))
        = (k - Lb.length)! • (autParts Lb •
            ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
              Ψ (fun i => (ofParts La : MultiIndex k) (σ i)) q) := by
    intro σ
    exact ofParts_autParts_orbit_sum Lb hLb hposb
      (fun q => Ψ (fun i => (ofParts La : MultiIndex k) (σ i)) q)
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ)]
  -- pull the two inner constants out of the σ-sum
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  -- outer axis (σ): collapse the σ-sum to the orbit-sum over p
  rw [ofParts_autParts_orbit_sum La hLa hposa
      (fun p => ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k), Ψ p q)]
  -- reconcile the nested ℕ-smul with the single product scalar
  simp only [← mul_smul]
  congr 1
  ring

/-- **Permanent-form identity (P3 steps 1+2 combined).** The orbit double-sum, scaled by the four
combinatorial factors, equals `k!` times the single-permutation ("permanent") sum
`∑_π Ψ (ofParts La) ((ofParts Lb)∘π)`. Reduces `denom_bridge`/`num_bridge` to the lone rook/permanent
expansion (P3 step 3). Requires only that `Ψ` is jointly permutation-invariant. -/
theorem orbitPair_smul_eq_permanent {k : ℕ} {R : Type*} [AddCommMonoid R]
    (La Lb : List ℕ) (hLa : La.length ≤ k) (hLb : Lb.length ≤ k)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x)
    (Ψ : MultiIndex k → MultiIndex k → R)
    (hinv : ∀ (p q : MultiIndex k) (ρ : Equiv.Perm (Fin k)),
        Ψ (fun i => p (ρ i)) (fun i => q (ρ i)) = Ψ p q) :
    ((k - La.length)! * autParts La * ((k - Lb.length)! * autParts Lb)) •
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k),
          ∑ q ∈ monoOrbit (ofParts Lb), Ψ p q)
      = (k)! • ∑ π : Equiv.Perm (Fin k),
          Ψ (ofParts La : MultiIndex k) (fun i => (ofParts Lb) (π i)) := by
  rw [← orbitPair_to_permSum La Lb hLa hLb hposa hposb Ψ,
      permSum_reindex (ofParts La) (ofParts Lb) Ψ hinv]

/-- **Denominator orbit-sum = `k!` · permanent (P3 steps 1+2, ℕ form).** The exact ℕ identity the
`denom_bridge` plumbing needs: the orbit double-sum of `∏ᵢ(pᵢ+qᵢ)!`, scaled by the four factors,
equals `k!` times the permanent of the matrix `(ofParts La j + ofParts Lb (π j))!`. The ONLY
remaining gap to `denom_bridge` is the rook expansion of this permanent (P3 step 3):
`k! · permanent = (k-|La|)!·(k-|Lb|)!·matchDenSum`. -/
theorem denom_orbitSum_eq_permanent {k : ℕ} (La Lb : List ℕ)
    (hLa : La.length ≤ k) (hLb : Lb.length ≤ k)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x) :
    ((k - La.length)! * autParts La * ((k - Lb.length)! * autParts Lb)) *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k),
          ∑ q ∈ monoOrbit (ofParts Lb), ∏ i, (p i + q i)!)
      = (k)! * ∑ π : Equiv.Perm (Fin k),
          ∏ j, ((ofParts La : MultiIndex k) j + (ofParts Lb) (π j))! := by
  have hinv : ∀ (p q : MultiIndex k) (ρ : Equiv.Perm (Fin k)),
      (∏ i, ((fun i => p (ρ i)) i + (fun i => q (ρ i)) i)!)
        = ∏ i, (p i + q i)! := by
    intro p q ρ
    exact Equiv.prod_comp ρ (fun i => (p i + q i)!)
  have h := orbitPair_smul_eq_permanent La Lb hLa hLb hposa hposb
    (fun p q => ∏ i, (p i + q i)!) hinv
  simpa only [smul_eq_mul] using h

end OrbitFree
end BoundedGaps
