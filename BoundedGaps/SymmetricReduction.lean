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

/-! ## Numerator permutation-invariance

The numerator of the Maynard ratio (`polynomialMaynardNumerator`) is a sum over a
coordinate `i` of squared "drop-`i`" marginals, each a `dirichletIntegralWithSlack` of the
removed-`i` exponent vector. Permuting the coordinates by `σ` permutes the *values* of that
removed vector without changing the multiset, so each marginal is unchanged up to a
reindexing of the outer `i`-sum.

The key arithmetic fact: `Fin.removeNth i (w ∘ σ)` and `Fin.removeNth (σ i) w` delete the
*same value* `w (σ i)` from `w`, so they share both `∑` and `∏ (·)!`. We never build the
induced permutation on `Fin n`; we cancel `w (σ i)` directly. -/

/-- Deleting position `i` from `w ∘ σ` and deleting position `σ i` from `w` leave the same
coordinate sum (both drop the value `w (σ i)`). -/
lemma removeNth_sum_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
    (∑ j, (Fin.removeNth i (fun m => w (σ m))) j) = ∑ j, (Fin.removeNth (σ i) w) j := by
  simp only [Fin.removeNth]
  have h1 : ∑ m, w (σ m) = w (σ i) + ∑ j : Fin n, w (σ (i.succAbove j)) :=
    Fin.sum_univ_succAbove (fun m => w (σ m)) i
  have h2 : ∑ m, w m = w (σ i) + ∑ j : Fin n, w ((σ i).succAbove j) :=
    Fin.sum_univ_succAbove w (σ i)
  have h3 : ∑ m, w (σ m) = ∑ m, w m := Equiv.sum_comp σ w
  omega

/-- The product-of-factorials version of `removeNth_sum_comp_perm`. -/
lemma removeNth_prodFactorial_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
    (∏ j, ((Fin.removeNth i (fun m => w (σ m))) j).factorial)
      = ∏ j, ((Fin.removeNth (σ i) w) j).factorial := by
  simp only [Fin.removeNth]
  have h1 : ∏ m, (w (σ m)).factorial
      = (w (σ i)).factorial * ∏ j : Fin n, (w (σ (i.succAbove j))).factorial :=
    Fin.prod_univ_succAbove (fun m => (w (σ m)).factorial) i
  have h2 : ∏ m, (w m).factorial
      = (w (σ i)).factorial * ∏ j : Fin n, (w ((σ i).succAbove j)).factorial :=
    Fin.prod_univ_succAbove (fun m => (w m).factorial) (σ i)
  have h3 : ∏ m, (w (σ m)).factorial = ∏ m, (w m).factorial :=
    Equiv.prod_comp σ (fun m => (w m).factorial)
  have key : (w (σ i)).factorial * ∏ j, (w (σ (i.succAbove j))).factorial
      = (w (σ i)).factorial * ∏ j, (w ((σ i).succAbove j)).factorial := by
    rw [← h1, h3, h2]
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) key

/-- `dirichletIntegralWithSlack` depends only on `∑ α` and `∏ (α ·)!`, so it is invariant
under the value-preserving reindexing of `removeNth` from `removeNth_*_comp_perm`. -/
lemma dirichletIntegralWithSlack_removeNth_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (β : ℕ) :
    dirichletIntegralWithSlack (Fin.removeNth i (fun m => w (σ m))) β
      = dirichletIntegralWithSlack (Fin.removeNth (σ i) w) β := by
  unfold dirichletIntegralWithSlack
  rw [removeNth_sum_comp_perm σ w i,
      show (∏ j, (((Fin.removeNth i (fun m => w (σ m))) j).factorial : ℚ))
          = ∏ j, (((Fin.removeNth (σ i) w) j).factorial : ℚ) from by
        rw [← Nat.cast_prod, ← Nat.cast_prod, removeNth_prodFactorial_comp_perm σ w i]]

/-- The shape in which the invariance appears inside the numerator: the removed exponent
vector is `(p.1 ∘ σ) + (q.1 ∘ σ)` (a `Pi.add` of two precomposed functions). -/
lemma dirichletIntegralWithSlack_removeNth_perm_add {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (β : ℕ) :
    dirichletIntegralWithSlack
        (Fin.removeNth i ((fun m => a (σ m)) + (fun m => b (σ m)))) β
      = dirichletIntegralWithSlack (Fin.removeNth (σ i) (a + b)) β :=
  dirichletIntegralWithSlack_removeNth_comp_perm σ (a + b) i β

/-- **Numerator permutation-invariance.** Permuting the `k` coordinates leaves the numerator
of the Maynard ratio unchanged. -/
theorem polynomialMaynardNumerator_permWeight {k : ℕ} (σ : Equiv.Perm (Fin k))
    (P : PolynomialSieveWeight k) :
    polynomialMaynardNumerator (permWeight σ P) = polynomialMaynardNumerator P := by
  cases k with
  | zero => rfl
  | succ n =>
    simp only [polynomialMaynardNumerator, permWeight]
    refine Fintype.sum_equiv σ _ _ (fun i => ?_)
    rw [Finset.sum_image (fun x _ y _ h => permTerm_injective σ h)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_image (fun x _ y _ h => permTerm_injective σ h)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    dsimp only
    rw [dirichletIntegralWithSlack_removeNth_perm_add σ p.1 q.1 i]

/-- **Full Rayleigh-ratio permutation-invariance.** Both numerator and denominator are
invariant, so the polynomial Maynard ratio is invariant under coordinate permutations —
the bedrock fact that makes restricting to *symmetric* test functions WLOG. -/
theorem polynomialMkF_permWeight {k : ℕ} (σ : Equiv.Perm (Fin k))
    (P : PolynomialSieveWeight k) :
    polynomialMkF (permWeight σ P) = polynomialMkF P := by
  unfold polynomialMkF
  rw [polynomialMaynardNumerator_permWeight, polynomialMaynardDenominator_permWeight]

/-! ## Toward the matching closed form (the orbit-sum kernel)

The next layer (the genuine multi-session kernel; see `tools/mk/SYMMETRIC_REDUCTION.md`)
collapses an orbit-pair sum to `(1/aut) · Σ_M ff(k,T)·W(M) / (k+|λ|+|μ|)!`, where `ff(k,T)`
is the number of ways to drop `T` labelled tokens into distinct slots of `Fin k`. The single
arithmetic fact underpinning that "parametric in `k`" structure — the placement count is the
falling factorial `k(k-1)⋯(k-T+1) = Nat.descFactorial k T`, a polynomial in `k` — is the
piece below. Everything else in the kernel (the overlap-pattern bijection, the weight `W(M)`)
is layered on top of it. -/

/-- **Placement count = falling factorial.** The number of ways to place `T` distinguishable
tokens into distinct slots of `Fin k` (i.e. injections `Fin T ↪ Fin k`) is the falling
factorial `ff(k,T) = k(k-1)⋯(k-T+1) = Nat.descFactorial k T`. This is the `ff(k,T)` factor in
the matching closed form, and the source of its polynomial-in-`k` character. -/
lemma placement_count (k T : ℕ) :
    Fintype.card (Fin T ↪ Fin k) = k.descFactorial T := by
  simp [Fintype.card_embedding_eq]

/-! ## Orbit-symmetric weights (foundation for the matching closed form)

A symmetric test function is a `ℚ`-combination of *orbit sums*: for a multi-index `α`, its
orbit sum collects every coordinate-permutation `α ∘ σ` of the exponent vector, each with
coefficient `1`. The matching closed form (the kernel) computes the Rayleigh ratio of such a
combination from its few orbit coefficients. The foundational fact below is that an orbit sum
is genuinely symmetric — fixed by the coordinate action `permWeight` — so it is a legitimate
symmetric test weight, and `polynomialMkF (∑ cᵢ • orbitSum αᵢ)` is what the kernel reduces. -/

/-- The `Perm (Fin k)`-orbit of a monomial `α` as a symmetric polynomial sieve weight: every
coordinate-permutation `α ∘ σ` of the exponent vector, each with coefficient `1`. -/
noncomputable def orbitSum {k : ℕ} (α : MultiIndex k) : PolynomialSieveWeight k :=
  ⟨Finset.univ.image
    (fun σ : Equiv.Perm (Fin k) => ((fun i => α (σ i) : MultiIndex k), (1 : ℚ)))⟩

/-- **Joint-type invariance of a denominator entry.** The denominator contribution
`monomialIntegral (p + q)` of a term-pair is invariant under simultaneously permuting both
exponent vectors by the same `σ`. Hence it depends only on the *joint type* of the pair (the
multiset of coordinatewise sums), not on the particular placement — the seed of the
overlap-pattern grouping in the matching closed form. -/
lemma monomialIntegral_add_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (α β : MultiIndex k) :
    monomialIntegral ((fun i => α (σ i)) + (fun i => β (σ i))) = monomialIntegral (α + β) := by
  have : ((fun i => α (σ i)) + (fun i => β (σ i)) : MultiIndex k)
      = (fun i => (α + β) (σ i)) := rfl
  rw [this, monomialIntegral_comp_perm σ (α + β)]

/-- An orbit sum lands in the symmetric subspace: it is fixed by every coordinate
permutation `τ`. (As `σ` ranges over all permutations, so does `σ * τ`.) -/
lemma permWeight_orbitSum {k : ℕ} (τ : Equiv.Perm (Fin k)) (α : MultiIndex k) :
    permWeight τ (orbitSum α) = orbitSum α := by
  unfold permWeight orbitSum
  congr 1
  rw [Finset.image_image]
  apply Finset.ext
  intro pc
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨σ * τ, ?_⟩
    rfl
  · rintro ⟨ρ, rfl⟩
    refine ⟨ρ * τ⁻¹, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    funext i
    simp [Equiv.Perm.mul_apply]

/-! ## Next: the orbit-sum reduction (host-preferred — the Finset `sum_bij` plumbing below
wants fast interactive feedback, not the box's slow build loop)

With the foundations above (`orbitSum`, `permWeight_orbitSum`, `monomialIntegral_add_comp_perm`)
the matching closed form proceeds via these concrete obligations:

1. `orbitSum_denom_const` — the inner sum `∑ q ∈ orbit(α), monomialIntegral (p + q)` is the SAME
   for every `p ∈ orbit(α)`. Proof: `monomialIntegral ((α∘σ) + q) = monomialIntegral (α + q∘σ⁻¹)`
   — apply `monomialIntegral_comp_perm` with `σ⁻¹`, so the `α∘σ` cancels to `α` while `q` picks up
   `∘σ⁻¹` — then reindex the `q`-sum by the orbit bijection `q ↦ q∘σ⁻¹` (`Finset.sum_bij'` with
   inverse `q ↦ q∘σ`; the orbit is closed since `(α∘ρ)∘σ⁻¹ = α∘(ρ*σ⁻¹)`).
2. ⟹ `polynomialMaynardDenominator (orbitSum α) = (orbit.card) • (inner sum at a fixed rep)`, and
   the analogous numerator reduction via `dirichletIntegralWithSlack_removeNth_comp_perm`.
3. The cross-orbit overlap count (the genuine combinatorial kernel): collapse
   `∑ over orbit(λ) × orbit(μ)` to `(1/aut)·∑_M ff(k,T)·W(M)` grouped by overlap pattern `M`
   (a partial matching of `λ`-parts to `μ`-parts sharing a slot), with `ff(k,T) = k.descFactorial T`
   (`placement_count`). Validated Python prototype: `tools/mk/mk_sym.py`; full plan + the exact
   reaches-4 table (deg ≤ 8 < 4 at k=50,54 ⟹ witness degree ≥ 9) in `tools/mk/SYMMETRIC_REDUCTION.md`.
-/

end BoundedGaps.SymmetricReduction
