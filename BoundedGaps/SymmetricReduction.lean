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

/-- The orbit of a monomial `α` as a `Finset` of exponent vectors (the distinct
coordinate-permutations of `α`). This is the index set of `orbitSum α`'s monomials. -/
noncomputable def monoOrbit {k : ℕ} (α : MultiIndex k) : Finset (MultiIndex k) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin k) => (fun i => α (σ i) : MultiIndex k))

/-- The orbit is closed under right-composition by any permutation `σ`, and `q ↦ q ∘ σ` is a
bijection of the orbit (as `ρ` ranges over all permutations, so does `ρ * σ`). Hence
post-composing the orbit's elements by `σ` leaves the orbit `Finset` unchanged. -/
lemma monoOrbit_image_comp {k : ℕ} (α : MultiIndex k) (σ : Equiv.Perm (Fin k)) :
    (monoOrbit α).image (fun q i => q (σ i)) = monoOrbit α := by
  unfold monoOrbit
  rw [Finset.image_image]
  apply Finset.ext
  intro p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ * σ, by funext i; simp [Equiv.Perm.mul_apply]⟩
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ * σ⁻¹, by funext i; simp [Equiv.Perm.mul_apply]⟩

/-- **The orbit-sum reduction (denominator core).** For every representative `α ∘ σ` of the
orbit, the inner sum `∑ q ∈ orbit, monomialIntegral (rep + q)` takes the SAME value. Proof:
reindex the `q`-sum by the orbit bijection `q ↦ q ∘ σ` (`monoOrbit_image_comp`), turning each
term into `monomialIntegral ((α ∘ σ) + (q ∘ σ)) = monomialIntegral ((α + q) ∘ σ)`, which equals
`monomialIntegral (α + q)` by `monomialIntegral_comp_perm`. This is the collapse that makes the
denominator of `orbitSum α` equal `(orbit card) • (inner sum at α)`. -/
lemma monomialIntegral_orbitSum_const {k : ℕ} (α : MultiIndex k) (σ : Equiv.Perm (Fin k)) :
    ∑ q ∈ monoOrbit α, monomialIntegral ((fun i => α (σ i)) + q)
      = ∑ q ∈ monoOrbit α, monomialIntegral (α + q) := by
  have hinj : ∀ x ∈ monoOrbit α, ∀ y ∈ monoOrbit α,
      (fun i => x (σ i) : MultiIndex k) = (fun i => y (σ i)) → x = y := by
    intro x _ y _ h
    funext i
    have := congrFun h (σ.symm i)
    simpa using this
  calc ∑ q ∈ monoOrbit α, monomialIntegral ((fun i => α (σ i)) + q)
      = ∑ q ∈ (monoOrbit α).image (fun q i => q (σ i)),
          monomialIntegral ((fun i => α (σ i)) + q) := by rw [monoOrbit_image_comp α σ]
    _ = ∑ q ∈ monoOrbit α,
          monomialIntegral ((fun i => α (σ i)) + (fun i => q (σ i))) :=
        Finset.sum_image hinj
    _ = ∑ q ∈ monoOrbit α, monomialIntegral (α + q) := by
        apply Finset.sum_congr rfl
        intro q _
        have h : ((fun i => α (σ i)) + (fun i => q (σ i)) : MultiIndex k)
            = (fun i => (α + q) (σ i)) := rfl
        rw [h, monomialIntegral_comp_perm σ (α + q)]

/-- **Denominator reduction for an orbit sum.** Assembling the constancy lemma: the simplex
integral of `(orbitSum α)²` is `(orbit card)` copies of the inner sum at the representative `α`.
This is the `Mr`-entry of the matching closed form for the diagonal pair `λ = μ = α`, modulo the
final factorial normalization. -/
theorem polynomialMaynardDenominator_orbitSum {k : ℕ} (α : MultiIndex k) :
    polynomialMaynardDenominator (orbitSum α)
      = (monoOrbit α).card • ∑ q ∈ monoOrbit α, monomialIntegral (α + q) := by
  have hinj : ∀ a ∈ monoOrbit α, ∀ b ∈ monoOrbit α,
      ((a, (1 : ℚ)) : MultiIndex k × ℚ) = (b, 1) → a = b :=
    fun a _ b _ h => ((Prod.mk.injEq _ _ _ _).mp h).1
  have hterms : (orbitSum α).terms
      = (monoOrbit α).image (fun m : MultiIndex k => (m, (1 : ℚ))) := by
    unfold orbitSum monoOrbit
    rw [Finset.image_image]
    rfl
  have key : polynomialMaynardDenominator (orbitSum α)
      = ∑ pm ∈ monoOrbit α, ∑ qm ∈ monoOrbit α, monomialIntegral (pm + qm) := by
    unfold polynomialMaynardDenominator
    rw [hterms, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun pm _ => ?_)
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun qm _ => ?_)
    simp
  rw [key]
  have hconst : ∀ pm ∈ monoOrbit α,
      ∑ qm ∈ monoOrbit α, monomialIntegral (pm + qm)
        = ∑ q ∈ monoOrbit α, monomialIntegral (α + q) := by
    intro pm hpm
    simp only [monoOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hpm
    obtain ⟨σ, hσ⟩ := hpm
    rw [← hσ]
    exact monomialIntegral_orbitSum_const α σ
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]

/-- **Numerator orbit constancy** (the analog of `monomialIntegral_orbitSum_const`). For each
representative `α ∘ σ` of the orbit, the numerator's inner double-sum over the removed index `i`
and the orbit element `q` takes the SAME value as at `α`. Unlike the denominator, the individual
`i`-terms are *not* orbit-invariant — but their sum over `i` is. Proof: reindex the inner `q`-sum
by the orbit bijection `q ↦ q ∘ σ` (`monoOrbit_image_comp` + `dirichletIntegralWithSlack_removeNth_perm_add`),
which turns the `i`-term at rep `α ∘ σ` into the `(σ i)`-term at rep `α`; then reindex the outer
`i`-sum by `σ` (`Fintype.sum_equiv`), re-collecting all indices. -/
lemma dirichletNum_orbitSum_const {n : ℕ} (α : MultiIndex (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
        (1 : ℚ) / (((α (σ i) + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack (Fin.removeNth i ((fun m => α (σ m)) + q))
            (α (σ i) + q i + 2))
      = ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
        (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack (Fin.removeNth i (α + q)) (α i + q i + 2) := by
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
  rw [dirichletIntegralWithSlack_removeNth_perm_add σ α q i]

/-- **Numerator reduction for an orbit sum.** The numerator of `orbitSum α` equals
`(orbit card)` copies of the inner double-sum (over removed index `i` and orbit element `q`) at
the single representative `α`. Same three-step shape as `polynomialMaynardDenominator_orbitSum`
(`orbitSum.terms ↦ monoOrbit` via `sum_image`; constancy; `sum_const`), with the constancy step
upgraded to the `i`-summed `dirichletNum_orbitSum_const`. -/
theorem polynomialMaynardNumerator_orbitSum {n : ℕ} (α : MultiIndex (n + 1)) :
    polynomialMaynardNumerator (orbitSum α)
      = (monoOrbit α).card •
          ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
            (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
              dirichletIntegralWithSlack (Fin.removeNth i (α + q)) (α i + q i + 2) := by
    have hinj : ∀ a ∈ monoOrbit α, ∀ b ∈ monoOrbit α,
        ((a, (1 : ℚ)) : MultiIndex (n + 1) × ℚ) = (b, 1) → a = b :=
      fun a _ b _ h => ((Prod.mk.injEq _ _ _ _).mp h).1
    have hterms : (orbitSum α).terms
        = (monoOrbit α).image (fun m : MultiIndex (n + 1) => (m, (1 : ℚ))) := by
      unfold orbitSum monoOrbit
      rw [Finset.image_image]
      rfl
    have key : polynomialMaynardNumerator (orbitSum α)
        = ∑ i : Fin (n + 1), ∑ pm ∈ monoOrbit α, ∑ qm ∈ monoOrbit α,
            (1 : ℚ) / (((pm i + 1 : ℕ) : ℚ) * ((qm i + 1 : ℕ) : ℚ)) *
              dirichletIntegralWithSlack (Fin.removeNth i (pm + qm)) (pm i + qm i + 2) := by
      simp only [polynomialMaynardNumerator]
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
              dirichletIntegralWithSlack (Fin.removeNth i (pm + qm)) (pm i + qm i + 2))
          = ∑ i : Fin (n + 1), ∑ q ∈ monoOrbit α,
            (1 : ℚ) / (((α i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
              dirichletIntegralWithSlack (Fin.removeNth i (α + q)) (α i + q i + 2) := by
      intro pm hpm
      simp only [monoOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hpm
      obtain ⟨σ, hσ⟩ := hpm
      rw [← hσ]
      exact dirichletNum_orbitSum_const α σ
    rw [Finset.sum_congr rfl hconst, Finset.sum_const]

/-- Every element of `monoOrbit α` has total degree `α.degree` (a permutation preserves the
coordinate sum). The bare-index analog of the term-degree fact used on the ε side. -/
lemma monoOrbit_mem_degree {k : ℕ} (α : MultiIndex k) {p : MultiIndex k}
    (hp : p ∈ monoOrbit α) : (∑ i, p i) = α.degree := by
  simp only [monoOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨σ, hσ⟩ := hp
  rw [← hσ]
  simpa [MultiIndex.degree] using Equiv.sum_comp σ (fun i => α i)

/-- **The cross-orbit denominator core.** The off-diagonal orbit-pair sum
`∑_{p∈orbit α} ∑_{q∈orbit β} monomialIntegral (p+q)` factors out the *constant* `monomialIntegral`
denominator `(k+|α|+|β|)!` — constant because `(p+q).degree = α.degree + β.degree` for every pair
of orbit elements — leaving the purely combinatorial sum `∑∑ ∏ᵢ (pᵢ+qᵢ)!`. This isolates the
content the matching/overlap closed form must count: the `monomialIntegral` analysis is fully
discharged, and what remains (collapsing `∑∑ ∏ᵢ (pᵢ+qᵢ)!` to `∑_M ff(k,T)·W(M)` over overlap
patterns) is a pure combinatorial identity. The diagonal `β = α` recovers
`polynomialMaynardDenominator_orbitSum`'s inner sum. -/
lemma orbitPair_denominator_eq {k : ℕ} (α β : MultiIndex k) :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, monomialIntegral (p + q)
      = (∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, (∏ i, ((p i + q i).factorial : ℚ)))
          / ((k + α.degree + β.degree).factorial : ℚ) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hsplit : (∑ i, (p + q) i) = (∑ i, p i) + (∑ i, q i) := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hdeg : (p + q).degree = α.degree + β.degree := by
    show (∑ i, (p + q) i) = α.degree + β.degree
    rw [hsplit, monoOrbit_mem_degree α hp, monoOrbit_mem_degree β hq]
  unfold monomialIntegral
  rw [hdeg, ← add_assoc]
  simp only [Pi.add_apply]

/-- **Cross-orbit core constancy.** For a fixed `α`, the sum `∑_{p∈orbit α} ∏ᵢ (pᵢ + qᵢ)!` is the
SAME for every representative `q = β ∘ τ` of `orbit β` as at `β`. Proof: reindex the `p`-sum by the
orbit bijection `p ↦ p ∘ τ` (`monoOrbit_image_comp`), turning `∏ᵢ (p(τ i) + β(τ i))!` into
`∏ᵢ ((p+β)(τ i))!`, then reindex the *product* over `i` by `τ` (`Equiv.prod_comp`). -/
lemma orbitCore_const {k : ℕ} (α β : MultiIndex k) (τ : Equiv.Perm (Fin k)) :
    ∑ p ∈ monoOrbit α, (∏ i, ((p i + (fun j => β (τ j)) i).factorial : ℚ))
      = ∑ p ∈ monoOrbit α, (∏ i, ((p i + β i).factorial : ℚ)) := by
  have hinj : ∀ x ∈ monoOrbit α, ∀ y ∈ monoOrbit α,
      (fun i => x (τ i) : MultiIndex k) = (fun i => y (τ i)) → x = y := by
    intro x _ y _ h
    funext i
    have := congrFun h (τ.symm i)
    simpa using this
  conv_lhs => rw [← monoOrbit_image_comp α τ]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact Equiv.prod_comp τ (fun j => ((p j + β j).factorial : ℚ))

/-- **Cross-orbit core: double sum collapses to a single orbit sum.** The off-diagonal
combinatorial core isolated by `orbitPair_denominator_eq` reduces to `|orbit β|` copies of the
single-orbit sum `∑_{p∈orbit α} ∏ᵢ (pᵢ + βᵢ)!` against the fixed representative `β` (the inner
`p`-sum is constant over `q ∈ orbit β` by `orbitCore_const`). What remains for the matching closed
form is then to evaluate this one structured sum (a permanent over a matrix with few distinct
rows/columns) as `∑_M (k.descFactorial T)·W(M)`. -/
lemma orbitPair_core_const {k : ℕ} (α β : MultiIndex k) :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, (∏ i, ((p i + q i).factorial : ℚ))
      = (monoOrbit β).card • ∑ p ∈ monoOrbit α, (∏ i, ((p i + β i).factorial : ℚ)) := by
  rw [Finset.sum_comm]
  have hconst : ∀ q ∈ monoOrbit β,
      ∑ p ∈ monoOrbit α, (∏ i, ((p i + q i).factorial : ℚ))
        = ∑ p ∈ monoOrbit α, (∏ i, ((p i + β i).factorial : ℚ)) := by
    intro q hq
    simp only [monoOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨τ, hτ⟩ := hq
    rw [← hτ]
    exact orbitCore_const α β τ
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]

/-- **Orbit sum via the symmetric group (constant-fiber / orbit-stabilizer bridge).** Summing `f`
over the *distinct* orbit `monoOrbit α` and summing `f (α ∘ σ)` over the whole symmetric group
differ exactly by the stabilizer size: every fiber of `σ ↦ α ∘ σ` over an orbit element is a coset
of the stabilizer `{σ : α ∘ σ = α}` (bijection `σ ↦ σ * ρ⁻¹` for a fixed preimage `ρ`), so all
fibers share its cardinality. This is the orbit-stabilizer step that lets the matching enumeration
operate over the group — where the overlap-pattern grouping of `∑_σ ∏ᵢ (α(σ i)+βᵢ)!` (a permanent)
lives — rather than over distinct multisets. -/
lemma group_sum_eq_stab_smul_orbitSum {k : ℕ} (α : MultiIndex k) (f : MultiIndex k → ℚ) :
    ∑ σ : Equiv.Perm (Fin k), f (fun i => α (σ i))
      = (Finset.univ.filter
            (fun σ : Equiv.Perm (Fin k) => (fun i => α (σ i) : MultiIndex k) = α)).card •
          ∑ p ∈ monoOrbit α, f p := by
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))),
      (fun i => α (σ i) : MultiIndex k) ∈ monoOrbit α :=
    fun σ _ => Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ => f (fun i => α (σ i))), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hfib : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => (fun i => α (σ i)) = p),
      f (fun i => α (σ i)) = f p := fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  congr 1
  obtain ⟨ρ, -, hρ⟩ := Finset.mem_image.mp hp
  apply Finset.card_bij (fun σ _ => σ * ρ⁻¹)
  · intro σ hσ
    have hσp : (fun i => α (σ i) : MultiIndex k) = p := (Finset.mem_filter.mp hσ).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    have hinv : ρ (ρ⁻¹ i) = i := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have hi : α (σ (ρ⁻¹ i)) = α i := by
      rw [congrFun hσp (ρ⁻¹ i), ← congrFun hρ (ρ⁻¹ i), hinv]
    simpa [Equiv.Perm.mul_apply] using hi
  · intro σ₁ _ σ₂ _ he
    exact mul_right_cancel he
  · intro τ hτ
    have hτs : (fun i => α (τ i) : MultiIndex k) = α := (Finset.mem_filter.mp hτ).2
    refine ⟨τ * ρ, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      funext i
      simp only [Equiv.Perm.mul_apply]
      rw [congrFun hτs (ρ i), congrFun hρ i]
    · group

/-! ## Status + next obligations toward the matching closed form

DONE (this file, axiom-clean): the symmetric-subspace foundations (`orbitSum`,
`permWeight_orbitSum`, `monomialIntegral_add_comp_perm`); the conceptual core — the **orbit-sum
constancy reduction** (`monomialIntegral_orbitSum_const`, via `monoOrbit_image_comp`); and the
**denominator assembly** (`polynomialMaynardDenominator_orbitSum`: the denominator of `orbitSum α`
is `(monoOrbit α).card • ∑ q ∈ monoOrbit α, monomialIntegral (α + q)` — the diagonal `Mr`-entry,
modulo the factorial normalization `(k+|α|+|α|)!`); and the **numerator assembly**
(`polynomialMaynardNumerator_orbitSum`: the numerator of `orbitSum α` is
`(monoOrbit α).card • ∑ i ∑ q, [1/((αᵢ+1)(qᵢ+1))]·dirichletIntegralWithSlack (removeNth i (α+q)) (αᵢ+qᵢ+2)`,
via the `i`-summed constancy `dirichletNum_orbitSum_const`). With both, the full diagonal `Mr`-ratio
of a single orbit sum is a closed form in the orbit's representative.

The numerator constancy was subtler than the denominator's: individual `i`-terms are NOT
orbit-invariant (the `(pᵢ+1)(qᵢ+1)` denominators and the `removeNth i` couple to `i`), but the
*sum over `i`* is — reindexing `q ↦ q ∘ σ` turns the `i`-term at rep `α ∘ σ` into the `(σ i)`-term
at rep `α`, and summing over `i` (`Fintype.sum_equiv σ`) re-collects them all.

Also DONE: `orbitPair_denominator_eq` — the **cross-orbit denominator core**: the off-diagonal
pair sum `∑_{p∈orbit α}∑_{q∈orbit β} monomialIntegral (p+q)` factors out the constant denominator
`(k+|α|+|β|)!`, fully discharging the `monomialIntegral` analysis and isolating the pure
combinatorial sum `∑∑ ∏ᵢ (pᵢ+qᵢ)!` that the matching count must collapse. (The ε-flavored orbit
reductions live in `SymmetricReductionEps.lean` — same machinery, for the unconditional `Mk_eps`
flagship.)

Remaining (the genuine multi-session combinatorial kernel — shared bottleneck for BOTH the
EH-conditional plain-`Mk` ladder AND the unconditional `Mk_eps 50` flagship):

3. **Cross-orbit overlap count**: collapse the now-isolated `∑_{p∈orbit α}∑_{q∈orbit β} ∏ᵢ (pᵢ+qᵢ)!`
   to `(1/aut)·∑_M ff(k,T)·W(M)` grouped by overlap pattern `M` (a partial matching of `α`-parts to
   `β`-parts sharing a slot), with `ff(k,T) = k.descFactorial T` (`placement_count`). Needs: an
   orbit→labelled-placement bijection counted by `placement_count`, the weight `W(M)`, and that
   `∏ᵢ (pᵢ+qᵢ)!` depends only on the overlap type. Validated Python prototype: `tools/mk/mk_sym.py`;
   exact reaches-4 table (deg ≤ 8 < 4 at k=50,54 ⟹ witness degree ≥ 9) in `tools/mk/SYMMETRIC_REDUCTION.md`.
-/

end BoundedGaps.SymmetricReduction
