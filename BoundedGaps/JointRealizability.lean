import Mathlib

open Finset Fintype

namespace BoundedGaps.JointReal

noncomputable section

/-
The image-restricted sigma fiber equivalence: the sigma of fibers over the image
    of a function is equivalent to the domain.
-/
def sigmaImageFiberEquiv {k : ℕ} (f : Fin k → ℕ) :
    (Σ (v : ↥(univ.image f)), {i : Fin k // f i = v.val}) ≃ Fin k where
  toFun := fun ⟨_, i, _⟩ => i
  invFun := fun i => ⟨⟨f i, mem_image_of_mem f (mem_univ i)⟩, i, rfl⟩
  left_inv := by
    grind +extAll
  right_inv := fun _ => rfl

/-
There exists an equivalence from the cell sigma type to `Fin k` that sends
    each cell `⟨v, b, j⟩` to a slot `i` with `α i = v.val`.
-/
lemma exists_alpha_equiv {k : ℕ} (α β : Fin k → ℕ)
    (X : ↥(univ.image α) → ↥(univ.image β) → ℕ)
    (hrow : ∀ v, ∑ b, X v b = (univ.filter (fun i => α i = v.val)).card) :
    ∃ (e : (Σ (v : ↥(univ.image α)) (b : ↥(univ.image β)), Fin (X v b)) ≃ Fin k),
      ∀ t, α (e t) = t.1.val := by
  -- By Fintype.equivOfCardEq, there exists a bijection between the v-slice of the cell type and the α-fiber.
  have h_bij : ∀ v : ↥(image α univ), ∃ e : (Σ b : ↥(image β univ), Fin (X v b)) ≃ {i : Fin k // α i = v.val}, True := by
    intro v
    have h_card : Fintype.card (Σ b : ↥(image β univ), Fin (X v b)) = Fintype.card {i : Fin k // α i = v.val} := by
      rw [Fintype.card_sigma, Fintype.card_subtype]
      simp only [Fintype.card_fin]
      exact hrow v
    exact ⟨ Fintype.equivOfCardEq h_card, trivial ⟩;
  choose e he using h_bij;
  refine' ⟨ _, _ ⟩;
  refine' ( Equiv.sigmaCongrRight e ).trans ( sigmaImageFiberEquiv α );
  grind +locals

/-
There exists an equivalence from the cell sigma type to `Fin k` that sends
    each cell `⟨v, b, j⟩` to a slot `i` with `β i = b.val`.
-/
lemma exists_beta_equiv {k : ℕ} (α β : Fin k → ℕ)
    (X : ↥(univ.image α) → ↥(univ.image β) → ℕ)
    (hcol : ∀ b, ∑ v, X v b = (univ.filter (fun i => β i = b.val)).card) :
    ∃ (e : (Σ (v : ↥(univ.image α)) (b : ↥(univ.image β)), Fin (X v b)) ≃ Fin k),
      ∀ t, β (e t) = t.2.1.val := by
  obtain ⟨e₁, he₁⟩ : ∃ (e₁ : (Σ (b : ↥(univ.image β)) (v : ↥(univ.image α)), Fin (X v b)) ≃ Fin k), ∀ t, β (e₁ t) = t.1.val := by
    have := @exists_alpha_equiv k ( fun i => β i ) ( fun i => α i ) ( fun b v => X v b ) ?_;
    · convert this using 6;
    · convert hcol using 1;
  refine' ⟨ Equiv.trans _ e₁, _ ⟩;
  exact ⟨ fun t => ⟨ t.2.1, t.1, t.2.2 ⟩, fun t => ⟨ t.2.1, t.1, t.2.2 ⟩, fun t => rfl, fun t => rfl ⟩;
  aesop

/-
The joint histogram property from composing the two equivalences.
-/
lemma joint_from_equivs {k : ℕ} (α β : Fin k → ℕ)
    (X : ↥(univ.image α) → ↥(univ.image β) → ℕ)
    (eα : (Σ (v : ↥(univ.image α)) (b : ↥(univ.image β)), Fin (X v b)) ≃ Fin k)
    (eβ : (Σ (v : ↥(univ.image α)) (b : ↥(univ.image β)), Fin (X v b)) ≃ Fin k)
    (hα : ∀ t, α (eα t) = t.1.val)
    (hβ : ∀ t, β (eβ t) = t.2.1.val) :
    let σ : Equiv.Perm (Fin k) := eβ.symm.trans eα
    ∀ (v : ↥(univ.image α)) (b : ↥(univ.image β)),
      (univ.filter (fun i => α (σ i) = v.val ∧ β i = b.val)).card = X v b := by
  intro σ v b
  have : Finset.card (Finset.filter (fun i => α (σ i) = v.val ∧ β i = b.val) Finset.univ) = Finset.card (Finset.filter (fun t => t.1 = v ∧ t.2.1 = b) (Finset.univ : Finset ((v : ↥(univ.image α)) × (b : ↥(univ.image β)) × Fin (X v b)))) := by
    convert Finset.card_image_of_injective _ ( show Function.Injective ( fun t : ( v : ↥ ( image α univ ) ) × ( b : ↥ ( image β univ ) ) × Fin ( X v b ) => eβ t ) from eβ.injective ) using 2;
    grind;
  rw [ this, show ( Finset.filter ( fun t : ( v : ↥ ( image α univ ) ) × ( b : ↥ ( image β univ ) ) × Fin ( X v b ) => t.fst = v ∧ t.snd.fst = b ) Finset.univ ) = Finset.image ( fun j : Fin ( X v b ) => ⟨ v, b, j ⟩ ) Finset.univ from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
  ext ⟨v', b', j⟩; simp [Finset.mem_image];
  simp +decide [eq_comm];
  rintro rfl; constructor <;> intro <;> cases ‹_› ; tauto;
  grind

/-- **Joint-type realizability.** Let `α β : Fin k → ℕ`. Given a contingency table
`X : ↥(image α) → ↥(image β) → ℕ` whose row margins equal α's value-fiber sizes and
whose column margins equal β's value-fiber sizes, there is a permutation `σ` of the
`k` slots such that the joint histogram of `(α ∘ σ, β)` is exactly `X`. -/
theorem joint_realizability {k : ℕ} (α β : Fin k → ℕ)
    (X : ↥(univ.image α) → ↥(univ.image β) → ℕ)
    (hrow : ∀ v, ∑ b, X v b = (univ.filter (fun i => α i = v.val)).card)
    (hcol : ∀ b, ∑ v, X v b = (univ.filter (fun i => β i = b.val)).card) :
    ∃ σ : Equiv.Perm (Fin k),
      ∀ (v : ↥(univ.image α)) (b : ↥(univ.image β)),
        (univ.filter (fun i => α (σ i) = v.val ∧ β i = b.val)).card = X v b := by
  obtain ⟨eα, hα⟩ := exists_alpha_equiv α β X hrow
  obtain ⟨eβ, hβ⟩ := exists_beta_equiv α β X hcol
  exact ⟨eβ.symm.trans eα, joint_from_equivs α β X eα eβ hα hβ⟩

end
end BoundedGaps.JointReal
