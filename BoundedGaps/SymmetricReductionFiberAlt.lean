import BoundedGaps.SymmetricReduction

/-!
# (f2), independently: a second proof of the joint-type fiber count

`SymmetricReduction.lean` proves the cross-orbit fiber count
`#{p ∈ monoOrbit α : jointMultiset β p = jointMultiset β p₀} = ∏_b multinomial(n_b; X(·,b))`
as `jointType_fiber_card_eq_multinomial`, with the contingency table written as a *multiset
count* `X v b = (jointMultiset β p₀).count (v,b)`.

This file gives a **second, independent proof** of the same fiber count, written with the
*filter-card* table form `X v b = #{i : p₀ᵢ = v ∧ βᵢ = b}` and its own helper lemmas
(`count_jointMultiset`, `jointMultiset_eq_iff`) — it does not route through the primary
proof's `jointMultiset_count_eq`. `fiber_card_forms_agree` then **links the two** with an
equality of the two multinomial-product formulas, so neither proof is orphaned and the two
table representations are certified equal.

Both proofs follow the same design-doc recipe (value-restriction to `↥(image α)` +
`card_jointType_eq_prod_multinomial` + a `card_bij'` between the orbit-fiber and the
function-fiber), so the independence is at the level of lemma plumbing and table form, not
overall strategy — a transcription/lemma-name cross-check, not a from-scratch-different idea.
-/

namespace BoundedGaps.SymmetricReduction.Alt
open BoundedGaps BoundedGaps.SymmetricReduction BoundedGaps.SievePolynomial
open Finset
open scoped Nat Classical

variable {k : ℕ}

/-- Every element of `monoOrbit α` takes values in `image α` (the permutation rearranges α's
values). -/
theorem orbit_val_mem (α : MultiIndex k) {p : MultiIndex k} (hp : p ∈ monoOrbit α) (i : Fin k) :
    p i ∈ Finset.image α univ := by
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, rfl⟩

/-- Multiplicity of `(c,b)` in `jointMultiset β p` is the joint fiber size `#{i : pᵢ=c ∧ βᵢ=b}`. -/
theorem count_jointMultiset (β p : MultiIndex k) (c b : ℕ) :
    Multiset.count (c, b) (jointMultiset β p)
      = (univ.filter (fun i => p i = c ∧ β i = b)).card := by
  unfold jointMultiset
  rw [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def]
  congr 1; ext i; simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq]; tauto

/-- Joint multisets agree iff the joint histograms agree at every value-pair. -/
theorem jointMultiset_eq_iff (β p q : MultiIndex k) :
    jointMultiset β p = jointMultiset β q ↔
      ∀ c b, (univ.filter (fun i => p i = c ∧ β i = b)).card
           = (univ.filter (fun i => q i = c ∧ β i = b)).card := by
  rw [Multiset.ext]
  constructor
  · intro h c b; rw [← count_jointMultiset, ← count_jointMultiset, h]
  · intro h cb; rw [count_jointMultiset, count_jointMultiset]; exact h cb.1 cb.2

/-- **(f2), filter-card table form.** Second proof of the joint-type fiber count, with the
contingency table written as the joint fiber size `#{i : p₀ᵢ = v ∧ βᵢ = b}`. -/
theorem fiber_card_eq_multinomial (α β p₀ : MultiIndex k) (hp₀ : p₀ ∈ monoOrbit α) :
    ((monoOrbit α).filter (fun p => jointMultiset β p = jointMultiset β p₀)).card
      = ∏ b : ↥(Finset.image β univ),
          Nat.multinomial univ (fun v : ↥(Finset.image α univ) =>
            (univ.filter (fun i => p₀ i = v.val ∧ β i = b.val)).card) := by
  set V := ↥(Finset.image α univ)
  set B := ↥(Finset.image β univ)
  set g : Fin k → B := fun i => ⟨β i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ with hg
  set X' : V → B → ℕ := fun v b => (univ.filter (fun i => p₀ i = v.val ∧ β i = b.val)).card with hX'
  have hcol : ∀ b, ∑ v, X' v b = Fintype.card {i // g i = b} := by
    intro b
    rw [Fintype.card_subtype]
    rw [Finset.sum_coe_sort (Finset.image α univ)
          (fun v => (univ.filter (fun i => p₀ i = v ∧ β i = b.val)).card)]
    rw [Finset.card_eq_sum_card_fiberwise
          (f := p₀) (t := Finset.image α univ) (fun i _ => orbit_val_mem α hp₀ i)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    congr 1; ext i
    simp only [mem_filter, mem_univ, true_and, hg]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, Subtype.ext_iff.mp h1⟩
  rw [← card_jointType_eq_prod_multinomial g X' hcol]
  refine Finset.card_bij'
    (fun (p : MultiIndex k) hp idx =>
      (⟨p idx, orbit_val_mem α (Finset.mem_filter.mp hp).1 idx⟩ : V))
    (fun (f : Fin k → V) _ idx => (f idx).val)
    ?hi ?hj ?linv ?rinv
  case linv => intro p hp; funext idx; rfl
  case rinv => intro f hf; funext idx; exact Subtype.ext rfl
  case hi =>
    intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hp_eq := (Finset.mem_filter.mp hp).2
    intro v b
    have hconv : (univ.filter (fun i =>
          (⟨p i, orbit_val_mem α (Finset.mem_filter.mp hp).1 i⟩ : V) = v ∧ g i = b))
        = univ.filter (fun i => p i = v.val ∧ β i = b.val) := by
      apply Finset.filter_congr; intro i _
      simp only [hg]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext_iff.mp h1, Subtype.ext_iff.mp h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    rw [hconv]
    exact (jointMultiset_eq_iff β p p₀).mp hp_eq v.val b.val
  case hj =>
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    set p : MultiIndex k := fun idx => (f idx).val with hp_def
    have hjoint : jointMultiset β p = jointMultiset β p₀ := by
      rw [jointMultiset_eq_iff]
      intro c b
      by_cases hc : c ∈ Finset.image α univ
      · by_cases hb : b ∈ Finset.image β univ
        · have hh := hf ⟨c, hc⟩ ⟨b, hb⟩
          have hconv : (univ.filter (fun i => f i = (⟨c, hc⟩ : V) ∧ g i = (⟨b, hb⟩ : B)))
              = univ.filter (fun i => p i = c ∧ β i = b) := by
            apply Finset.filter_congr; intro i _
            simp only [hg]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext_iff.mp h1, Subtype.ext_iff.mp h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
          rw [hconv] at hh
          rw [hh]
        · have e1 : (univ.filter (fun i => p i = c ∧ β i = b)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro i _; rintro ⟨-, hbi⟩
            exact hb (hbi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
          have e2 : (univ.filter (fun i => p₀ i = c ∧ β i = b)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]; intro i _; rintro ⟨-, hbi⟩
            exact hb (hbi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
          rw [e1, e2]
      · have e1 : (univ.filter (fun i => p i = c ∧ β i = b)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _; rintro ⟨hci, -⟩
          have hpi : p i ∈ Finset.image α univ := (f i).property
          exact hc (hci ▸ hpi)
        have e2 : (univ.filter (fun i => p₀ i = c ∧ β i = b)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _; rintro ⟨hci, -⟩
          exact hc (hci ▸ orbit_val_mem α hp₀ i)
        rw [e1, e2]
    refine Finset.mem_filter.mpr ⟨?_, hjoint⟩
    rw [mem_monoOrbit_iff]
    intro v
    have h1 : (univ.filter (fun i => p i = v)).card = (univ.filter (fun i => p₀ i = v)).card := by
      rw [card_filter_eq_sum_joint p β v, card_filter_eq_sum_joint p₀ β v]
      exact Finset.sum_congr rfl (fun b _ => (jointMultiset_eq_iff β p p₀).mp hjoint v b)
    rw [h1]; exact (mem_monoOrbit_iff α p₀).mp hp₀ v

/-- **The ⟺ link.** The primary proof's *multiset-count* table and this file's *filter-card*
table give the **same** product of multinomials — proven by chaining the two independent fiber
counts (`SymmetricReduction.jointType_fiber_card_eq_multinomial` and `fiber_card_eq_multinomial`
above) through their shared value, so each proof is load-bearing and neither is orphaned. -/
theorem fiber_card_forms_agree (α β p₀ : MultiIndex k) (hp₀ : p₀ ∈ monoOrbit α) :
    (∏ b : ↥(Finset.image β univ), Nat.multinomial univ
        (fun v : ↥(Finset.image α univ) => (jointMultiset β p₀).count (v.val, b.val)))
      = ∏ b : ↥(Finset.image β univ), Nat.multinomial univ
        (fun v : ↥(Finset.image α univ) =>
          (univ.filter (fun i => p₀ i = v.val ∧ β i = b.val)).card) :=
  (jointType_fiber_card_eq_multinomial α β p₀ hp₀).symm.trans
    (fiber_card_eq_multinomial α β p₀ hp₀)

end BoundedGaps.SymmetricReduction.Alt
