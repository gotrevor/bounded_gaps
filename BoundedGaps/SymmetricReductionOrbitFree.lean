import BoundedGaps.SymmetricReduction

/-!
# Orbit-free re-indexing of the cross-orbit core closed form

`SymmetricReduction.orbitCore_eq_multinomial_sum` evaluates the single-orbit core
`S(α,β) = ∑_{p∈monoOrbit α} ∏ᵢ (pᵢ+βᵢ)!` as a sum over the *realized* joint types
`X ∈ (monoOrbit α).image (jointMultiset β)`. That index set still references the
orbit, so it is **not** `native_decide`-able at `k = 54` (the orbit is the image of
`54!` permutations).

This file re-indexes the same sum over an **orbit-free** index: the explicit Finset
of margin-correct contingency tables `T : ↥(image α) → ↥(image β) → Fin (k+1)` whose
row margins are α's value-fiber sizes and whose column margins are β's. That set is
computable from the *shapes* of α and β alone (their value histograms), so the whole
Rayleigh entry becomes a finite rational computation a kernel can evaluate.

The set equality `(monoOrbit α).image (jointMultiset β) = image tableToMultiset
(MarginCorrectTables α β)` has two halves:
* **forward** (realized ⟹ correct margins): in-repo, `sum_joint_eq_fiber` / `_col`.
* **backward** (correct margins ⟹ realized): the `joint_realizability` converse,
  currently offloaded to Aristotle (job `38089125-…`). Until its proof lands it is
  the single `sorry` here.
-/

namespace BoundedGaps

open Finset
open scoped Nat
open SymmetricReduction SievePolynomial

namespace OrbitFree

variable {k : ℕ} (α β : MultiIndex k)

/-- A contingency table against the value sets of `α` (rows) and `β` (columns). Entries
are bounded by `k` (encoded as `Fin (k+1)`) so the function type is a `Fintype` and the
margin-correct tables form an explicit, enumerable `Finset`. -/
abbrev CTable : Type := ↥(univ.image α) → ↥(univ.image β) → Fin (k + 1)

/-- The explicit, orbit-free index set: contingency tables whose **row** margins equal
α's value-fiber sizes and whose **column** margins equal β's. Computable from α, β. -/
def MarginCorrectTables : Finset (CTable α β) :=
  univ.filter (fun T =>
    (∀ v, ∑ b, (T v b : ℕ) = (univ.filter (fun i => α i = v.val)).card) ∧
    (∀ b, ∑ v, (T v b : ℕ) = (univ.filter (fun i => β i = b.val)).card))

/-- The joint multiset (contingency-table content) named by a table `T`: pair `(v,b)`
appears with multiplicity `T v b`. This is the bridge to the multiset-indexed sum of
`orbitCore_eq_multinomial_sum`. -/
def tableToMultiset (T : CTable α β) : Multiset (ℕ × ℕ) :=
  ∑ v : ↥(univ.image α), ∑ b : ↥(univ.image β),
    Multiset.replicate (T v b) (v.val, b.val)

/-- **Keystone count lemma.** The multiset named by `T` has multiplicity `T v b` at
each in-range cell `(v.val, b.val)`. This is what matches the table-indexed multinomial
summand to the multiset-indexed one of `orbitCore_eq_multinomial_sum`. -/
lemma tableToMultiset_count_mem (T : CTable α β)
    (v₀ : ↥(univ.image α)) (b₀ : ↥(univ.image β)) :
    (tableToMultiset α β T).count (v₀.val, b₀.val) = T v₀ b₀ := by
  classical
  unfold tableToMultiset
  rw [Multiset.count_sum']
  rw [Finset.sum_eq_single v₀]
  · rw [Multiset.count_sum']
    rw [Finset.sum_eq_single b₀]
    · rw [Multiset.count_replicate, if_pos rfl]
    · intro b _ hb
      rw [Multiset.count_replicate, if_neg]
      intro h
      exact hb (Subtype.ext (congrArg Prod.snd h))
    · intro h; exact absurd (Finset.mem_univ b₀) h
  · intro v _ hv
    rw [Multiset.count_sum']
    apply Finset.sum_eq_zero
    intro b _
    rw [Multiset.count_replicate, if_neg]
    intro h
    exact hv (Subtype.ext (congrArg Prod.fst h))
  · intro h; exact absurd (Finset.mem_univ v₀) h

/-- The joint multiset against `β` has exactly `k` pairs (one per slot). -/
lemma jointMultiset_card (p : MultiIndex k) : (jointMultiset β p).card = k := by
  unfold jointMultiset
  rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ, Fintype.card_fin]

/-- The **inverse map**: the contingency table read off a coordinate vector `p` (its
joint histogram against `β`). Entries are `≤ k` so they land in `Fin (k+1)`. -/
def orbitTable (p : MultiIndex k) : CTable α β :=
  fun v b => ⟨(jointMultiset β p).count (v.val, b.val),
    Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans (jointMultiset_card β p).le)⟩

/-- **Forward (j) direction.** The table read off any orbit element is margin-correct:
its row margins are α's value-fiber sizes (orbit ⟹ same histogram as α) and its column
margins are β's. Pure; uses only `sum_joint_eq_fiber` / `_col` and `mem_monoOrbit_iff`. -/
lemma orbitTable_mem (p : MultiIndex k) (hp : p ∈ monoOrbit α) :
    orbitTable α β p ∈ MarginCorrectTables α β := by
  classical
  rw [MarginCorrectTables, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro v
    have hval : ∀ b : ↥(univ.image β), ((orbitTable α β p v b : ℕ))
        = (univ.filter (fun i => p i = v.val ∧ β i = b.val)).card :=
      fun b => jointMultiset_count_eq β p v.val b.val
    rw [Finset.sum_congr rfl (fun b _ => hval b), sum_joint_eq_fiber β p v.val]
    exact (mem_monoOrbit_iff α p).mp hp v.val
  · intro b
    have hval : ∀ v : ↥(univ.image α), ((orbitTable α β p v b : ℕ))
        = (univ.filter (fun i => p i = v.val ∧ β i = b.val)).card :=
      fun v => jointMultiset_count_eq β p v.val b.val
    rw [Finset.sum_congr rfl (fun v _ => hval v),
        sum_joint_eq_fiber_col α β p (fun i => orbit_vals_mem α hp i) b.val]

/-- **The realizability converse** (Aristotle target `joint_realizability`). A
margin-correct table is realized by a permutation of α against β: there is `σ` whose
joint histogram of `(α ∘ σ, β)` is exactly `T`. Forward direction is in-repo;
this backward direction is the offloaded `sorry`. -/
theorem table_realized_in_orbit (T : CTable α β)
    (hT : T ∈ MarginCorrectTables α β) :
    ∃ p ∈ monoOrbit α, jointMultiset β p
      = tableToMultiset α β T := by
  sorry

/-- The **total clamped inverse**: read a table off any multiset (entries clamped to
`≤ k` so they land in `Fin (k+1)`). On realized multisets the clamp is inactive. -/
def multisetToTable (X : Multiset (ℕ × ℕ)) : CTable α β :=
  fun v b => ⟨min (X.count (v.val, b.val)) k,
    lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self k)⟩

/-- On a realized multiset the clamp does nothing, so `multisetToTable` recovers
`orbitTable` (counts are `≤ k`). -/
lemma multisetToTable_jointMultiset (p : MultiIndex k) :
    multisetToTable α β (jointMultiset β p) = orbitTable α β p := by
  funext v b
  refine Fin.ext ?_
  simp only [multisetToTable, orbitTable]
  exact min_eq_left ((Multiset.count_le_card _ _).trans (jointMultiset_card β p).le)

/-- **Table roundtrip** (unconditional): reading a table off the multiset it names
recovers the table. Entries `≤ k` (they are `Fin (k+1)`), so the clamp is inactive. -/
lemma multisetToTable_tableToMultiset (T : CTable α β) :
    multisetToTable α β (tableToMultiset α β T) = T := by
  funext v b
  refine Fin.ext ?_
  simp only [multisetToTable]
  rw [tableToMultiset_count_mem]
  exact min_eq_left (Nat.lt_succ_iff.mp (T v b).isLt)

/-- The multiset named by a table has no mass off the value sets of α (rows) and β
(columns). -/
lemma tableToMultiset_count_not_mem (T : CTable α β) (c d : ℕ)
    (h : c ∉ univ.image α ∨ d ∉ univ.image β) :
    (tableToMultiset α β T).count (c, d) = 0 := by
  unfold tableToMultiset
  rw [Multiset.count_sum']
  apply Finset.sum_eq_zero; intro v _
  rw [Multiset.count_sum']
  apply Finset.sum_eq_zero; intro b _
  rw [Multiset.count_replicate, if_neg]
  intro heq
  rw [Prod.mk.injEq] at heq
  rcases h with h | h
  · exact h (heq.1 ▸ v.2)
  · exact h (heq.2 ▸ b.2)

/-- The joint multiset of an `image α`-valued vector has no mass off α's and β's value
sets. -/
lemma jointMultiset_count_zero (p : MultiIndex k) (hp : ∀ i, p i ∈ univ.image α)
    (c d : ℕ) (h : c ∉ univ.image α ∨ d ∉ univ.image β) :
    (jointMultiset β p).count (c, d) = 0 := by
  rw [jointMultiset_count_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i _ ⟨h1, h2⟩
  rcases h with h | h
  · exact h (h1 ▸ hp i)
  · exact h (h2 ▸ Finset.mem_image_of_mem β (Finset.mem_univ i))

/-- **Realized roundtrip**: for an `image α`-valued vector, the multiset named by its
table is the original joint multiset. The non-trivial direction of the bijection's
inverse on the orbit-image side. -/
lemma tableToMultiset_orbitTable (p : MultiIndex k) (hp : ∀ i, p i ∈ univ.image α) :
    tableToMultiset α β (orbitTable α β p) = jointMultiset β p := by
  ext ⟨c, d⟩
  by_cases hc : c ∈ univ.image α
  · by_cases hd : d ∈ univ.image β
    · have hrw : ((c, d) : ℕ × ℕ)
          = ((⟨c, hc⟩ : ↥(univ.image α)).val, (⟨d, hd⟩ : ↥(univ.image β)).val) := rfl
      rw [hrw, tableToMultiset_count_mem]
      simp only [orbitTable]
    · rw [tableToMultiset_count_not_mem α β _ c d (Or.inr hd),
          jointMultiset_count_zero α β p hp c d (Or.inr hd)]
  · rw [tableToMultiset_count_not_mem α β _ c d (Or.inl hc),
        jointMultiset_count_zero α β p hp c d (Or.inl hc)]

/-- **Orbit-free cross-orbit core closed form.** The same value as
`orbitCore_eq_multinomial_sum`, re-indexed over the margin-correct tables. The summand
is fully computable: a product of multinomials in the table entries times the factorial
weight `∏_{v,b} ((v+b)!)^{T v b}`. Modulo `table_realized_in_orbit` (Aristotle). -/
theorem orbitCore_eq_multinomial_sum_orbitFree :
    ∑ p ∈ monoOrbit α, (∏ i, ((p i + β i).factorial : ℚ))
      = ∑ T ∈ MarginCorrectTables α β,
          (∏ b : ↥(univ.image β), (Nat.multinomial univ
              (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
            * jointWeight (tableToMultiset α β T) := by
  classical
  rw [orbitCore_eq_multinomial_sum]
  refine Finset.sum_bij'
    (i := fun X _ => multisetToTable α β X)
    (j := fun T _ => tableToMultiset α β T) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    dsimp only
    rw [multisetToTable_jointMultiset]
    exact orbitTable_mem α β p hp
  · intro T hT
    obtain ⟨p, hp, heq⟩ := table_realized_in_orbit α β T hT
    exact Finset.mem_image.mpr ⟨p, hp, heq⟩
  · intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    dsimp only
    rw [multisetToTable_jointMultiset]
    exact tableToMultiset_orbitTable α β p (fun i => orbit_vals_mem α hp i)
  · intro T _
    exact multisetToTable_tableToMultiset α β T
  · intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    dsimp only
    rw [multisetToTable_jointMultiset,
        tableToMultiset_orbitTable α β p (fun i => orbit_vals_mem α hp i)]
    simp only [orbitTable]

end OrbitFree

end BoundedGaps
