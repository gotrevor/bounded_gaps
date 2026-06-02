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

/-- **The realizability converse** (Aristotle target `joint_realizability`). A
margin-correct table is realized by a permutation of α against β: there is `σ` whose
joint histogram of `(α ∘ σ, β)` is exactly `T`. Forward direction is in-repo;
this backward direction is the offloaded `sorry`. -/
theorem table_realized_in_orbit (T : CTable α β)
    (hT : T ∈ MarginCorrectTables α β) :
    ∃ p ∈ monoOrbit α, jointMultiset β p
      = tableToMultiset α β T := by
  sorry

/-- **Orbit-free cross-orbit core closed form.** The same value as
`orbitCore_eq_multinomial_sum`, re-indexed over the margin-correct tables. The summand
is fully computable: a product of multinomials in the table entries times the factorial
weight `∏_{v,b} ((v+b)!)^{T v b}`. -/
theorem orbitCore_eq_multinomial_sum_orbitFree :
    ∑ p ∈ monoOrbit α, (∏ i, ((p i + β i).factorial : ℚ))
      = ∑ T ∈ MarginCorrectTables α β,
          (∏ b : ↥(univ.image β), (Nat.multinomial univ
              (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
            * jointWeight (tableToMultiset α β T) := by
  sorry

end OrbitFree

end BoundedGaps
