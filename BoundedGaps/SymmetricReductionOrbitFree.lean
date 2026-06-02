import BoundedGaps.SymmetricReduction
import BoundedGaps.JointRealizability

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

/-- **The realizability converse** (`joint_realizability`, formalized by Aristotle and
ported in `JointRealizability.lean`). A margin-correct table is realized by a
permutation of α against β: there is `σ` with `α ∘ σ ∈ monoOrbit α` whose joint
histogram against β is exactly `T`. The bridge applies `joint_realizability` to `T`'s
entries and reads off the histogram via `jointMultiset_count_eq` / the off-support
vanishing lemmas. -/
theorem table_realized_in_orbit (T : CTable α β)
    (hT : T ∈ MarginCorrectTables α β) :
    ∃ p ∈ monoOrbit α, jointMultiset β p
      = tableToMultiset α β T := by
  classical
  rw [MarginCorrectTables, Finset.mem_filter] at hT
  obtain ⟨-, hrow, hcol⟩ := hT
  obtain ⟨σ, hσ⟩ :=
    JointReal.joint_realizability α β (fun v b => (T v b : ℕ)) hrow hcol
  refine ⟨fun i => α (σ i), ?_, ?_⟩
  · rw [mem_monoOrbit_iff]
    intro v
    simp only [Finset.card_filter]
    exact Equiv.sum_comp σ (fun i => if α i = v then 1 else 0)
  · have hpval : ∀ i, α (σ i) ∈ univ.image α :=
      fun i => Finset.mem_image_of_mem α (Finset.mem_univ (σ i))
    ext ⟨c, d⟩
    by_cases hc : c ∈ univ.image α
    · by_cases hd : d ∈ univ.image β
      · have hrw : ((c, d) : ℕ × ℕ)
            = ((⟨c, hc⟩ : ↥(univ.image α)).val, (⟨d, hd⟩ : ↥(univ.image β)).val) := rfl
        rw [hrw, jointMultiset_count_eq, tableToMultiset_count_mem]
        exact hσ ⟨c, hc⟩ ⟨d, hd⟩
      · rw [jointMultiset_count_zero α β _ hpval c d (Or.inr hd),
            tableToMultiset_count_not_mem α β _ c d (Or.inr hd)]
    · rw [jointMultiset_count_zero α β _ hpval c d (Or.inl hc),
          tableToMultiset_count_not_mem α β _ c d (Or.inl hc)]

/-- **Orbit-free cross-orbit core closed form.** The same value as
`orbitCore_eq_multinomial_sum`, re-indexed over the margin-correct tables. The summand
is fully computable: a product of multinomials in the table entries times the factorial
weight `∏_{v,b} ((v+b)!)^{T v b}`. Now axiom-clean (realizability discharged). -/
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

/-- **Orbit cardinality is a multinomial.** The number of distinct rearrangements of β
equals the multinomial coefficient of β's value-fiber sizes — computable from β's shape
alone, no orbit enumeration. Discharges the last orbit reference in the denominator entry.
Proven via the keystone `card_fiberwise_eq_multinomial` and a `card_bij'` from `monoOrbit β`
to the `image β`-valued functions with β's fiber sizes. -/
lemma monoOrbit_card_eq_multinomial :
    (monoOrbit β).card
      = Nat.multinomial (univ : Finset ↥(univ.image β))
          (fun b => (univ.filter (fun i => β i = b.val)).card) := by
  classical
  set h : ↥(univ.image β) → ℕ :=
    fun b => (univ.filter (fun i => β i = b.val)).card with hh
  have hsum : ∑ b, h b = Fintype.card (Fin k) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset (Fin k))) (t := (univ : Finset ↥(univ.image β)))
      (f := fun i => (⟨β i, Finset.mem_image_of_mem β (Finset.mem_univ i)⟩
        : ↥(univ.image β)))
      (fun i _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hfib
    rw [hfib]
    apply Finset.sum_congr rfl
    intro b _
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    simp [Subtype.ext_iff, eq_comm]
  rw [← card_fiberwise_eq_multinomial h hsum]
  apply Finset.card_bij'
    (i := fun (p : MultiIndex k) (hp : p ∈ monoOrbit β) =>
            (fun idx => (⟨p idx, orbit_vals_mem β hp idx⟩ : ↥(univ.image β))))
    (j := fun (f : Fin k → ↥(univ.image β)) (_ : f ∈ univ.filter _) =>
            (fun idx => (f idx).val : MultiIndex k))
  case hi =>
    intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro b
    have key : (univ.filter (fun a => p a = b.val)).card = h b :=
      (mem_monoOrbit_iff β p).mp hp b.val
    rw [← key]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    simp [Subtype.ext_iff]
  case hj =>
    intro f hf
    have hPV : ∀ v, (univ.filter (fun a => f a = v)).card = h v :=
      (Finset.mem_filter.mp hf).2
    rw [mem_monoOrbit_iff]
    intro c
    by_cases hc : c ∈ univ.image β
    · have e1 : (univ.filter (fun i => (f i).val = c)).card
              = (univ.filter (fun i => f i = (⟨c, hc⟩ : ↥(univ.image β)))).card := by
        apply congrArg Finset.card; apply Finset.filter_congr; intro i _
        simp [Subtype.ext_iff]
      rw [e1, hPV ⟨c, hc⟩]
    · have e0 : (univ.filter (fun i => (f i).val = c)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _ heq; exact hc (heq ▸ (f i).2)
      have eβ : (univ.filter (fun i => β i = c)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _ heq
        exact hc (heq ▸ Finset.mem_image_of_mem β (Finset.mem_univ i))
      rw [e0, eβ]
  case left_inv => intro p _; funext idx; rfl
  case right_inv => intro f _; funext idx; exact Subtype.ext rfl

/-- **Orbit-free cross-orbit denominator matrix entry.** The full off-diagonal orbit-pair
denominator `∑_{p∈orbit α} ∑_{q∈orbit β} monomialIntegral (p+q)` equals `|monoOrbit β|`
copies of the orbit-free contingency-table sum, divided by the constant factorial
`(k+|α|+|β|)!`. Chains `orbitPair_denominator_eq` (factor the constant denominator),
`orbitPair_core_const` (collapse the `q`-sum), and the orbit-free re-index. The only
residual orbit reference is the scalar `(monoOrbit β).card`. -/
theorem orbitPair_denominator_orbitFree :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, monomialIntegral (p + q)
      = ((monoOrbit β).card • ∑ T ∈ MarginCorrectTables α β,
            (∏ b : ↥(univ.image β), (Nat.multinomial univ
                (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
              * jointWeight (tableToMultiset α β T))
          / ((k + α.degree + β.degree).factorial : ℚ) := by
  rw [orbitPair_denominator_eq, orbitPair_core_const,
      orbitCore_eq_multinomial_sum_orbitFree]

/-- **Fully orbit-free cross-orbit denominator matrix entry.** Eliminating the last
orbit reference `(monoOrbit β).card` via `monoOrbit_card_eq_multinomial`, the entire
off-diagonal denominator is expressed in objects computable from the *shapes* of α and β
alone: a multinomial of β's fiber sizes, the margin-correct contingency-table sum, and the
constant factorial. No `monoOrbit` appears on the right. -/
theorem orbitPair_denominator_shapeForm :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, monomialIntegral (p + q)
      = ((Nat.multinomial (univ : Finset ↥(univ.image β))
            (fun b => (univ.filter (fun i => β i = b.val)).card)) •
          ∑ T ∈ MarginCorrectTables α β,
            (∏ b : ↥(univ.image β), (Nat.multinomial univ
                (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
              * jointWeight (tableToMultiset α β T))
          / ((k + α.degree + β.degree).factorial : ℚ) := by
  rw [orbitPair_denominator_orbitFree, monoOrbit_card_eq_multinomial]

/-- Computable twin of `jointWeight` (identical body; the library's `noncomputable`
marker is gratuitous — `ℚ` arithmetic and `Multiset.prod` reduce in the kernel). Lets the
shape-form expression evaluate for `native_decide`. -/
def jointWeightC (X : Multiset (ℕ × ℕ)) : ℚ :=
  (X.map (fun cb => ((cb.1 + cb.2).factorial : ℚ))).prod

@[simp] lemma jointWeightC_eq (X : Multiset (ℕ × ℕ)) : jointWeightC X = jointWeight X := rfl

/-- **`native_decide`-ready denominator matrix entry.** `orbitPair_denominator_shapeForm`
restated with the computable `jointWeightC`. Every operation on the right reduces in the
kernel: the Fintype-enumerated `MarginCorrectTables`, `Nat.multinomial`, `tableToMultiset`,
and `jointWeightC`. (Defeq to the shape-form, since `jointWeightC = jointWeight`.) -/
theorem orbitPair_denominator_computable :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, monomialIntegral (p + q)
      = ((Nat.multinomial (univ : Finset ↥(univ.image β))
            (fun b => (univ.filter (fun i => β i = b.val)).card)) •
          ∑ T ∈ MarginCorrectTables α β,
            (∏ b : ↥(univ.image β), (Nat.multinomial univ
                (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
              * jointWeightC (tableToMultiset α β T))
          / ((k + α.degree + β.degree).factorial : ℚ) :=
  orbitPair_denominator_shapeForm α β

/-- **Cross-orbit numerator: factor out the constant Dirichlet denominator.** The
numerator analog of `orbitPair_denominator_eq`. Each summand's
`dirichletIntegralWithSlack (removeNth i (p+q)) (pᵢ+qᵢ+2)` has denominator
`(n + ∑ⱼ(removeNthᵢ(p+q))ⱼ + (pᵢ+qᵢ+2))!`, which collapses to the **constant**
`(n+1+|α|+|β|+1)!` for every `i` and every orbit pair (the `removeNth`-sum plus the
slack exponent restores the full degree). So the whole cross-orbit numerator sum is the
purely combinatorial numerator over that single factorial. -/
lemma orbitPair_numerator_eq {n : ℕ} (α β : MultiIndex (n + 1)) :
    ∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
        (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack (Fin.removeNth i (p + q)) (p i + q i + 2)
      = (∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
          (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
            ((∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ))
              * ((p i + q i + 2).factorial : ℚ)))
        / (((n + 1) + α.degree + β.degree + 1).factorial : ℚ) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hsucc : (∑ m, (p + q) m) = (p + q) i + ∑ j, (Fin.removeNth i (p + q)) j :=
    Fin.sum_univ_succAbove (p + q) i
  have hdeg : (∑ m, (p m + q m)) = α.degree + β.degree := by
    rw [Finset.sum_add_distrib, monoOrbit_mem_degree α hp, monoOrbit_mem_degree β hq]
  simp only [Pi.add_apply] at hsucc
  have harg : n + (∑ j, (Fin.removeNth i (p + q)) j) + (p i + q i + 2)
      = (n + 1) + α.degree + β.degree + 1 := by omega
  unfold dirichletIntegralWithSlack
  rw [harg]
  ring

/-- **Numerator summand factorization** (the insight that makes the numerator
denominator-grade, not a harder pointed build). The `removeNth`-product times the slack
factorial factors as the *full* joint-type product `∏ₘ((p+q)ₘ)!` times a **local
marked-cell factor** `(pᵢ+qᵢ+2)!/(pᵢ+qᵢ)!` depending only on the value pair at `i`. Via
`Fin.prod_univ_succAbove`: `∏ₘ((p+q)ₘ)! = ((p+q)ᵢ)! · ∏ⱼ(removeNthᵢ(p+q))ⱼ!`. Consequence:
`∑ᵢ (local factor) = ∑cells Y·(factor)` for the (p,q) joint type `Y`, so the whole
numerator regroups over the (p,q) joint type like the denominator. -/
lemma numerator_summand_factor {n : ℕ} (p q : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
    (∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ)) * ((p i + q i + 2).factorial : ℚ)
      = (∏ m, (((p + q) m).factorial : ℚ))
          * ((p i + q i + 2).factorial : ℚ) / ((p i + q i).factorial : ℚ) := by
  have hprod : (∏ m, (((p + q) m).factorial : ℚ))
      = (((p + q) i).factorial : ℚ) * ∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ) :=
    Fin.prod_univ_succAbove (fun m => (((p + q) m).factorial : ℚ)) i
  have hne : ((p i + q i).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hprod]
  simp only [Pi.add_apply]
  field_simp

/-- **The local marked-cell factor.** For a marked coordinate with value pair `(a,b) = (pᵢ,qᵢ)`,
the part of the numerator summand that depends *only* on that cell:
`1/((a+1)(b+1)) · (a+b+2)!/(a+b)!`. (The `(a+b+2)!/(a+b)!` is the slack-factorial ratio
`numerator_summand_factor` isolates; `1/((a+1)(b+1))` is the `1/((pᵢ+1)(qᵢ+1))` weight.)
Computable, so the eventual `native_decide` form can `#eval` it. -/
def markedCellFactor (a b : ℕ) : ℚ :=
  (1 : ℚ) / (((a + 1 : ℕ) : ℚ) * ((b + 1 : ℕ) : ℚ))
    * ((a + b + 2).factorial : ℚ) / ((a + b).factorial : ℚ)

/-- **Numerator combinatorial sum, factored over the joint type.** The combinatorial numerator
sum isolated by `orbitPair_numerator_eq` (the triple sum `∑ᵢ∑ₚ∑_q`) regroups, for each orbit
pair `(p,q)`, as the **whole joint-type product** `∏ₘ((p+q)ₘ)!` times the **marked-cell sum**
`∑ᵢ markedCellFactor(pᵢ,qᵢ)`. The marked coordinate `i` is moved innermost (`Finset.sum_comm`),
the joint-type product (independent of `i`) is pulled out (`Finset.mul_sum`), and the per-`i`
summand is collapsed by `numerator_summand_factor`. Both factors depend on `(p,q)` only through
the pair multiset `{(pₘ,qₘ)}ₘ` — the bridge to the orbit-free (p,q)-joint-type re-index. -/
lemma numerator_combinatorial_factored {n : ℕ} (α β : MultiIndex (n + 1)) :
    (∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
        (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          ((∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ))
            * ((p i + q i + 2).factorial : ℚ)))
      = ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
          (∏ m, (((p + q) m).factorial : ℚ)) * (∑ i, markedCellFactor (p i) (q i)) := by
  -- Step 1: collapse each per-`i` summand to `(joint product) * markedCellFactor(pᵢ,qᵢ)`.
  have h1 : ∀ (i : Fin (n + 1)) (p q : MultiIndex (n + 1)),
      (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
        ((∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ))
          * ((p i + q i + 2).factorial : ℚ))
        = (∏ m, (((p + q) m).factorial : ℚ)) * markedCellFactor (p i) (q i) := by
    intro i p q
    rw [numerator_summand_factor p q i]
    unfold markedCellFactor
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun q _ => h1 i p q)))]
  -- Step 2: move `i` innermost (swap with `p`, then with `q`) and factor the joint product out.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.mul_sum]

end OrbitFree

end BoundedGaps
