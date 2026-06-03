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

/-- The **marked-cell sum** attached to a joint multiset `X`: `∑_{(c,b)∈X} markedCellFactor c b`.
With `X = jointMultiset q p = {(pᵢ,qᵢ)}ᵢ` this is exactly `∑ᵢ markedCellFactor(pᵢ,qᵢ)`
(`markedSum_jointMultiset`). The numerator analog of `jointWeight`. -/
def markedSum (X : Multiset (ℕ × ℕ)) : ℚ :=
  (X.map (fun cb => markedCellFactor cb.1 cb.2)).sum

/-- The **numerator pair weight** of a joint multiset `X`: `jointWeight X · markedSum X`. With
`X = jointMultiset q p` this is the full per-orbit-pair numerator summand
(`numerator_summand_eq_pairWeight`). The numerator analog of `jointWeight` for the denominator. -/
noncomputable def pairWeight (X : Multiset (ℕ × ℕ)) : ℚ := jointWeight X * markedSum X

/-- The marked-cell sum over coordinates depends on `(p,q)` only through the pair multiset
`jointMultiset q p = {(pᵢ,qᵢ)}ᵢ`. (A sum over `Fin k` is the multiset sum over the mapped
marked factors.) Mirror of `prodFactorial_eq_jointWeight`. -/
lemma markedSum_jointMultiset {k : ℕ} (p q : MultiIndex k) :
    (∑ i, markedCellFactor (p i) (q i)) = markedSum (jointMultiset q p) := by
  unfold markedSum jointMultiset
  rw [Multiset.map_map]
  rfl

/-- The factored numerator summand `(∏ₘ(p+q)ₘ!) · ∑ᵢ markedCellFactor(pᵢ,qᵢ)` equals
`pairWeight (jointMultiset q p)` — i.e. it depends on `(p,q)` only through the pair multiset.
This is the bridge that lets the double orbit sum regroup over the (p,q) joint type. -/
lemma numerator_summand_eq_pairWeight {k : ℕ} (p q : MultiIndex k) :
    (∏ m, (((p + q) m).factorial : ℚ)) * (∑ i, markedCellFactor (p i) (q i))
      = pairWeight (jointMultiset q p) := by
  unfold pairWeight
  rw [markedSum_jointMultiset, ← prodFactorial_eq_jointWeight q p]
  simp only [Pi.add_apply]

/-- **Numerator combinatorial sum as a pair-weighted double orbit sum.** Combining
`numerator_combinatorial_factored` with the multiset bridge: the combinatorial numerator
(the triple sum from `orbitPair_numerator_eq`) is `∑_{p∈orbit α}∑_{q∈orbit β} pairWeight(jointMultiset q p)`.
The summand is now a pure function of the (p,q) joint type, ready for the orbit-free re-index. -/
lemma numerator_combinatorial_pairWeight {n : ℕ} (α β : MultiIndex (n + 1)) :
    (∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
        (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          ((∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ))
            * ((p i + q i + 2).factorial : ℚ)))
      = ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, pairWeight (jointMultiset q p) := by
  rw [numerator_combinatorial_factored]
  exact Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => numerator_summand_eq_pairWeight p q))

/-- **Pair-orbit regrouping (abstract count).** Any function `F` of the pair multiset
`jointMultiset q p = {(pᵢ,qᵢ)}ᵢ`, summed over the full orbit pair `monoOrbit α × monoOrbit β`,
regroups over the *distinct* pair multisets `X`, each weighted by the pair-fiber count
`#{(p,q) : jointMultiset q p = X}`. The numerator analog of `orbitCore_eq_jointType_sum`, but
over the product of two orbits. Proof: combine the double sum over the product
(`Finset.sum_product`), then `Finset.sum_fiberwise_of_maps_to` (the summand is constant on each
fiber by definition of `X`). -/
lemma pairOrbit_regroup {k : ℕ} (α β : MultiIndex k) (F : Multiset (ℕ × ℕ) → ℚ) :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, F (jointMultiset q p)
      = ∑ X ∈ (monoOrbit α ×ˢ monoOrbit β).image (fun pq => jointMultiset pq.2 pq.1),
          (((monoOrbit α ×ˢ monoOrbit β).filter
              (fun pq => jointMultiset pq.2 pq.1 = X)).card : ℚ) * F X := by
  rw [← Finset.sum_product']
  have hmaps : ∀ pq ∈ monoOrbit α ×ˢ monoOrbit β,
      jointMultiset pq.2 pq.1
        ∈ (monoOrbit α ×ˢ monoOrbit β).image (fun pq => jointMultiset pq.2 pq.1) :=
    fun pq hpq => Finset.mem_image_of_mem _ hpq
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun pq => F (jointMultiset pq.2 pq.1))]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  have hconst : ∀ pq ∈ (monoOrbit α ×ˢ monoOrbit β).filter
      (fun pq => jointMultiset pq.2 pq.1 = X),
      F (jointMultiset pq.2 pq.1) = F X := fun pq hpq => by rw [(Finset.mem_filter.mp hpq).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- The cell counts of a margin-correct table sum to `k`: `∑_{(v,b)} Y v b = k`. Both
`∑_v∑_b` and the row margins recover the full slot count. (The `Fin k` version of the
`monoOrbit_card_eq_multinomial` margin sum, but over both axes.) -/
lemma marginCorrect_cells_sum {k : ℕ} (α β : MultiIndex k) (Y : CTable α β)
    (hY : Y ∈ MarginCorrectTables α β) :
    ∑ c : ↥(univ.image α) × ↥(univ.image β), (Y c.1 c.2 : ℕ) = k := by
  classical
  rw [MarginCorrectTables, Finset.mem_filter] at hY
  obtain ⟨-, hrow, -⟩ := hY
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun v _ => hrow v)]
  -- ∑_{v∈image α} #{i : α i = v} = k
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin k))) (t := (univ : Finset ↥(univ.image α)))
    (f := fun i => (⟨α i, Finset.mem_image_of_mem α (Finset.mem_univ i)⟩
      : ↥(univ.image α)))
    (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  conv_rhs => rw [hfib]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp [Subtype.ext_iff, eq_comm]

/-- **Fréchet lower bound** for a margin-correct table entry: `rowmargin v + colmargin b ≤
T v b + k`. (Equivalently `T v b ≥ rowmargin v + colmargin b - k`, the standard contingency-table
lower bound.) For the dominant `0`-value cell this caps the free range at `k - max(margins) =
#nonzero-positions`, so it shrinks the bounded enumeration's largest factor from `~k` to `~2·deg`. -/
lemma marginCorrect_frechet {k : ℕ} (α β : MultiIndex k) (T : CTable α β)
    (hT : T ∈ MarginCorrectTables α β) (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    (univ.filter (fun i => α i = v.val)).card + (univ.filter (fun i => β i = b.val)).card
      ≤ (T v b : ℕ) + k := by
  classical
  have hmem := hT
  rw [MarginCorrectTables, Finset.mem_filter] at hmem
  obtain ⟨-, hrow, hcol⟩ := hmem
  set rM : ↥(univ.image α) → ℕ := fun v' => (univ.filter (fun i => α i = v'.val)).card with hrMdef
  set cM : ↥(univ.image β) → ℕ := fun b' => (univ.filter (fun i => β i = b'.val)).card with hcMdef
  -- row-sums total to k
  have hrowsum : ∑ v' : ↥(univ.image α), rM v' = k := by
    have hcells := marginCorrect_cells_sum α β T hT
    rw [Fintype.sum_prod_type] at hcells
    calc ∑ v' : ↥(univ.image α), rM v'
        = ∑ v' : ↥(univ.image α), ∑ b' : ↥(univ.image β), (T v' b' : ℕ) :=
          Finset.sum_congr rfl (fun v' _ => (hrow v').symm)
      _ = k := hcells
  -- split the column margin off the `v` cell
  have hcolsplit : cM b = (T v b : ℕ) + ∑ v' ∈ univ.erase v, (T v' b : ℕ) :=
    calc cM b = ∑ v' : ↥(univ.image α), (T v' b : ℕ) := (hcol b).symm
      _ = (T v b : ℕ) + ∑ v' ∈ univ.erase v, (T v' b : ℕ) :=
          (Finset.add_sum_erase _ (fun v' => (T v' b : ℕ)) (Finset.mem_univ v)).symm
  -- split k off the `v` row
  have hksplit : k = rM v + ∑ v' ∈ univ.erase v, rM v' :=
    calc k = ∑ v' : ↥(univ.image α), rM v' := hrowsum.symm
      _ = rM v + ∑ v' ∈ univ.erase v, rM v' :=
          (Finset.add_sum_erase _ rM (Finset.mem_univ v)).symm
  -- each off-row column cell ≤ that row's full margin
  have hbound : ∑ v' ∈ univ.erase v, (T v' b : ℕ) ≤ ∑ v' ∈ univ.erase v, rM v' := by
    apply Finset.sum_le_sum
    intro v' _
    calc (T v' b : ℕ) ≤ ∑ b' : ↥(univ.image β), (T v' b' : ℕ) :=
          Finset.single_le_sum (f := fun b' => (T v' b' : ℕ)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ b)
      _ = rM v' := hrow v'
  show rM v + cM b ≤ (T v b : ℕ) + k
  omega

/-- **Pair-fiber count = full-cell multinomial.** The number of orbit pairs `(p,q)` whose joint
type is the margin-correct table `Y` equals the 2-D multinomial `k! / ∏_{(v,b)} (Y v b)!`. Each
`(p,q)` corresponds to a function `r : Fin k → (image α × image β)` (the per-slot value pair), the
orbit constraints being implied by `Y`'s margins; `card_fiberwise_eq_multinomial` then counts those
functions. The numerator analog of `jointType_fiber_card_eq_multinomial`, but over the orbit
product and landing on a single multinomial over all cells. -/
theorem pair_fiber_card_eq_multinomial {k : ℕ} (α β : MultiIndex k) (Y : CTable α β)
    (hY : Y ∈ MarginCorrectTables α β) :
    ((monoOrbit α ×ˢ monoOrbit β).filter
        (fun pq => jointMultiset pq.2 pq.1 = tableToMultiset α β Y)).card
      = Nat.multinomial (univ : Finset (↥(univ.image α) × ↥(univ.image β)))
          (fun c => (Y c.1 c.2 : ℕ)) := by
  classical
  set V := ↥(univ.image α) × ↥(univ.image β) with hVdef
  set h : V → ℕ := fun c => (Y c.1 c.2 : ℕ) with hh
  have hsum : ∑ c, h c = Fintype.card (Fin k) := by
    rw [Fintype.card_fin]; exact marginCorrect_cells_sum α β Y hY
  rw [← card_fiberwise_eq_multinomial h hsum]
  obtain ⟨-, hrow, hcol⟩ := Finset.mem_filter.mp hY
  apply Finset.card_bij'
    (i := fun (pq : MultiIndex k × MultiIndex k)
              (hpq : pq ∈ (monoOrbit α ×ˢ monoOrbit β).filter _) =>
            (fun idx =>
              ((⟨pq.1 idx, orbit_vals_mem α
                  (Finset.mem_product.mp (Finset.mem_of_mem_filter _ hpq)).1 idx⟩,
               ⟨pq.2 idx, orbit_vals_mem β
                  (Finset.mem_product.mp (Finset.mem_of_mem_filter _ hpq)).2 idx⟩) : V)))
    (j := fun (r : Fin k → V) (_ : r ∈ univ.filter (fun r => ∀ c,
              (univ.filter (fun i => r i = c)).card = h c)) =>
            (((fun idx => (r idx).1.val), (fun idx => (r idx).2.val))
              : MultiIndex k × MultiIndex k))
  case hi =>
    -- forward map lands in the function fiber set
    intro pq hpq
    obtain ⟨hmem, hjoint⟩ := Finset.mem_filter.mp hpq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro c
    -- #{i : r i = c} = #{i : pq.1 i = c.1.val ∧ pq.2 i = c.2.val}
    have hcard : (univ.filter (fun i =>
        ((⟨pq.1 i, orbit_vals_mem α (Finset.mem_product.mp hmem).1 i⟩,
          ⟨pq.2 i, orbit_vals_mem β (Finset.mem_product.mp hmem).2 i⟩) : V) = c)).card
          = (univ.filter (fun i => pq.1 i = c.1.val ∧ pq.2 i = c.2.val)).card := by
      apply congrArg Finset.card; apply Finset.filter_congr; intro i _
      simp [Prod.ext_iff, Subtype.ext_iff]
    rw [hcard, ← jointMultiset_count_eq pq.2 pq.1 c.1.val c.2.val, hjoint]
    have : ((c.1.val, c.2.val) : ℕ × ℕ)
        = ((c.1 : ↥(univ.image α)).val, (c.2 : ↥(univ.image β)).val) := rfl
    rw [this, tableToMultiset_count_mem]
  case hj =>
    -- backward map lands in the orbit-pair fiber set
    intro r hr
    have hPV := (Finset.mem_filter.mp hr).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · -- (r ·).1.val ∈ monoOrbit α
      rw [mem_monoOrbit_iff]
      intro c
      by_cases hc : c ∈ univ.image α
      · set vc : ↥(univ.image α) := ⟨c, hc⟩ with hvc
        have e1 : (univ.filter (fun i => (r i).1.val = c)).card
                = (univ.filter (fun i => (r i).1 = vc)).card := by
          apply congrArg Finset.card; apply Finset.filter_congr; intro i _
          simp [hvc, Subtype.ext_iff]
        have e2 : (univ.filter (fun i => (r i).1 = vc)).card
                = ∑ b : ↥(univ.image β), (univ.filter (fun i => r i = (vc, b))).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := fun i => (r i).2) (t := univ)
                (fun i _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.filter_filter]; apply congrArg Finset.card; apply Finset.filter_congr
          intro i _; rw [Prod.ext_iff]
        rw [e1, e2, Finset.sum_congr rfl (fun b _ => hPV (vc, b)), hrow vc]
      · have hcoe : (univ.filter (fun i => (r i).1.val = c)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _ heq; exact hc (heq ▸ (r i).1.2)
        have hα : (univ.filter (fun i => α i = c)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _ heq
          exact hc (heq ▸ Finset.mem_image_of_mem α (Finset.mem_univ i))
        rw [hcoe, hα]
    · -- (r ·).2.val ∈ monoOrbit β
      rw [mem_monoOrbit_iff]
      intro c
      by_cases hc : c ∈ univ.image β
      · set bc : ↥(univ.image β) := ⟨c, hc⟩ with hbc
        have e1 : (univ.filter (fun i => (r i).2.val = c)).card
                = (univ.filter (fun i => (r i).2 = bc)).card := by
          apply congrArg Finset.card; apply Finset.filter_congr; intro i _
          simp [hbc, Subtype.ext_iff]
        have e2 : (univ.filter (fun i => (r i).2 = bc)).card
                = ∑ v : ↥(univ.image α), (univ.filter (fun i => r i = (v, bc))).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := fun i => (r i).1) (t := univ)
                (fun i _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl; intro v _
          rw [Finset.filter_filter]; apply congrArg Finset.card; apply Finset.filter_congr
          intro i _; rw [Prod.ext_iff]; tauto
        rw [e1, e2, Finset.sum_congr rfl (fun v _ => hPV (v, bc)), hcol bc]
      · have hcoe : (univ.filter (fun i => (r i).2.val = c)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _ heq; exact hc (heq ▸ (r i).2.2)
        have hβ : (univ.filter (fun i => β i = c)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro i _ heq
          exact hc (heq ▸ Finset.mem_image_of_mem β (Finset.mem_univ i))
        rw [hcoe, hβ]
    · -- jointMultiset q p = tableToMultiset Y
      ext ⟨c, d⟩
      rw [jointMultiset_count_eq (fun idx => (r idx).2.val) (fun idx => (r idx).1.val) c d]
      by_cases hc : c ∈ univ.image α
      · by_cases hd : d ∈ univ.image β
        · have hrw : ((c, d) : ℕ × ℕ)
              = ((⟨c, hc⟩ : ↥(univ.image α)).val, (⟨d, hd⟩ : ↥(univ.image β)).val) := rfl
          rw [hrw, tableToMultiset_count_mem]
          have : (univ.filter (fun i => (r i).1.val = c ∧ (r i).2.val = d)).card
              = (univ.filter (fun i => r i = (⟨c, hc⟩, ⟨d, hd⟩))).card := by
            apply congrArg Finset.card; apply Finset.filter_congr; intro i _
            simp [Prod.ext_iff, Subtype.ext_iff]
          rw [this]; exact hPV (⟨c, hc⟩, ⟨d, hd⟩)
        · rw [tableToMultiset_count_not_mem α β _ c d (Or.inr hd),
              Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro i _ ⟨-, h2⟩
          exact hd (h2 ▸ (r i).2.2)
      · rw [tableToMultiset_count_not_mem α β _ c d (Or.inl hc),
            Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro i _ ⟨h1, -⟩
        exact hc (h1 ▸ (r i).1.2)
  case left_inv =>
    intro pq _; exact Prod.ext (funext fun _ => rfl) (funext fun _ => rfl)
  case right_inv =>
    intro r _; funext idx; exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- **General-column row-collapse.** Summing the joint fiber `#{i : p i = v ∧ q i = b}`
over all column values `b ∈ image β` recovers the row fiber `#{i : p i = v}`, provided the
column vector `q` is `image β`-valued. The numerator analog of `sum_joint_eq_fiber`, but with
the column vector `q` free instead of the section `β`. -/
lemma joint_sum_over_col (p q : MultiIndex k) (hq : ∀ i, q i ∈ univ.image β) (v : ℕ) :
    ∑ b : ↥(univ.image β), (univ.filter (fun i => p i = v ∧ q i = b.val)).card
      = (univ.filter (fun i => p i = v)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := univ.filter (fun i => p i = v))
        (f := fun i => (⟨q i, hq i⟩ : ↥(univ.image β)))
        (t := univ) (fun i _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.filter_filter]
  apply congrArg Finset.card; apply Finset.filter_congr; intro i _
  simp [Subtype.ext_iff, and_comm]

/-- **General-column column-collapse.** Summing the joint fiber over all row values
`v ∈ image α` recovers the column fiber `#{i : q i = b}`, provided the row vector `p` is
`image α`-valued. The numerator analog of `sum_joint_eq_fiber_col`. -/
lemma joint_sum_over_row (p q : MultiIndex k) (hp : ∀ i, p i ∈ univ.image α) (b : ℕ) :
    ∑ v : ↥(univ.image α), (univ.filter (fun i => p i = v.val ∧ q i = b)).card
      = (univ.filter (fun i => q i = b)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := univ.filter (fun i => q i = b))
        (f := fun i => (⟨p i, hp i⟩ : ↥(univ.image α)))
        (t := univ) (fun i _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.filter_filter]
  apply congrArg Finset.card; apply Finset.filter_congr; intro i _
  simp [Subtype.ext_iff, and_comm]

/-- The cell `(v,b)` of the table read off the joint multiset `jointMultiset q p` is the
joint fiber count `#{i : p i = v ∧ q i = b}` (the count is `≤ k`, so the clamp is inactive). -/
lemma joint_entry (p q : MultiIndex k) (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    ((multisetToTable α β (jointMultiset q p) v b : ℕ))
      = (univ.filter (fun i => p i = v.val ∧ q i = b.val)).card := by
  simp only [multisetToTable]
  rw [jointMultiset_count_eq q p v.val b.val]
  exact min_eq_left
    ((Finset.card_filter_le _ _).trans_eq (by rw [Finset.card_univ, Fintype.card_fin]))

/-- **Margin-correctness of a general joint type.** For `p ∈ monoOrbit α`, `q ∈ monoOrbit β`,
the table read off `jointMultiset q p` is margin-correct: its row margins are α's fiber sizes
(p shares α's histogram), its column margins are β's (q shares β's). The product-orbit analog
of `orbitTable_mem`, where the column vector `q` is a general orbit element instead of `β`. -/
lemma joint_multisetToTable_mem (p q : MultiIndex k)
    (hp : p ∈ monoOrbit α) (hq : q ∈ monoOrbit β) :
    multisetToTable α β (jointMultiset q p) ∈ MarginCorrectTables α β := by
  classical
  rw [MarginCorrectTables, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro v
    rw [Finset.sum_congr rfl (fun b _ => joint_entry α β p q v b),
        joint_sum_over_col β p q (fun i => orbit_vals_mem β hq i) v.val]
    exact (mem_monoOrbit_iff α p).mp hp v.val
  · intro b
    rw [Finset.sum_congr rfl (fun v _ => joint_entry α β p q v b),
        joint_sum_over_row α p q (fun i => orbit_vals_mem α hp i) b.val]
    exact (mem_monoOrbit_iff β q).mp hq b.val

/-- **Realized roundtrip for a general joint type.** Reading the table off `jointMultiset q p`
and naming its multiset recovers the original (entries `≤ k`, support inside `image α × image β`).
The product-orbit analog of `tableToMultiset_orbitTable`. -/
lemma tableToMultiset_jointTable (p q : MultiIndex k)
    (hp : ∀ i, p i ∈ univ.image α) (hq : ∀ i, q i ∈ univ.image β) :
    tableToMultiset α β (multisetToTable α β (jointMultiset q p)) = jointMultiset q p := by
  ext ⟨c, d⟩
  by_cases hc : c ∈ univ.image α
  · by_cases hd : d ∈ univ.image β
    · have hrw : ((c, d) : ℕ × ℕ)
          = ((⟨c, hc⟩ : ↥(univ.image α)).val, (⟨d, hd⟩ : ↥(univ.image β)).val) := rfl
      rw [hrw, tableToMultiset_count_mem, joint_entry, ← jointMultiset_count_eq q p c d]
    · rw [tableToMultiset_count_not_mem α β _ c d (Or.inr hd),
          jointMultiset_count_eq q p c d]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i _ ⟨-, h2⟩
      exact hd (h2 ▸ hq i)
  · rw [tableToMultiset_count_not_mem α β _ c d (Or.inl hc),
        jointMultiset_count_eq q p c d]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i _ ⟨h1, -⟩
    exact hc (h1 ▸ hp i)

/-- **Product-orbit image collapses to the single-orbit image.** The distinct joint types
arising from the full orbit pair `monoOrbit α × monoOrbit β` are exactly those arising from a
single α-orbit element against the fixed `β`: every joint type `jointMultiset q p` is realized
as `jointMultiset β p'` (via the realizability converse applied to its margin-correct table),
and conversely `jointMultiset β p = jointMultiset pq.2 pq.1` with `pq = (p, β)`. This lets the
pair-orbit regrouping reuse the denominator's table bijection. -/
lemma pair_image_eq :
    (monoOrbit α ×ˢ monoOrbit β).image (fun pq => jointMultiset pq.2 pq.1)
      = (monoOrbit α).image (jointMultiset β) := by
  classical
  apply Finset.Subset.antisymm
  · intro X hX
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨p', hp', heq⟩ :=
      table_realized_in_orbit α β _ (joint_multisetToTable_mem α β pq.1 pq.2 hp hq)
    rw [tableToMultiset_jointTable α β pq.1 pq.2
          (fun i => orbit_vals_mem α hp i) (fun i => orbit_vals_mem β hq i)] at heq
    exact Finset.mem_image.mpr ⟨p', hp', heq⟩
  · intro X hX
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hX
    refine Finset.mem_image.mpr ⟨(p, β), Finset.mem_product.mpr ⟨hp, ?_⟩, rfl⟩
    exact (mem_monoOrbit_iff β β).mpr (fun _ => rfl)

/-- **Orbit-free cross-orbit numerator re-index.** The pair-weighted double orbit sum (the
combinatorial numerator, via `numerator_combinatorial_pairWeight`) re-indexes over the
margin-correct contingency tables: each table `T` contributes the full-cell 2-D multinomial
`k! / ∏_{(v,b)} (T v b)!` times the numerator pair weight of its multiset. The numerator analog
of `orbitCore_eq_multinomial_sum_orbitFree`. Combines `pairOrbit_regroup`, the image collapse
`pair_image_eq`, the denominator's table bijection, and `pair_fiber_card_eq_multinomial` for the
fiber count. Axiom-clean (realizability already discharged). -/
theorem numerator_orbitFree :
    ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, pairWeight (jointMultiset q p)
      = ∑ T ∈ MarginCorrectTables α β,
          (Nat.multinomial (univ : Finset (↥(univ.image α) × ↥(univ.image β)))
              (fun c => (T c.1 c.2 : ℕ)) : ℚ)
            * pairWeight (tableToMultiset α β T) := by
  classical
  rw [pairOrbit_regroup α β pairWeight, pair_image_eq]
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
    have hvals : ∀ i, p i ∈ univ.image α := fun i => orbit_vals_mem α hp i
    have hround : tableToMultiset α β (orbitTable α β p) = jointMultiset β p :=
      tableToMultiset_orbitTable α β p hvals
    dsimp only
    rw [multisetToTable_jointMultiset, hround]
    congr 1
    norm_cast
    rw [← hround,
        pair_fiber_card_eq_multinomial α β (orbitTable α β p) (orbitTable_mem α β p hp)]

/-- **Fully orbit-free cross-orbit numerator matrix entry.** The full off-diagonal orbit-pair
numerator (the marked-coordinate triple sum of `dirichletIntegralWithSlack`) equals the
orbit-free contingency-table sum over `MarginCorrectTables`, divided by the constant factorial
`(n+1+|α|+|β|+1)!`. Chains `orbitPair_numerator_eq` (factor out the constant Dirichlet
denominator), `numerator_combinatorial_pairWeight` (regroup the marked sum into the pair weight),
and `numerator_orbitFree` (the (p,q)-joint-type re-index). Unlike the denominator, no orbit
cardinality factor survives: the numerator regroups over the full joint type, so the q-collapse
is never used. The right-hand side has **no** `monoOrbit` — every object is computable from the
shapes of α and β. -/
theorem orbitPair_numerator_orbitFree {n : ℕ} (α β : MultiIndex (n + 1)) :
    (∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
        (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack (Fin.removeNth i (p + q)) (p i + q i + 2))
      = (∑ T ∈ MarginCorrectTables α β,
            (Nat.multinomial (univ : Finset (↥(univ.image α) × ↥(univ.image β)))
                (fun c => (T c.1 c.2 : ℕ)) : ℚ)
              * pairWeight (tableToMultiset α β T))
          / (((n + 1) + α.degree + β.degree + 1).factorial : ℚ) := by
  rw [orbitPair_numerator_eq, numerator_combinatorial_pairWeight, numerator_orbitFree]

/-- Computable twin of `pairWeight` (the library's `jointWeight` factor is gratuitously
`noncomputable`; `markedSum` is already computable). `= pairWeight` by `rfl`. -/
def pairWeightC (X : Multiset (ℕ × ℕ)) : ℚ := jointWeightC X * markedSum X

@[simp] lemma pairWeightC_eq (X : Multiset (ℕ × ℕ)) : pairWeightC X = pairWeight X := rfl

/-- **`native_decide`-ready numerator matrix entry.** `orbitPair_numerator_orbitFree` restated
with the computable `pairWeightC`. Every operation on the right reduces in the kernel: the
Fintype-enumerated `MarginCorrectTables`, `Nat.multinomial`, `tableToMultiset`, and `pairWeightC`.
(Defeq to the shape-form, since `pairWeightC = pairWeight`.) -/
theorem orbitPair_numerator_computable {n : ℕ} (α β : MultiIndex (n + 1)) :
    (∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
        (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack (Fin.removeNth i (p + q)) (p i + q i + 2))
      = (∑ T ∈ MarginCorrectTables α β,
            (Nat.multinomial (univ : Finset (↥(univ.image α) × ↥(univ.image β)))
                (fun c => (T c.1 c.2 : ℕ)) : ℚ)
              * pairWeightC (tableToMultiset α β T))
          / (((n + 1) + α.degree + β.degree + 1).factorial : ℚ) :=
  orbitPair_numerator_orbitFree α β

/-! ## Cross-orbit Rayleigh matrix entries

The `Mr[λ][μ]` matrix entries of the symmetric-reduction Gram matrix are bilinear forms in two
polynomial sieve weights. For the orbit basis `orbitSum λ`, the denominator/numerator cross
terms evaluate to the orbit-pair sums computed orbit-freely above, so each matrix entry is a
closed form computable from the shapes `λ, μ` alone. These are the building blocks of the
bilinear expansion `polynomialMaynard* (∑_λ c_λ orbitSum λ) = ∑_{λ,μ} c_λ c_μ Mr[λ][μ]`
(the remaining assembly step needs the disjoint-orbit-union weight representation). -/

/-- The **cross denominator** of two polynomial sieve weights: `∫ (P·Q)` over the simplex,
`∑_{p∈P}∑_{q∈Q} c_p c_q monomialIntegral(p+q)`. `crossDenominator P P = polynomialMaynardDenominator P`
by definition; the symmetric Gram-matrix denominator entry is `crossDenominator (orbitSum λ) (orbitSum μ)`. -/
noncomputable def crossDenominator {k : ℕ} (P Q : PolynomialSieveWeight k) : ℚ :=
  ∑ p ∈ P.terms, ∑ q ∈ Q.terms, p.2 * q.2 * monomialIntegral (p.1 + q.1)

/-- The **cross numerator** of two polynomial sieve weights (the `Mk` numerator bilinear form,
`k = n+1`): the marked-coordinate triple sum of `dirichletIntegralWithSlack`. `crossNumerator P P
= polynomialMaynardNumerator P` for `k = n+1`. -/
noncomputable def crossNumerator {n : ℕ} (P Q : PolynomialSieveWeight (n + 1)) : ℚ :=
  ∑ i : Fin (n + 1), ∑ p ∈ P.terms, ∑ q ∈ Q.terms,
    (p.2 * q.2 : ℚ) / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
      dirichletIntegralWithSlack (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2)

/-- `orbitSum`'s terms are the orbit vectors with coefficient `1`. -/
lemma orbitSum_terms {k : ℕ} (α : MultiIndex k) :
    (orbitSum α).terms = (monoOrbit α).image (fun m : MultiIndex k => (m, (1 : ℚ))) := by
  unfold orbitSum monoOrbit; rw [Finset.image_image]; rfl

private lemma coe_one_inj {k : ℕ} (s : Finset (MultiIndex k)) :
    ∀ a ∈ s, ∀ b ∈ s, ((a, (1 : ℚ)) : MultiIndex k × ℚ) = (b, 1) → a = b :=
  fun a _ b _ h => ((Prod.mk.injEq _ _ _ _).mp h).1

/-- **Cross-orbit denominator entry = orbit-pair sum.** The Gram-matrix denominator entry of the
orbit basis is the off-diagonal orbit-pair sum (`orbitPair_denominator_*`); the diagonal recovers
`polynomialMaynardDenominator_orbitSum`. -/
lemma crossDenominator_orbitSum {k : ℕ} (α β : MultiIndex k) :
    crossDenominator (orbitSum α) (orbitSum β)
      = ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β, monomialIntegral (p + q) := by
  unfold crossDenominator
  rw [orbitSum_terms, Finset.sum_image (coe_one_inj _)]
  refine Finset.sum_congr rfl (fun pm _ => ?_)
  rw [orbitSum_terms, Finset.sum_image (coe_one_inj _)]
  refine Finset.sum_congr rfl (fun qm _ => ?_)
  simp

/-- **Cross-orbit numerator entry = orbit-pair marked sum.** The Gram-matrix numerator entry of
the orbit basis is the marked-coordinate orbit-pair sum (`orbitPair_numerator_*`). -/
lemma crossNumerator_orbitSum {n : ℕ} (α β : MultiIndex (n + 1)) :
    crossNumerator (orbitSum α) (orbitSum β)
      = ∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
          (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
            dirichletIntegralWithSlack (Fin.removeNth i (p + q)) (p i + q i + 2) := by
  unfold crossNumerator
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [orbitSum_terms, Finset.sum_image (coe_one_inj _)]
  refine Finset.sum_congr rfl (fun pm _ => ?_)
  rw [orbitSum_terms, Finset.sum_image (coe_one_inj _)]
  refine Finset.sum_congr rfl (fun qm _ => ?_)
  simp

/-- **`native_decide`-ready denominator Gram entry.** The orbit-basis denominator matrix entry as
a closed form computable from the shapes `α, β` (no `monoOrbit`). -/
theorem crossDenominator_orbitSum_computable {k : ℕ} (α β : MultiIndex k) :
    crossDenominator (orbitSum α) (orbitSum β)
      = ((Nat.multinomial (univ : Finset ↥(univ.image β))
            (fun b => (univ.filter (fun i => β i = b.val)).card)) •
          ∑ T ∈ MarginCorrectTables α β,
            (∏ b : ↥(univ.image β), (Nat.multinomial univ
                (fun v : ↥(univ.image α) => (T v b : ℕ)) : ℚ))
              * jointWeightC (tableToMultiset α β T))
          / ((k + α.degree + β.degree).factorial : ℚ) :=
  (crossDenominator_orbitSum α β).trans (orbitPair_denominator_computable α β)

/-- **`native_decide`-ready numerator Gram entry.** The orbit-basis numerator matrix entry as a
closed form computable from the shapes `α, β` (no `monoOrbit`, no orbit cardinality factor). -/
theorem crossNumerator_orbitSum_computable {n : ℕ} (α β : MultiIndex (n + 1)) :
    crossNumerator (orbitSum α) (orbitSum β)
      = (∑ T ∈ MarginCorrectTables α β,
            (Nat.multinomial (univ : Finset (↥(univ.image α) × ↥(univ.image β)))
                (fun c => (T c.1 c.2 : ℕ)) : ℚ)
              * pairWeightC (tableToMultiset α β T))
          / (((n + 1) + α.degree + β.degree + 1).factorial : ℚ) :=
  (crossNumerator_orbitSum α β).trans (orbitPair_numerator_computable α β)

/-! ## Symmetric weights and the bilinear (Gram) expansion

A symmetric polynomial sieve weight is a linear combination `∑_λ c_λ orbitSum λ` over a family
`R` of orbit representatives. Its terms are the disjoint union of the per-orbit term sets (orbit
vectors carrying coefficient `c λ`). Because distinct representatives have disjoint orbits, the
Maynard denominator/numerator — both bilinear in the terms — expand as the Gram quadratic form
`∑_{λ,μ∈R} c_λ c_μ Mr[λ][μ]` with `Mr` the cross-orbit entries above. -/

/-- The **symmetric weight** `∑_{λ∈R} c_λ · orbitSum λ`: terms are the per-orbit vectors carrying
coefficient `c λ`, disjointly unioned over the representative family `R`. -/
noncomputable def symWeight {k : ℕ} (R : Finset (MultiIndex k)) (c : MultiIndex k → ℚ) :
    PolynomialSieveWeight k :=
  ⟨R.biUnion (fun lam => (monoOrbit lam).image (fun v => (v, c lam)))⟩

/-- The per-orbit term sets of a symmetric weight are pairwise disjoint, given that distinct
representatives have disjoint orbits (a `(v, c a) = (w, c b)` forces `v = w ∈ orbit a ∩ orbit b`). -/
lemma symWeight_termSets_disjoint {k : ℕ} (R : Finset (MultiIndex k)) (c : MultiIndex k → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    (R : Set (MultiIndex k)).PairwiseDisjoint
      (fun lam => (monoOrbit lam).image (fun v => (v, c lam))) := by
  intro a ha b hb hab
  rw [Function.onFun, Finset.disjoint_left]
  rintro x hxa hxb
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hxa
  obtain ⟨w, hw, hw2⟩ := Finset.mem_image.mp hxb
  have hvw : w = v := congrArg Prod.fst hw2
  exact (hR a ha b hb hab).forall_ne_finset hv (hvw ▸ hw) rfl

private lemma fst_inj {k : ℕ} (c : ℚ) (s : Finset (MultiIndex k)) :
    ∀ x ∈ s, ∀ y ∈ s, ((fun v => (v, c)) x : MultiIndex k × ℚ) = (fun v => (v, c)) y → x = y :=
  fun _ _ _ _ h => congrArg Prod.fst h

/-- **Bilinear (Gram) expansion of the denominator.** The Maynard denominator of a symmetric
weight is the quadratic form `∑_{a,b∈R} c_a c_b · crossDenominator (orbitSum a) (orbitSum b)` in
the orbit basis. Each entry is the `native_decide`-ready closed form
`crossDenominator_orbitSum_computable`. -/
theorem polynomialMaynardDenominator_symWeight {k : ℕ} (R : Finset (MultiIndex k))
    (c : MultiIndex k → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMaynardDenominator (symWeight R c)
      = ∑ a ∈ R, ∑ b ∈ R, c a * c b * crossDenominator (orbitSum a) (orbitSum b) := by
  classical
  have hdisj := symWeight_termSets_disjoint R c hR
  unfold polynomialMaynardDenominator symWeight
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_biUnion hdisj), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [crossDenominator_orbitSum,
      Finset.sum_image (fst_inj (c a) (monoOrbit a)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_image (fst_inj (c b) (monoOrbit b)), Finset.mul_sum]

/-- **Disjoint-union double-sum reindex.** Any bilinear summand `h p q` summed over the term
pairs of a symmetric weight regroups over the orbit basis: `∑_{a,b∈R} ∑_{v∈orbit a}∑_{w∈orbit b}
h (v, c_a) (w, c_b)`. The shared engine for both the denominator and numerator bilinear
expansions (double `sum_biUnion` + per-orbit `sum_image`). -/
lemma symWeight_double_sum {k : ℕ} (R : Finset (MultiIndex k)) (c : MultiIndex k → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (h : (MultiIndex k × ℚ) → (MultiIndex k × ℚ) → ℚ) :
    ∑ p ∈ (symWeight R c).terms, ∑ q ∈ (symWeight R c).terms, h p q
      = ∑ a ∈ R, ∑ b ∈ R, ∑ v ∈ monoOrbit a, ∑ w ∈ monoOrbit b, h (v, c a) (w, c b) := by
  classical
  have hdisj := symWeight_termSets_disjoint R c hR
  show ∑ p ∈ R.biUnion _, ∑ q ∈ R.biUnion _, h p q = _
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_biUnion hdisj), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.sum_image (fst_inj (c a) (monoOrbit a))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_image (fst_inj (c b) (monoOrbit b))]

/-- **Bilinear (Gram) expansion of the numerator.** The Maynard numerator of a symmetric weight
is the quadratic form `∑_{a,b∈R} c_a c_b · crossNumerator (orbitSum a) (orbitSum b)` in the orbit
basis. Applies `symWeight_double_sum` per marked coordinate `i`, then commutes the `∑ i` inward to
collect each `crossNumerator` entry. Each entry is `crossNumerator_orbitSum_computable`. -/
theorem polynomialMaynardNumerator_symWeight {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMaynardNumerator (symWeight R c)
      = ∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator (orbitSum a) (orbitSum b) := by
  classical
  simp only [polynomialMaynardNumerator]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
        symWeight_double_sum R c hR
          (fun p q => (p.2 * q.2 : ℚ) / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
            dirichletIntegralWithSlack (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2)))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [crossNumerator_orbitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  dsimp only
  ring

/-- **Symmetric Maynard ratio as a Gram quotient.** The polynomial Maynard ratio of a symmetric
weight `∑_{λ∈R} c_λ orbitSum λ` is the orbit-basis quadratic-form quotient
`(∑ c_a c_b crossNumerator) / (∑ c_a c_b crossDenominator)`. Both Gram matrices are entrywise
`native_decide`-ready closed forms (`crossNumerator_orbitSum_computable`,
`crossDenominator_orbitSum_computable`) — so the whole ratio is computable from the shapes in `R`
and the coefficients `c`, with no `monoOrbit` enumeration. This is the object whose `> 4` (at
`k = 54`, degree ≥ 9) discharges `mk_54_witness_under_EH` via `Mk_ge_polynomialMkF`. -/
theorem polynomialMkF_symWeight {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMkF (symWeight R c)
      = (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator (orbitSum a) (orbitSum b))
          / (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossDenominator (orbitSum a) (orbitSum b)) := by
  unfold polynomialMkF
  rw [polynomialMaynardNumerator_symWeight R c hR,
      polynomialMaynardDenominator_symWeight R c hR]

/-- **Orbits partition.** Two monomial orbits are either equal or disjoint: they share an element
iff the two monomials have the same value-histogram, in which case their orbits coincide
(`mem_monoOrbit_iff`). -/
lemma monoOrbit_eq_or_disjoint {k : ℕ} (a b : MultiIndex k) :
    monoOrbit a = monoOrbit b ∨ Disjoint (monoOrbit a) (monoOrbit b) := by
  classical
  by_cases h : ∀ v, (univ.filter (fun i => a i = v)).card
      = (univ.filter (fun i => b i = v)).card
  · left
    apply Finset.ext; intro p
    rw [mem_monoOrbit_iff, mem_monoOrbit_iff]
    constructor
    · intro hp v; rw [hp v]; exact h v
    · intro hp v; rw [hp v]; exact (h v).symm
  · right
    rw [Finset.disjoint_left]
    intro p hpa hpb
    apply h
    intro v
    rw [← (mem_monoOrbit_iff a p).mp hpa v, (mem_monoOrbit_iff b p).mp hpb v]

/-- **Disjointness from distinct orbits.** The `symWeight` disjointness hypothesis `hR` is implied
by the cleaner "distinct representatives lie in distinct orbits" — which for a canonical (e.g.
non-increasing) representative set is just "distinct value-multisets". Discharges `hR` for the
`Mk` witness lemmas at a concrete `k`. -/
lemma disjoint_of_distinct_orbit {k : ℕ} (R : Finset (MultiIndex k))
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → monoOrbit a ≠ monoOrbit b) :
    ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b) :=
  fun a ha b hb hab => (monoOrbit_eq_or_disjoint a b).resolve_left (hR a ha b hb hab)

/-- **Distinct orbits from a histogram witness.** A single value `v` where `a` and `b` have
different fiber sizes certifies `monoOrbit a ≠ monoOrbit b` (equal orbits ⟹ same histogram, since
`a ∈ monoOrbit a`). Since `monoOrbit` is `noncomputable`, this histogram form — not a direct
`decide` on orbit equality — is how `hR` gets discharged. -/
lemma monoOrbit_ne_of_histogram_witness {k : ℕ} (a b : MultiIndex k) (v : ℕ)
    (h : (univ.filter (fun i => a i = v)).card ≠ (univ.filter (fun i => b i = v)).card) :
    monoOrbit a ≠ monoOrbit b := by
  intro heq
  apply h
  have ha : a ∈ monoOrbit b := heq ▸ (mem_monoOrbit_iff a a).mpr (fun _ => rfl)
  exact (mem_monoOrbit_iff b a).mp ha v

/-- **Decidable discharge of the `symWeight` disjointness `hR`.** Reduces `hR` to the **decidable**
proposition "every distinct pair in `R` differs in some value-fiber size" (the search bounded to
`image a ∪ image b`). For concrete `R` the hypothesis is closed by `decide` / `native_decide`;
it is exactly "distinct representatives have distinct value-multisets". -/
lemma disjoint_of_histogram {k : ℕ} (R : Finset (MultiIndex k))
    (h : ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
        ∃ v ∈ univ.image a ∪ univ.image b,
          (univ.filter (fun i => a i = v)).card ≠ (univ.filter (fun i => b i = v)).card) :
    ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b) := by
  intro a ha b hb hab
  obtain ⟨v, _, hv⟩ := h a ha b hb hab
  exact (monoOrbit_eq_or_disjoint a b).resolve_left (monoOrbit_ne_of_histogram_witness a b v hv)

/-- **Symmetric-weight `Mk` witness.** A symmetric weight whose orbit-basis Gram quotient exceeds
`4` certifies `Mk (n+1) > 4`. Combines `polynomialMkF_symWeight` with the abstract bridge
`Mk_gt_four_of_polynomial_witness` (`Mk_ge_polynomialMkF` + `polynomialMkF_eq_MkF`). This reduces
the witness goal to a **single rational inequality** on the two `native_decide`-ready Gram
matrices — the only step left for `mk_54_witness_under_EH` is to plug in the `k=54` orbit
representatives `R`, the LDL eigenvector coefficients `c`, discharge the disjointness `hR` (via
`disjoint_of_distinct_orbit`), and `native_decide` the quotient. -/
theorem Mk_gt_four_of_symWeight_witness {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (4 : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator (orbitSum a) (orbitSum b))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossDenominator (orbitSum a) (orbitSum b))) :
    Sieve.Mk (n + 1) > 4 := by
  apply Mk_gt_four_of_polynomial_witness (symWeight R c)
  rw [polynomialMkF_symWeight R c hR]
  exact_mod_cast hwit

/-- **Symmetric-weight `Mk` lower bound, general threshold.** A symmetric weight whose orbit-basis
Gram quotient exceeds a rational `T` certifies `Mk (n+1) > T`. Generalizes
`Mk_gt_four_of_symWeight_witness` to any threshold; pairs with `exists_theta_of_Mk_gt` to discharge
any `2·m/ϑ` EH witness. Routes through the real `Mk_ge_polynomialMkF` + `polynomialMkF_eq_MkF`. -/
theorem Mk_gt_of_symWeight_witness {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator (orbitSum a) (orbitSum b))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossDenominator (orbitSum a) (orbitSum b))) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  have h1 := Mk_ge_polynomialMkF (symWeight R c)
  rw [ge_iff_le, polynomialMkF_eq_MkF, polynomialMkF_symWeight R c hR] at h1
  exact lt_of_lt_of_le (by exact_mod_cast hwit) h1

/-- **EH-witness existential, general threshold.** For any positive `T < Mk k`, there is `ϑ∈(0,1)`
with `Mk k > T/ϑ` (take `ϑ` the midpoint of `(T/M, 1)`, which is `<1` since `T<M`). The Polymath8b
EH witnesses are the case `T = 2·m`: `mk_54` (`m=2`), `mk_5511` (`m=3`), `mk_41588` (`m=4`),
`mk_309661` (`m=5`). -/
theorem exists_theta_of_Mk_gt {k : ℕ} (T : ℝ) (hT : 0 < T) (h : T < Sieve.Mk k) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk k > T / ϑ := by
  have hM : (0 : ℝ) < Sieve.Mk k := lt_trans hT h
  set M := Sieve.Mk k with hMdef
  have hTM : T / M < 1 := (div_lt_one hM).mpr h
  have hTMpos : 0 < T / M := div_pos hT hM
  refine ⟨(T / M + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  have hϑpos : 0 < (T / M + 1) / 2 := by linarith
  rw [gt_iff_lt, div_lt_iff₀ hϑpos]
  calc T = M * (T / M) := by field_simp
    _ < M * ((T / M + 1) / 2) := by apply mul_lt_mul_of_pos_left _ hM; linarith

/-- **EH-witness existential from `Mk k > 4`.** The `mk_54_witness_under_EH` shape `∃ ϑ∈(0,1),
Mk k > 2·2/ϑ` follows from bare `Mk k > 4` (the `T = 4` case of `exists_theta_of_Mk_gt`). Turns a
`native_decide`'d `Mk 54 > 4` into exactly the axiom's statement. -/
theorem exists_theta_of_Mk_gt_four {k : ℕ} (h : (4 : ℝ) < Sieve.Mk k) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk k > 2 * 2 / ϑ := by
  obtain ⟨ϑ, hϑ, hgt⟩ := exists_theta_of_Mk_gt 4 (by norm_num) h
  exact ⟨ϑ, hϑ, by rw [show (2 : ℝ) * 2 = 4 by norm_num]; exact hgt⟩

/-- **Conditional discharge of `mk_54_witness_under_EH`.** Given `k = 54` orbit representatives
`R` (pairwise-disjoint orbits — supply `disjoint_of_histogram R (by native_decide)`) and LDL
coefficients `c` whose orbit-basis Gram quotient exceeds `4` (a pure rational `native_decide`), the
Polymath8b EH-witness for `k = 54` holds. This is the entire reduction: orbit symmetry →
`native_decide`-ready Gram matrices → `Mk 54 > 4` → the EH-witness existential. The remaining input
is the concrete `(R, c)` and the two `native_decide`s. -/
theorem mk_54_witness_under_EH_of_symWeight (R : Finset (MultiIndex (53 + 1)))
    (c : MultiIndex (53 + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (4 : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator (orbitSum a) (orbitSum b))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossDenominator (orbitSum a) (orbitSum b))) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 54 > 2 * 2 / ϑ :=
  exists_theta_of_Mk_gt_four (Mk_gt_four_of_symWeight_witness R c hR hwit)

/-! ## Computable Gram entries — the `native_decide` bridge

`crossDenominator`/`crossNumerator` are `noncomputable` (they go through `monomialIntegral` /
`dirichletIntegralWithSlack`), so a witness stated with them cannot be `native_decide`'d. These
`def`s are their `native_decide`-ready closed forms (`= crossDenominator_orbitSum_computable` /
`crossNumerator_orbitSum_computable`, by definitional unfolding); the witness restated with them
*is* `native_decide`-able. Verified in-kernel: `gramDenEntry ![2,1,0] ![1,1,0] = 11/3360`,
`gramNumEntry ![2,1,0] ![1,1,0] = 7/2160`. -/

/-- Computable denominator Gram entry (`= crossDenominator (orbitSum a) (orbitSum b)`). -/
def gramDenEntry {k : ℕ} (a b : MultiIndex k) : ℚ :=
  ((Nat.multinomial (univ : Finset ↥(univ.image b))
        (fun bb => (univ.filter (fun i => b i = bb.val)).card)) •
      ∑ T ∈ MarginCorrectTables a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => (T v bb : ℕ)) : ℚ))
          * jointWeightC (tableToMultiset a b T))
    / ((k + a.degree + b.degree).factorial : ℚ)

/-- Computable numerator Gram entry (`= crossNumerator (orbitSum a) (orbitSum b)`). -/
def gramNumEntry {n : ℕ} (a b : MultiIndex (n + 1)) : ℚ :=
  (∑ T ∈ MarginCorrectTables a b,
      (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => (T c.1 c.2 : ℕ)) : ℚ)
        * pairWeightC (tableToMultiset a b T))
    / (((n + 1) + a.degree + b.degree + 1).factorial : ℚ)

lemma gramDenEntry_eq {k : ℕ} (a b : MultiIndex k) :
    crossDenominator (orbitSum a) (orbitSum b) = gramDenEntry a b :=
  crossDenominator_orbitSum_computable a b

lemma gramNumEntry_eq {n : ℕ} (a b : MultiIndex (n + 1)) :
    crossNumerator (orbitSum a) (orbitSum b) = gramNumEntry a b :=
  crossNumerator_orbitSum_computable a b

/-! ## Margin-bounded tables — the tractable `native_decide` enumeration

`MarginCorrectTables α β` is `univ.filter` over `CTable α β = img(α) → img(β) → Fin (k+1)`,
whose `univ` has cardinality `(k+1)^(|img α|·|img β|)`. For any real witness (orbits with
`≥ 3` distinct exponent values, hence `≥ 9` cells) this is astronomically large — `native_decide`
on `gram*Entry` is infeasible even at `k = 6`. But margin-correctness forces every entry
`T v b ≤ min(rowmargin v, colmargin b)` (a single term is `≤` its row/column sum), so re-typing
the entries to `Fin (min + 1)` is a **value-preserving bijection** on the margin-correct tables.
The bounded `univ` has cardinality `∏ (min + 1)` — and since the only large margins are the
`0`-value ones, this is `(k+1) · (small)^(cells-1)` (e.g. `(k+1)·2⁸ ≈ 77k` for an img-3 pair vs
`(k+1)⁹ ≈ 10²²`). The expensive bignum multinomials run only on the *accepted* (filtered) tables.
`gram*EntryBdd` is `gram*Entry` restated over this bounded type; the witness lemmas use it. -/

/-- Margin-bounded contingency table: entry `(v,b)` capped at `min(rowmargin v, colmargin b)`. -/
abbrev CTableBdd : Type :=
  (v : ↥(univ.image α)) → (b : ↥(univ.image β)) →
    Fin (min ((univ.filter (fun i => α i = v.val)).card)
             ((univ.filter (fun i => β i = b.val)).card) + 1)

/-- Margin-correct bounded tables: same margin filter as `MarginCorrectTables`, over the
bounded type. Its `univ` is `∏ (min+1)` — tractable. -/
def MarginCorrectTablesBdd : Finset (CTableBdd α β) :=
  univ.filter (fun T =>
    (∀ v, ∑ b, (T v b : ℕ) = (univ.filter (fun i => α i = v.val)).card) ∧
    (∀ b, ∑ v, (T v b : ℕ) = (univ.filter (fun i => β i = b.val)).card))

/-- The joint multiset named by a bounded table (identical formula to `tableToMultiset`). -/
def tableToMultisetBdd (T : CTableBdd α β) : Multiset (ℕ × ℕ) :=
  ∑ v : ↥(univ.image α), ∑ b : ↥(univ.image β),
    Multiset.replicate (T v b) (v.val, b.val)

/-- Cast a bounded table up to a full `CTable` (always valid: `min + 1 ≤ k + 1`). -/
def ctableCastUp (T : CTableBdd α β) : CTable α β :=
  fun v b => ⟨(T v b : ℕ), by
    have hle : (T v b : ℕ) ≤
        min ((univ.filter (fun i => α i = v.val)).card)
            ((univ.filter (fun i => β i = b.val)).card) :=
      Nat.lt_succ_iff.mp (T v b).isLt
    have hk : (univ.filter (fun i => α i = v.val)).card ≤ k := by
      have := Finset.card_filter_le (univ : Finset (Fin k)) (fun i => α i = v.val)
      simpa using this
    exact Nat.lt_succ_of_le (le_trans (le_trans hle (min_le_left _ _)) hk)⟩

@[simp] lemma ctableCastUp_val (T : CTableBdd α β) (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    (ctableCastUp α β T v b : ℕ) = (T v b : ℕ) := rfl

/-- Cast a margin-correct full table down to the bounded type (entries fit by margin-correctness). -/
def ctableCastDown (T : CTable α β) (hT : T ∈ MarginCorrectTables α β) : CTableBdd α β :=
  fun v b => ⟨(T v b : ℕ), by
    rw [MarginCorrectTables, Finset.mem_filter] at hT
    obtain ⟨_, hrow, hcol⟩ := hT
    have h1 : (T v b : ℕ) ≤ (univ.filter (fun i => α i = v.val)).card := by
      rw [← hrow v]
      exact Finset.single_le_sum (f := fun b' => (T v b' : ℕ)) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have h2 : (T v b : ℕ) ≤ (univ.filter (fun i => β i = b.val)).card := by
      rw [← hcol b]
      exact Finset.single_le_sum (f := fun v' => (T v' b : ℕ)) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ v)
    exact Nat.lt_succ_of_le (le_min h1 h2)⟩

@[simp] lemma ctableCastDown_val (T : CTable α β) (hT : T ∈ MarginCorrectTables α β)
    (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    (ctableCastDown α β T hT v b : ℕ) = (T v b : ℕ) := rfl

/-- `ctableCastUp` of a bounded margin-correct table is margin-correct (values preserved). -/
lemma ctableCastUp_mem {T : CTableBdd α β} (hT : T ∈ MarginCorrectTablesBdd α β) :
    ctableCastUp α β T ∈ MarginCorrectTables α β := by
  rw [MarginCorrectTablesBdd, Finset.mem_filter] at hT
  obtain ⟨_, hrow, hcol⟩ := hT
  rw [MarginCorrectTables, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    fun v => by simpa only [ctableCastUp_val] using hrow v,
    fun b => by simpa only [ctableCastUp_val] using hcol b⟩

/-- `ctableCastDown` of a margin-correct table is margin-correct in the bounded type. -/
lemma ctableCastDown_mem {T : CTable α β} (hT : T ∈ MarginCorrectTables α β) :
    ctableCastDown α β T hT ∈ MarginCorrectTablesBdd α β := by
  rw [MarginCorrectTablesBdd, Finset.mem_filter]
  have hT' := hT
  rw [MarginCorrectTables, Finset.mem_filter] at hT'
  obtain ⟨_, hrow, hcol⟩ := hT'
  refine ⟨Finset.mem_univ _, fun v => ?_, fun b => ?_⟩
  · simp only [ctableCastDown_val]; exact hrow v
  · simp only [ctableCastDown_val]; exact hcol b

lemma ctableCastDown_castUp {T : CTableBdd α β} (hT : T ∈ MarginCorrectTablesBdd α β) :
    ctableCastDown α β (ctableCastUp α β T) (ctableCastUp_mem α β hT) = T := by
  funext v b; apply Fin.ext; rfl

lemma ctableCastUp_castDown {T : CTable α β} (hT : T ∈ MarginCorrectTables α β) :
    ctableCastUp α β (ctableCastDown α β T hT) = T := by
  funext v b; apply Fin.ext; rfl

/-- **Margin-bounded denominator Gram entry** — `gramDenEntry` over the tractable bounded
table type (`= gramDenEntry`, see `gramDenEntryBdd_eq`). This is what `native_decide` evaluates. -/
def gramDenEntryBdd {k : ℕ} (a b : MultiIndex k) : ℚ :=
  ((Nat.multinomial (univ : Finset ↥(univ.image b))
        (fun bb => (univ.filter (fun i => b i = bb.val)).card)) •
      ∑ T ∈ MarginCorrectTablesBdd a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => (T v bb : ℕ)) : ℚ))
          * jointWeightC (tableToMultisetBdd a b T))
    / ((k + a.degree + b.degree).factorial : ℚ)

/-- **Margin-bounded numerator Gram entry** (`= gramNumEntry`, see `gramNumEntryBdd_eq`). -/
def gramNumEntryBdd {n : ℕ} (a b : MultiIndex (n + 1)) : ℚ :=
  (∑ T ∈ MarginCorrectTablesBdd a b,
      (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => (T c.1 c.2 : ℕ)) : ℚ)
        * pairWeightC (tableToMultisetBdd a b T))
    / (((n + 1) + a.degree + b.degree + 1).factorial : ℚ)

lemma gramDenEntryBdd_eq {k : ℕ} (a b : MultiIndex k) :
    gramDenEntryBdd a b = gramDenEntry a b := by
  have hS : (∑ T ∈ MarginCorrectTablesBdd a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => (T v bb : ℕ)) : ℚ))
          * jointWeightC (tableToMultisetBdd a b T))
      = ∑ T ∈ MarginCorrectTables a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => (T v bb : ℕ)) : ℚ))
          * jointWeightC (tableToMultiset a b T) :=
    Finset.sum_bij' (i := fun T _ => ctableCastUp a b T)
      (j := fun T hT => ctableCastDown a b T hT)
      (fun T hT => ctableCastUp_mem a b hT)
      (fun T hT => ctableCastDown_mem a b hT)
      (fun T hT => ctableCastDown_castUp a b hT)
      (fun T hT => ctableCastUp_castDown a b hT)
      (fun T _ => rfl)
  unfold gramDenEntryBdd gramDenEntry
  rw [hS]

lemma gramNumEntryBdd_eq {n : ℕ} (a b : MultiIndex (n + 1)) :
    gramNumEntryBdd a b = gramNumEntry a b := by
  have hS : (∑ T ∈ MarginCorrectTablesBdd a b,
        (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
            (fun c => (T c.1 c.2 : ℕ)) : ℚ)
          * pairWeightC (tableToMultisetBdd a b T))
      = ∑ T ∈ MarginCorrectTables a b,
        (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
            (fun c => (T c.1 c.2 : ℕ)) : ℚ)
          * pairWeightC (tableToMultiset a b T) :=
    Finset.sum_bij' (i := fun T _ => ctableCastUp a b T)
      (j := fun T hT => ctableCastDown a b T hT)
      (fun T hT => ctableCastUp_mem a b hT)
      (fun T hT => ctableCastDown_mem a b hT)
      (fun T hT => ctableCastDown_castUp a b hT)
      (fun T hT => ctableCastUp_castDown a b hT)
      (fun T _ => rfl)
  unfold gramNumEntryBdd gramNumEntry
  rw [hS]

/-! ### Fréchet-windowed tables — the fully tractable enumeration

`MarginCorrectTablesBdd` still enumerates the dominant `0`-value cell over `0..min(margins) ≈ k`.
The Fréchet bound `T v b ≥ rowmargin + colmargin - k` (`marginCorrect_frechet`) caps that cell's
*free* range at `min - (row+col-k) = k - max(row,col) = #nonzero-positions ≤ 2·deg`. Re-typing each
entry to `Fin (cellHi - cellLo + 1)` (with `entryW = cellLo + raw`) makes the `0`-cell factor
`~2·deg` instead of `~k`, so the whole bounded enumeration is `(2·deg)^(cells)` — fully
`k`-independent. This is what makes a full `Mk k > 4` witness `native_decide` feasible. -/

/-- Fréchet upper window bound: `min(rowmargin v, colmargin b)`. -/
def cellHi (v : ↥(univ.image α)) (b : ↥(univ.image β)) : ℕ :=
  min ((univ.filter (fun i => α i = v.val)).card) ((univ.filter (fun i => β i = b.val)).card)

/-- Fréchet lower window bound: `rowmargin v + colmargin b - k` (truncated). -/
def cellLo (v : ↥(univ.image α)) (b : ↥(univ.image β)) : ℕ :=
  (univ.filter (fun i => α i = v.val)).card + (univ.filter (fun i => β i = b.val)).card - k

/-- Fréchet-windowed contingency table: entry `(v,b)` stored as an offset `raw ∈ Fin(width+1)`
into the window `[cellLo, cellHi]`. -/
abbrev CTableW : Type :=
  (v : ↥(univ.image α)) → (b : ↥(univ.image β)) → Fin (cellHi α β v b - cellLo α β v b + 1)

/-- The actual entry value of a windowed table: `cellLo + raw`. -/
def entryW (T : CTableW α β) (v : ↥(univ.image α)) (b : ↥(univ.image β)) : ℕ :=
  cellLo α β v b + (T v b).val

/-- Margin-correct windowed tables. -/
def MarginCorrectTablesW : Finset (CTableW α β) :=
  univ.filter (fun T =>
    (∀ v, ∑ b, entryW α β T v b = (univ.filter (fun i => α i = v.val)).card) ∧
    (∀ b, ∑ v, entryW α β T v b = (univ.filter (fun i => β i = b.val)).card))

/-- The joint multiset named by a windowed table (uses `entryW`). -/
def tableToMultisetW (T : CTableW α β) : Multiset (ℕ × ℕ) :=
  ∑ v : ↥(univ.image α), ∑ b : ↥(univ.image β),
    Multiset.replicate (entryW α β T v b) (v.val, b.val)

lemma cellHi_le_k (v : ↥(univ.image α)) (b : ↥(univ.image β)) : cellHi α β v b ≤ k := by
  simp only [cellHi]
  exact le_trans (min_le_left _ _)
    (by simpa using Finset.card_filter_le (univ : Finset (Fin k)) (fun i => α i = v.val))

/-- Cast a windowed table up to a full `CTable` (`entryW ≤ cellHi ≤ k`). -/
def ctableCastUpW (T : CTableW α β) : CTable α β :=
  fun v b => ⟨entryW α β T v b, by
    have hrk : (univ.filter (fun i => α i = v.val)).card ≤ k := by
      simpa using Finset.card_filter_le (univ : Finset (Fin k)) (fun i => α i = v.val)
    have hck : (univ.filter (fun i => β i = b.val)).card ≤ k := by
      simpa using Finset.card_filter_le (univ : Finset (Fin k)) (fun i => β i = b.val)
    have hraw : (T v b).val ≤ cellHi α β v b - cellLo α β v b := Nat.lt_succ_iff.mp (T v b).isLt
    simp only [entryW, cellHi, cellLo] at hraw ⊢
    omega⟩

@[simp] lemma ctableCastUpW_val (T : CTableW α β) (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    (ctableCastUpW α β T v b : ℕ) = entryW α β T v b := rfl

/-- Cast a margin-correct full table down to the windowed type (entries fit the Fréchet window). -/
def ctableCastDownW (T : CTable α β) (hT : T ∈ MarginCorrectTables α β) : CTableW α β :=
  fun v b => ⟨(T v b : ℕ) - cellLo α β v b, by
    have hub : (T v b : ℕ) ≤ cellHi α β v b := by
      have hmem := hT; rw [MarginCorrectTables, Finset.mem_filter] at hmem
      obtain ⟨_, hrow, hcol⟩ := hmem
      simp only [cellHi]
      refine le_min ?_ ?_
      · rw [← hrow v]
        exact Finset.single_le_sum (f := fun b' => (T v b' : ℕ)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      · rw [← hcol b]
        exact Finset.single_le_sum (f := fun v' => (T v' b : ℕ)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ v)
    omega⟩

/-- `entryW` of a downcast recovers the original entry (Fréchet: `cellLo ≤ T v b`). -/
lemma entryW_ctableCastDownW (T : CTable α β) (hT : T ∈ MarginCorrectTables α β)
    (v : ↥(univ.image α)) (b : ↥(univ.image β)) :
    entryW α β (ctableCastDownW α β T hT) v b = (T v b : ℕ) := by
  have hlo : cellLo α β v b ≤ (T v b : ℕ) := by
    have := marginCorrect_frechet α β T hT v b
    simp only [cellLo]; omega
  show cellLo α β v b + ((T v b : ℕ) - cellLo α β v b) = (T v b : ℕ)
  omega

lemma ctableCastUpW_mem {T : CTableW α β} (hT : T ∈ MarginCorrectTablesW α β) :
    ctableCastUpW α β T ∈ MarginCorrectTables α β := by
  rw [MarginCorrectTablesW, Finset.mem_filter] at hT
  obtain ⟨_, hrow, hcol⟩ := hT
  rw [MarginCorrectTables, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    fun v => by simpa only [ctableCastUpW_val] using hrow v,
    fun b => by simpa only [ctableCastUpW_val] using hcol b⟩

lemma ctableCastDownW_mem {T : CTable α β} (hT : T ∈ MarginCorrectTables α β) :
    ctableCastDownW α β T hT ∈ MarginCorrectTablesW α β := by
  rw [MarginCorrectTablesW, Finset.mem_filter]
  have hmem := hT; rw [MarginCorrectTables, Finset.mem_filter] at hmem
  obtain ⟨_, hrow, hcol⟩ := hmem
  refine ⟨Finset.mem_univ _, fun v => ?_, fun b => ?_⟩
  · rw [Finset.sum_congr rfl (fun b' _ => entryW_ctableCastDownW α β T hT v b')]; exact hrow v
  · rw [Finset.sum_congr rfl (fun v' _ => entryW_ctableCastDownW α β T hT v' b)]; exact hcol b

lemma ctableCastDownW_castUpW {T : CTableW α β} (hT : T ∈ MarginCorrectTablesW α β) :
    ctableCastDownW α β (ctableCastUpW α β T) (ctableCastUpW_mem α β hT) = T := by
  funext v b; apply Fin.ext
  show (ctableCastUpW α β T v b : ℕ) - cellLo α β v b = (T v b).val
  rw [ctableCastUpW_val]
  show cellLo α β v b + (T v b).val - cellLo α β v b = (T v b).val
  omega

lemma ctableCastUpW_castDownW {T : CTable α β} (hT : T ∈ MarginCorrectTables α β) :
    ctableCastUpW α β (ctableCastDownW α β T hT) = T := by
  funext v b; apply Fin.ext
  show entryW α β (ctableCastDownW α β T hT) v b = (T v b : ℕ)
  exact entryW_ctableCastDownW α β T hT v b

/-- **Fréchet-windowed denominator Gram entry** (`= gramDenEntry`, see `gramDenEntryW_eq`). The
`native_decide`-feasible form: enumerates `univ` over `CTableW` (card `∏ (window+1)`, `k`-independent). -/
def gramDenEntryW {k : ℕ} (a b : MultiIndex k) : ℚ :=
  ((Nat.multinomial (univ : Finset ↥(univ.image b))
        (fun bb => (univ.filter (fun i => b i = bb.val)).card)) •
      ∑ T ∈ MarginCorrectTablesW a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => entryW a b T v bb) : ℚ))
          * jointWeightC (tableToMultisetW a b T))
    / ((k + a.degree + b.degree).factorial : ℚ)

/-- **Fréchet-windowed numerator Gram entry** (`= gramNumEntry`, see `gramNumEntryW_eq`). -/
def gramNumEntryW {n : ℕ} (a b : MultiIndex (n + 1)) : ℚ :=
  (∑ T ∈ MarginCorrectTablesW a b,
      (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => entryW a b T c.1 c.2) : ℚ)
        * pairWeightC (tableToMultisetW a b T))
    / (((n + 1) + a.degree + b.degree + 1).factorial : ℚ)

lemma gramDenEntryW_eq {k : ℕ} (a b : MultiIndex k) :
    gramDenEntryW a b = gramDenEntry a b := by
  have hS : (∑ T ∈ MarginCorrectTablesW a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => entryW a b T v bb) : ℚ))
          * jointWeightC (tableToMultisetW a b T))
      = ∑ T ∈ MarginCorrectTables a b,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => (T v bb : ℕ)) : ℚ))
          * jointWeightC (tableToMultiset a b T) :=
    Finset.sum_bij' (i := fun T _ => ctableCastUpW a b T)
      (j := fun T hT => ctableCastDownW a b T hT)
      (fun T hT => ctableCastUpW_mem a b hT)
      (fun T hT => ctableCastDownW_mem a b hT)
      (fun T hT => ctableCastDownW_castUpW a b hT)
      (fun T hT => ctableCastUpW_castDownW a b hT)
      (fun T _ => rfl)
  unfold gramDenEntryW gramDenEntry
  rw [hS]

lemma gramNumEntryW_eq {n : ℕ} (a b : MultiIndex (n + 1)) :
    gramNumEntryW a b = gramNumEntry a b := by
  have hS : (∑ T ∈ MarginCorrectTablesW a b,
        (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
            (fun c => entryW a b T c.1 c.2) : ℚ)
          * pairWeightC (tableToMultisetW a b T))
      = ∑ T ∈ MarginCorrectTables a b,
        (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
            (fun c => (T c.1 c.2 : ℕ)) : ℚ)
          * pairWeightC (tableToMultiset a b T) :=
    Finset.sum_bij' (i := fun T _ => ctableCastUpW a b T)
      (j := fun T hT => ctableCastDownW a b T hT)
      (fun T hT => ctableCastUpW_mem a b hT)
      (fun T hT => ctableCastDownW_mem a b hT)
      (fun T hT => ctableCastDownW_castUpW a b hT)
      (fun T hT => ctableCastUpW_castDownW a b hT)
      (fun T _ => rfl)
  unfold gramNumEntryW gramNumEntry
  rw [hS]

/-! ### A.1: filter-card-hoisted windowed entries — the box-feasible `native_decide` shape

`gramDenEntryW`/`gramNumEntryW` recompute the value-fiber size
`(univ.filter (fun i => α i = v.val)).card` (an `O(k)` scan of `Fin k`) inside `entryW`'s
`cellLo` and the `MarginCorrectTablesW` margin filter — **per table**, in the hot enumeration
loop. For an img-4 orbit at `k = 300` that is `~10⁵` tables × `~10⁴` ops = `~10⁹` ops per
entry (empirically: a single img-4 `gramDenEntryW` does not finish in minutes, while an img-3
one — `~10³` tables — finishes in seconds).

The `WH` variants take the row/column margins as **explicit functions** `ra, rb : ℕ → ℕ`
(value → fiber size). The witness supplies them *materialized* (the histogram computed once and
captured in an `O(1)`-lookup closure — see `histArr` below), so every hot-loop access is `O(1)`
and no `Fin k` scan happens per table. The bridge lemmas (`gram*EntryWH_eq`) show that feeding
the *true* margins recovers `gram*EntryW` exactly, so soundness needs no new axiom — the margins
are the literal cards by construction. -/

/-- `entryW` with the margin cards passed as explicit functions (no `Fin k` scan):
`entryWH ra rb T v b = (ra v + rb b - k) + raw`. Equals `entryW` when `ra, rb` are the true
fiber sizes (`entryWH_eq_entryW`). -/
def entryWH (ra rb : ℕ → ℕ) (T : CTableW α β) (v : ↥(univ.image α)) (b : ↥(univ.image β)) : ℕ :=
  (ra v.val + rb b.val - k) + (T v b).val

/-- Margin-correct windowed tables with hoisted margins (filter uses `ra, rb`, not `Fin k` scans). -/
def MarginCorrectTablesWH (ra rb : ℕ → ℕ) : Finset (CTableW α β) :=
  univ.filter (fun T =>
    (∀ v, ∑ b, entryWH α β ra rb T v b = ra v.val) ∧
    (∀ b, ∑ v, entryWH α β ra rb T v b = rb b.val))

/-- The joint multiset named by a windowed table, using the hoisted `entryWH`. -/
def tableToMultisetWH (ra rb : ℕ → ℕ) (T : CTableW α β) : Multiset (ℕ × ℕ) :=
  ∑ v : ↥(univ.image α), ∑ b : ↥(univ.image β),
    Multiset.replicate (entryWH α β ra rb T v b) (v.val, b.val)

/-- **Filter-card-hoisted denominator Gram entry** (`= gramDenEntryW` when fed true margins,
see `gramDenEntryWH_eq`). This is the box-feasible `native_decide` shape: the witness supplies
`ra, rb` as `O(1)`-lookup closures, so the table enumeration never scans `Fin k`. -/
def gramDenEntryWH {k : ℕ} (a b : MultiIndex k) (ra rb : ℕ → ℕ) : ℚ :=
  ((Nat.multinomial (univ : Finset ↥(univ.image b)) (fun bb => rb bb.val)) •
      ∑ T ∈ MarginCorrectTablesWH a b ra rb,
        (∏ bb : ↥(univ.image b), (Nat.multinomial univ
            (fun v : ↥(univ.image a) => entryWH a b ra rb T v bb) : ℚ))
          * jointWeightC (tableToMultisetWH a b ra rb T))
    / ((k + a.degree + b.degree).factorial : ℚ)

/-- **Filter-card-hoisted numerator Gram entry** (`= gramNumEntryW`, see `gramNumEntryWH_eq`). -/
def gramNumEntryWH {n : ℕ} (a b : MultiIndex (n + 1)) (ra rb : ℕ → ℕ) : ℚ :=
  (∑ T ∈ MarginCorrectTablesWH a b ra rb,
      (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => entryWH a b ra rb T c.1 c.2) : ℚ)
        * pairWeightC (tableToMultisetWH a b ra rb T))
    / (((n + 1) + a.degree + b.degree + 1).factorial : ℚ)

/-- The materialized histogram of `a` as an `O(1)`-lookup function: `histArr D a v` reads the
`v`-th entry of the precomputed array `[card(a=0), …, card(a=D)]`. The array is built once
(per use site) by `k` scans; thereafter every `histArr D a v` is an array index, so threading
`histArr D a` into `gram*EntryWH` keeps the table loop `Fin k`-scan-free. Agrees with the true
fiber size for every value `≤ D` (`histArr_eq`); the witness uses `D = ` max degree. -/
def histArr (D : ℕ) (a : MultiIndex k) : ℕ → ℕ :=
  let arr := (List.range (D + 1)).map (fun w => (univ.filter (fun i => a i = w)).card)
  fun v => arr.getD v 0

lemma histArr_eq (D : ℕ) (a : MultiIndex k) {v : ℕ} (hv : v ≤ D) :
    histArr D a v = (univ.filter (fun i => a i = v)).card := by
  show ((List.range (D + 1)).map (fun w => (univ.filter (fun i => a i = w)).card)).getD v 0
      = (univ.filter (fun i => a i = v)).card
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hv)]
  rfl

/-- The pointwise equality `entryWH = entryW` under the margin-agreement hypotheses; shared by
both bridge lemmas. -/
lemma entryWH_eq_entryW {k : ℕ} (a b : MultiIndex k) (ra rb : ℕ → ℕ)
    (ha : ∀ v ∈ univ.image a, ra v = (univ.filter (fun i => a i = v)).card)
    (hb : ∀ w ∈ univ.image b, rb w = (univ.filter (fun i => b i = w)).card)
    (T : CTableW a b) (v : ↥(univ.image a)) (w : ↥(univ.image b)) :
    entryWH a b ra rb T v w = entryW a b T v w := by
  unfold entryWH entryW cellLo
  rw [ha v.val v.property, hb w.val w.property]

/-- The margin-correct table sets coincide under the agreement hypotheses; shared. -/
lemma marginCorrectTablesWH_eq {k : ℕ} (a b : MultiIndex k) (ra rb : ℕ → ℕ)
    (ha : ∀ v ∈ univ.image a, ra v = (univ.filter (fun i => a i = v)).card)
    (hb : ∀ w ∈ univ.image b, rb w = (univ.filter (fun i => b i = w)).card) :
    MarginCorrectTablesWH a b ra rb = MarginCorrectTablesW a b := by
  have hentry := entryWH_eq_entryW a b ra rb ha hb
  unfold MarginCorrectTablesWH MarginCorrectTablesW
  apply Finset.filter_congr
  intro T _
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · constructor
    · intro h
      calc (∑ w, entryW a b T v w) = ∑ w, entryWH a b ra rb T v w :=
            Finset.sum_congr rfl (fun w _ => (hentry T v w).symm)
        _ = ra v.val := h
        _ = _ := ha v.val v.property
    · intro h
      calc (∑ w, entryWH a b ra rb T v w) = ∑ w, entryW a b T v w :=
            Finset.sum_congr rfl (fun w _ => hentry T v w)
        _ = (univ.filter (fun i => a i = v.val)).card := h
        _ = ra v.val := (ha v.val v.property).symm
  · constructor
    · intro h
      calc (∑ v, entryW a b T v w) = ∑ v, entryWH a b ra rb T v w :=
            Finset.sum_congr rfl (fun v _ => (hentry T v w).symm)
        _ = rb w.val := h
        _ = _ := hb w.val w.property
    · intro h
      calc (∑ v, entryWH a b ra rb T v w) = ∑ v, entryW a b T v w :=
            Finset.sum_congr rfl (fun v _ => hentry T v w)
        _ = (univ.filter (fun i => b i = w.val)).card := h
        _ = rb w.val := (hb w.val w.property).symm

/-- The joint multisets coincide under the agreement hypotheses; shared. -/
lemma tableToMultisetWH_eq {k : ℕ} (a b : MultiIndex k) (ra rb : ℕ → ℕ)
    (ha : ∀ v ∈ univ.image a, ra v = (univ.filter (fun i => a i = v)).card)
    (hb : ∀ w ∈ univ.image b, rb w = (univ.filter (fun i => b i = w)).card)
    (T : CTableW a b) :
    tableToMultisetWH a b ra rb T = tableToMultisetW a b T := by
  have hentry := entryWH_eq_entryW a b ra rb ha hb
  unfold tableToMultisetWH tableToMultisetW
  exact Finset.sum_congr rfl (fun v _ =>
    Finset.sum_congr rfl (fun w _ => by rw [hentry T v w]))

/-- **Bridge: hoisted denominator entry = windowed denominator entry**, given that `ra, rb` agree
with the true fiber sizes on the value sets of `a, b`. The whole point: with this, the witness
evaluates `gramDenEntryWH a b (litRa) (litRb)` (fast) and discharges the agreement separately. -/
lemma gramDenEntryWH_eq {k : ℕ} (a b : MultiIndex k) (ra rb : ℕ → ℕ)
    (ha : ∀ v ∈ univ.image a, ra v = (univ.filter (fun i => a i = v)).card)
    (hb : ∀ w ∈ univ.image b, rb w = (univ.filter (fun i => b i = w)).card) :
    gramDenEntryWH a b ra rb = gramDenEntryW a b := by
  have hentry := entryWH_eq_entryW a b ra rb ha hb
  have hMfun : (fun bb : ↥(univ.image b) => rb bb.val)
             = (fun bb : ↥(univ.image b) => (univ.filter (fun i => b i = bb.val)).card) :=
    funext (fun bb => hb bb.val bb.property)
  have hM : Nat.multinomial (univ : Finset ↥(univ.image b)) (fun bb => rb bb.val)
          = Nat.multinomial (univ : Finset ↥(univ.image b))
              (fun bb => (univ.filter (fun i => b i = bb.val)).card) :=
    congrArg (Nat.multinomial univ) hMfun
  have hsummand : ∀ T : CTableW a b,
      (∏ bb : ↥(univ.image b), (Nat.multinomial univ
          (fun v : ↥(univ.image a) => entryWH a b ra rb T v bb) : ℚ))
        * jointWeightC (tableToMultisetWH a b ra rb T)
      = (∏ bb : ↥(univ.image b), (Nat.multinomial univ
          (fun v : ↥(univ.image a) => entryW a b T v bb) : ℚ))
        * jointWeightC (tableToMultisetW a b T) := by
    intro T
    congr 1
    · refine Finset.prod_congr rfl (fun bb _ => ?_)
      have hf : (fun v : ↥(univ.image a) => entryWH a b ra rb T v bb)
              = (fun v : ↥(univ.image a) => entryW a b T v bb) := funext (fun v => hentry T v bb)
      rw [hf]
    · rw [tableToMultisetWH_eq a b ra rb ha hb T]
  unfold gramDenEntryWH gramDenEntryW
  rw [marginCorrectTablesWH_eq a b ra rb ha hb, hM,
    Finset.sum_congr rfl (fun T _ => hsummand T)]

/-- **Bridge: hoisted numerator entry = windowed numerator entry** (numerator analog of
`gramDenEntryWH_eq`). -/
lemma gramNumEntryWH_eq {n : ℕ} (a b : MultiIndex (n + 1)) (ra rb : ℕ → ℕ)
    (ha : ∀ v ∈ univ.image a, ra v = (univ.filter (fun i => a i = v)).card)
    (hb : ∀ w ∈ univ.image b, rb w = (univ.filter (fun i => b i = w)).card) :
    gramNumEntryWH a b ra rb = gramNumEntryW a b := by
  have hentry := entryWH_eq_entryW a b ra rb ha hb
  have hsummand : ∀ T : CTableW a b,
      (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => entryWH a b ra rb T c.1 c.2) : ℚ)
        * pairWeightC (tableToMultisetWH a b ra rb T)
      = (Nat.multinomial (univ : Finset (↥(univ.image a) × ↥(univ.image b)))
          (fun c => entryW a b T c.1 c.2) : ℚ)
        * pairWeightC (tableToMultisetW a b T) := by
    intro T
    congr 1
    · have hf : (fun c : ↥(univ.image a) × ↥(univ.image b) => entryWH a b ra rb T c.1 c.2)
              = (fun c => entryW a b T c.1 c.2) := funext (fun c => hentry T c.1 c.2)
      rw [hf]
    · rw [tableToMultisetWH_eq a b ra rb ha hb T]
  unfold gramNumEntryWH gramNumEntryW
  rw [marginCorrectTablesWH_eq a b ra rb ha hb,
    Finset.sum_congr rfl (fun T _ => hsummand T)]

/-- **Computable-form symmetric-weight `Mk` lower bound.** `Mk_gt_of_symWeight_witness` restated
with the computable `gram*Entry` matrices, so `hwit` is a `native_decide`-able rational inequality.
This is the witness shape the endgame actually feeds. -/
theorem Mk_gt_of_symWeight_witness_computable {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntry a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntry a b)) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  apply Mk_gt_of_symWeight_witness R c hR T
  simp only [gramNumEntry_eq, gramDenEntry_eq]
  exact hwit

/-- **Fully `native_decide`-ready discharge of `mk_54_witness_under_EH`.** Given `k=54` orbit reps
`R`, coeffs `c`, the (decidable) disjointness `hR`, and a `native_decide`-able rational inequality
on the computable Gram matrices, produces exactly `mk_54_witness_under_EH`. Endgame invocation:
`mk_54_witness_under_EH_of_symWeight_computable R c (disjoint_of_histogram R (by native_decide))
(by native_decide)`. -/
theorem mk_54_witness_under_EH_of_symWeight_computable (R : Finset (MultiIndex (53 + 1)))
    (c : MultiIndex (53 + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (4 : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntry a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntry a b)) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 54 > 2 * 2 / ϑ :=
  exists_theta_of_Mk_gt_four (Mk_gt_of_symWeight_witness_computable R c hR 4 hwit)

/-- **Uniform `native_decide`-ready discharge of any `2·m/ϑ` EH witness.** For any `m ≥ 1`, a
symmetric weight whose computable Gram quotient exceeds `2·m` certifies the Polymath8b EH-witness
shape `∃ ϑ∈(0,1), Mk (n+1) > 2·m/ϑ`. Instantiates to `mk_54` (`m=2`), `mk_5511` (`m=3`),
`mk_41588` (`m=4`), `mk_309661` (`m=5`) — each via `… R c (disjoint_of_histogram R (by
native_decide)) (by native_decide)` plus a `norm_num` to match the literal `2*m`. -/
theorem mk_witness_under_EH_of_symWeight_computable {n m : ℕ} (hm : 0 < m)
    (R : Finset (MultiIndex (n + 1))) (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (2 * m : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntry a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntry a b)) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk (n + 1) > 2 * (m : ℝ) / ϑ :=
  exists_theta_of_Mk_gt (2 * (m : ℝ)) (by positivity)
    (by exact_mod_cast Mk_gt_of_symWeight_witness_computable R c hR (2 * m) hwit)

/-- **Margin-bounded `Mk` lower bound** — `Mk_gt_of_symWeight_witness_computable` restated with the
tractable `gram*EntryBdd` matrices. The `hwit` inequality is the one `native_decide` actually
evaluates: it enumerates the bounded `univ` (card `∏ (min+1)`), not `(k+1)^(cells)`. -/
theorem Mk_gt_of_symWeight_witness_bdd {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryBdd a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryBdd a b)) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  apply Mk_gt_of_symWeight_witness_computable R c hR T
  simp only [gramNumEntryBdd_eq, gramDenEntryBdd_eq] at hwit
  exact hwit

/-- **Margin-bounded `2·m/ϑ` EH-witness discharge** — the `native_decide`-feasible form of
`mk_witness_under_EH_of_symWeight_computable`. The bounded Gram matrices make the `hwit`
`native_decide` tractable (no `(k+1)^(cells)` table enumeration). -/
theorem mk_witness_under_EH_of_symWeight_bdd {n m : ℕ} (hm : 0 < m)
    (R : Finset (MultiIndex (n + 1))) (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (2 * m : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryBdd a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryBdd a b)) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk (n + 1) > 2 * (m : ℝ) / ϑ :=
  exists_theta_of_Mk_gt (2 * (m : ℝ)) (by positivity)
    (by exact_mod_cast Mk_gt_of_symWeight_witness_bdd R c hR (2 * m) hwit)

/-- **Fréchet-windowed `Mk` lower bound** — the fully `k`-independent-enumeration witness shape.
`hwit` is evaluated by `native_decide` over `gram*EntryW`, whose tables enumerate
`∏(window+1)` (no `~k` factor on the `0`-cell). This is the shape a full `Mk k > 4` discharge feeds. -/
theorem Mk_gt_of_symWeight_witness_W {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryW a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryW a b)) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  apply Mk_gt_of_symWeight_witness_computable R c hR T
  simp only [gramNumEntryW_eq, gramDenEntryW_eq] at hwit
  exact hwit

/-- **Fréchet-windowed `2·m/ϑ` EH-witness discharge** — the most tractable `native_decide` shape. -/
theorem mk_witness_under_EH_of_symWeight_W {n m : ℕ} (hm : 0 < m)
    (R : Finset (MultiIndex (n + 1))) (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (hwit : (2 * m : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryW a b)
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryW a b)) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk (n + 1) > 2 * (m : ℝ) / ϑ :=
  exists_theta_of_Mk_gt (2 * (m : ℝ)) (by positivity)
    (by exact_mod_cast Mk_gt_of_symWeight_witness_W R c hR (2 * m) hwit)

/-- **Filter-card-hoisted `Mk` lower bound — the box-feasible witness shape.** Identical to
`Mk_gt_of_symWeight_witness_W`, but each Gram entry is evaluated with margins supplied by a
per-rep histogram function `m : MultiIndex (n+1) → ℕ → ℕ` (so `native_decide` never scans
`Fin k` inside the table enumeration). The agreement `hm` — that `m a` reproduces `a`'s value-
fiber sizes — is discharged once per rep by `decide`/`native_decide` (outside the hot loop), and
`gram*EntryWH_eq` then shows the hoisted entries equal the windowed ones. -/
theorem Mk_gt_of_symWeight_witness_WH {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (m : MultiIndex (n + 1) → ℕ → ℕ)
    (hm : ∀ a ∈ R, ∀ v ∈ univ.image a, m a v = (univ.filter (fun i => a i = v)).card)
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryWH a b (m a) (m b))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryWH a b (m a) (m b))) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  apply Mk_gt_of_symWeight_witness_W R c hR T
  have hnum : (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryWH a b (m a) (m b))
            = (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryW a b) :=
    Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => by
      rw [gramNumEntryWH_eq a b (m a) (m b) (hm a ha) (hm b hb)]))
  have hden : (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryWH a b (m a) (m b))
            = (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryW a b) :=
    Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => by
      rw [gramDenEntryWH_eq a b (m a) (m b) (hm a ha) (hm b hb)]))
  rw [hnum, hden] at hwit
  exact hwit

/-- **Filter-card-hoisted `2·m/ϑ` EH-witness discharge** — the box-feasible analog of
`mk_witness_under_EH_of_symWeight_W`. -/
theorem mk_witness_under_EH_of_symWeight_WH {n mm : ℕ} (hmm : 0 < mm)
    (R : Finset (MultiIndex (n + 1))) (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (m : MultiIndex (n + 1) → ℕ → ℕ)
    (hm : ∀ a ∈ R, ∀ v ∈ univ.image a, m a v = (univ.filter (fun i => a i = v)).card)
    (hwit : (2 * mm : ℚ) <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntryWH a b (m a) (m b))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryWH a b (m a) (m b))) :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk (n + 1) > 2 * (mm : ℝ) / ϑ :=
  exists_theta_of_Mk_gt (2 * (mm : ℝ)) (by positivity)
    (by exact_mod_cast Mk_gt_of_symWeight_witness_WH R c hR m hm (2 * mm) hwit)

/-- **Canonical witness encoding.** A descending parts list `L` as a padded `MultiIndex k`
(zeros beyond `L`). The orbit representatives of an `Mk k > 4` witness are `ofParts` of the
degree-≤`D` partitions; `Mk_gt_of_symWeight_witness_W {ofParts Lᵢ} c …` is the discharge shape.
Foundation for the A.1 filter-card hoist (`PENDING_WORK.md`): the value-histogram of `ofParts L`
is read off `L` (count of `v` in `L`, or `k - L.length` at `v = 0`) with no `Fin k` scan. -/
def ofParts {k : ℕ} (L : List ℕ) : MultiIndex k := fun i => L.getD i.val 0

/-- **`ofParts` is injective on positive-parts lists** (length ≤ k). Distinct partition-lists give
distinct multi-indices — so the witness reps `Ls.map ofParts` are `Nodup` when `Ls` is, the
foundation for re-keying the witness on parts-lists (`PENDING_WORK.md §A`). -/
lemma ofParts_inj {k : ℕ} {La Lb : List ℕ} (hA : La.length ≤ k) (hB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x)
    (h : (ofParts La : MultiIndex k) = ofParts Lb) : La = Lb := by
  have hpt : ∀ i : ℕ, i < k → La.getD i 0 = Lb.getD i 0 := fun i hi => congrFun h ⟨i, hi⟩
  have hlen : La.length = Lb.length := by
    rcases lt_trichotomy La.length Lb.length with hlt | heq | hgt
    · exfalso
      have hk : La.length < k := lt_of_lt_of_le hlt hB
      have hpos : 0 < Lb.getD La.length 0 := by
        rw [List.getD_eq_getElem Lb 0 hlt]; exact hposB _ (List.getElem_mem _)
      rw [← hpt La.length hk, List.getD_eq_default La 0 (le_refl _)] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact heq
    · exfalso
      have hk : Lb.length < k := lt_of_lt_of_le hgt hA
      have hpos : 0 < La.getD Lb.length 0 := by
        rw [List.getD_eq_getElem La 0 hgt]; exact hposA _ (List.getElem_mem _)
      rw [hpt Lb.length hk, List.getD_eq_default Lb 0 (le_refl _)] at hpos
      exact absurd hpos (lt_irrefl 0)
  apply List.ext_getElem hlen
  intro i h1 h2
  have := hpt i (lt_of_lt_of_le h1 hA)
  rwa [List.getD_eq_getElem La 0 h1, List.getD_eq_getElem Lb 0 h2] at this

/-- **Value-histogram of `ofParts L`, closed form** (Aristotle-proved, job `656d6b54`). Among the
`k` slots, value `v` occurs `L.count v` times within the list, plus — only at `v = 0` — once per
`k - L.length` padding slot. This is the key to a *fully `k`-independent* margin: no `Fin k` scan. -/
theorem card_filter_ofParts (k : ℕ) (L : List ℕ) (hL : L.length ≤ k) (v : ℕ) :
    (univ.filter (fun i : Fin k => L.getD i.val 0 = v)).card
      = L.count v + (if v = 0 then k - L.length else 0) := by
  induction k generalizing L with
  | zero => simp_all [Nat.le_zero, List.length_eq_zero_iff]
  | succ k ih =>
    cases L with
    | nil =>
      simp only [List.getD_nil, List.count_nil, List.length_nil, Nat.sub_zero, Finset.card_filter]
      by_cases hv : v = 0 <;> simp [hv, eq_comm]
    | cons x L =>
      rw [Finset.card_filter, Fin.sum_univ_succ]
      have hL' : L.length ≤ k := by simpa using hL
      have key : (∑ j : Fin k, if (x :: L).getD (Fin.succ j).val 0 = v then 1 else 0)
               = (univ.filter (fun j : Fin k => L.getD j.val 0 = v)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun j _ => by simp [List.getD_cons_succ])
      rw [key, ih L hL']
      simp only [Fin.val_zero, List.getD_cons_zero, List.count_cons, List.length_cons, beq_iff_eq]
      split_ifs <;> omega

/-- The `k`-independent value-histogram of `ofParts L`: `L.count v` plus `k - L.length` padding
zeros at `v = 0`. Computed from `L` alone (`O(|L|)`, no `Fin k` scan) — the materialized margin
the box-feasible witness threads into `gram*EntryWH`. Agrees with the true fiber size
(`partsHist_eq`, via `card_filter_ofParts`). -/
def partsHist (k : ℕ) (L : List ℕ) : ℕ → ℕ :=
  fun v => L.count v + (if v = 0 then k - L.length else 0)

@[simp] lemma partsHist_eq {k : ℕ} (L : List ℕ) (hL : L.length ≤ k) (v : ℕ) :
    partsHist k L v = (univ.filter (fun i : Fin k => (ofParts L) i = v)).card := by
  show partsHist k L v = (univ.filter (fun i : Fin k => L.getD i.val 0 = v)).card
  rw [card_filter_ofParts k L hL v]; rfl

/-! ## A.2: the matchings closed form — the box-feasible Gram entries

Empirically (lap 2026-06-03), the windowed enumeration is `native_decide`-infeasible for img-4
orbits: even with the `Fin k` scan hoisted (`partsHist`), an img-4 orbit gives `~131072` windowed
tables *per entry* (k-independent), so the full 45-orbit witness is hours/OOM. The fix is to
REPLACE the table enumeration by the **matchings closed form** (`tools/mk/mk_sym.py`, validated vs
brute force and vs the Lean spot-checks `11/3360`, `7/2160`):

  `gramDenEntry (ofParts La) (ofParts Lb) = matchDenForm La Lb k`,
  `gramNumEntry (ofParts La) (ofParts Lb) = matchNumForm La Lb k`,

a sum over the (k-INDEPENDENT, `~34`-term) partial matchings of the nonzero parts, with
`Nat.descFactorial` (a ≤`2·deg`-term product, no factorial) in place of the falling factorial and
ONE `(k+|La|+|Lb|)!` per entry. These `#eval`/`native_decide` **instantly** even at `k=300` img-4.

`matchData La Lb`: for every partial matching of `La`-parts to `Lb`-parts, the pair
`(numPairs, W)` with `W = ∏ paired (a+b)! · ∏ unmatched a! · ∏ unmatched b!`. The recursion sends
each `La` head to *unmatched* (`×a!`) or *matched* to a current `Lb` entry (erase it, `×(a+b)!`,
`numPairs+1`) — a bijective enumeration of partial matchings. -/
def matchData : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod)]
  | (a :: La), Lb =>
      (matchData La Lb).map (fun pw => (pw.1, a.factorial * pw.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchData La (Lb.eraseIdx jb.1)).map (fun pw => (pw.1 + 1, (a + jb.2).factorial * pw.2)))

/-- `Sden = ∑_M ff(k,T_M)·W(M)`, with `T_M = |La|+|Lb|-numPairs` and `ff(k,T) = k.descFactorial T`. -/
def matchDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ((matchData La Lb).map
    (fun pw => k.descFactorial (La.length + Lb.length - pw.1) * pw.2)).sum

/-- `aut L = ∏_v (multiplicity of value v in L)!`. -/
def autParts (L : List ℕ) : ℕ := (L.dedup.map (fun v => (L.count v).factorial)).prod

/-- **Matchings closed form, denominator Gram entry** (`= gramDenEntry (ofParts La) (ofParts Lb)`,
see `gramDenEntry_eq_matchDenForm`). `native_decide`-instant: no table enumeration. -/
def matchDenForm (La Lb : List ℕ) (k : ℕ) : ℚ :=
  (matchDenSum La Lb k : ℚ) / (autParts La * autParts Lb * (k + La.sum + Lb.sum).factorial : ℚ)

/-- `g(a,b) = (a+b+2)!/((a+1)(b+1)(a+b)!)`; `g(0,0)=2`. The numerator's per-token weight. -/
def gWeight (a b : ℕ) : ℚ := ((a + b + 2).factorial : ℚ) / ((a + 1) * (b + 1) * (a + b).factorial : ℚ)

/-- Per matching, `(numPairs, W, Gocc)` where `Gocc = ∑ over occupied tokens of g(content)`
(paired → `g(a,b)`, `La`-solo → `g(a,0)`, `Lb`-solo → `g(0,b)`). -/
def matchDataN : List ℕ → List ℕ → List (ℕ × ℕ × ℚ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod, (Lb.map (fun b => gWeight 0 b)).sum)]
  | (a :: La), Lb =>
      (matchDataN La Lb).map (fun t => (t.1, a.factorial * t.2.1, gWeight a 0 + t.2.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchDataN La (Lb.eraseIdx jb.1)).map
            (fun t => (t.1 + 1, (a + jb.2).factorial * t.2.1, gWeight a jb.2 + t.2.2)))

/-- `Snum = ∑_M ff(k,T)·W·(Gocc + (k-T)·g(0,0))`, `g(0,0)=2`. -/
def matchNumSum (La Lb : List ℕ) (k : ℕ) : ℚ :=
  ((matchDataN La Lb).map (fun t =>
    let T := La.length + Lb.length - t.1
    (k.descFactorial T : ℚ) * t.2.1 * (t.2.2 + (k - T : ℕ) * gWeight 0 0))).sum

/-- **Matchings closed form, numerator Gram entry** (`= gramNumEntry (ofParts La) (ofParts Lb)`,
see `gramNumEntry_eq_matchNumForm`). -/
def matchNumForm (La Lb : List ℕ) (k : ℕ) : ℚ :=
  matchNumSum La Lb k / (autParts La * autParts Lb * (k + La.sum + Lb.sum + 1).factorial : ℚ)

/-- **Bridge (DENOMINATOR): the table-sum Gram entry equals the matchings closed form.** This is
the genuine combinatorial identity (contingency-table sum = partial-matchings sum, the
permanent/rook expansion of `∑_{p∈orbit a}∑_{q∈orbit b} ∏ᵢ(pᵢ+qᵢ)!` grouped by overlap pattern).
NUMERICALLY VALIDATED: `matchDenForm [2,1] [1,1] 3 = 11/3360 = gramDenEntry ![2,1,0] ![1,1,0]`,
and against `tools/mk/mk_sym.py reduced_closed` across `k`. Disclosed `axiom` pending the formal
proof (the open A.2 theorem; see `PENDING_WORK.md §A`). `La, Lb` are the nonzero parts (positive,
length ≤ k). -/
axiom gramDenEntry_eq_matchDenForm {k : ℕ} (La Lb : List ℕ)
    (hLa : La.length ≤ k) (hLb : Lb.length ≤ k)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x) :
    gramDenEntry (ofParts La : MultiIndex k) (ofParts Lb) = matchDenForm La Lb k

/-- **Bridge (NUMERATOR): the table-sum numerator equals the matchings closed form.** Numerator
analog of `gramDenEntry_eq_matchDenForm` (with the per-token `g` weights and the `(k-T)·g(0,0)`
empty-slot term). NUMERICALLY VALIDATED: `matchNumForm [2,1] [1,1] 3 = 7/2160 =
gramNumEntry ![2,1,0] ![1,1,0]`. Disclosed `axiom` pending the A.2 proof. -/
axiom gramNumEntry_eq_matchNumForm {n : ℕ} (La Lb : List ℕ)
    (hLa : La.length ≤ n + 1) (hLb : Lb.length ≤ n + 1)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x) :
    gramNumEntry (ofParts La : MultiIndex (n + 1)) (ofParts Lb) = matchNumForm La Lb (n + 1)

/-- **Matchings-form `Mk` lower bound — the box-feasible witness shape.** Each Gram entry is the
`native_decide`-instant matchings closed form (no `~131072`-table enumeration). The reps are
`ofParts (P a)` for parts-lists `P a` (positive, length ≤ `n+1`), supplied so the matchings forms
can be evaluated directly. Rests on the two bridge axioms (A.2). -/
theorem Mk_gt_of_symWeight_witness_match {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b))
    (P : MultiIndex (n + 1) → List ℕ)
    (hP : ∀ a ∈ R, a = ofParts (P a) ∧ (∀ x ∈ P a, 0 < x) ∧ (P a).length ≤ n + 1)
    (T : ℚ)
    (hwit : T <
      (∑ a ∈ R, ∑ b ∈ R, c a * c b * matchNumForm (P a) (P b) (n + 1))
        / (∑ a ∈ R, ∑ b ∈ R, c a * c b * matchDenForm (P a) (P b) (n + 1))) :
    (T : ℝ) < Sieve.Mk (n + 1) := by
  apply Mk_gt_of_symWeight_witness_computable R c hR T
  have hnum : (∑ a ∈ R, ∑ b ∈ R, c a * c b * matchNumForm (P a) (P b) (n + 1))
            = (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramNumEntry a b) :=
    Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => by
      obtain ⟨hPa, hposa, hlena⟩ := hP a ha
      obtain ⟨hPb, hposb, hlenb⟩ := hP b hb
      rw [← gramNumEntry_eq_matchNumForm (P a) (P b) hlena hlenb hposa hposb, ← hPa, ← hPb]))
  have hden : (∑ a ∈ R, ∑ b ∈ R, c a * c b * matchDenForm (P a) (P b) (n + 1))
            = (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntry a b) :=
    Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => by
      obtain ⟨hPa, hposa, hlena⟩ := hP a ha
      obtain ⟨hPb, hposb, hlenb⟩ := hP b hb
      rw [← gramDenEntry_eq_matchDenForm (P a) (P b) hlena hlenb hposa hposb, ← hPa, ← hPb]))
  rw [hnum, hden] at hwit
  exact hwit

/-! ## End-to-end validation (regression guard)

A non-vacuous use of the whole pipeline at `k = 3`: the symmetric weight on
`R = {![2,1,0], ![1,1,0]}` with unit coefficients has Gram quotient `2063/2060 > 1`, certifying
`Mk 3 > 1`. **Both** the disjointness `hR` and the rational Gram inequality are discharged by
`native_decide` — exactly the two `native_decide`s the `k=54` endgame needs, just with larger
data. This confirms the orbit-symmetry → Gram → `Mk` chain is sound and the `native_decide`s
fire. (`Mk 3 > 1` is itself a weak bound; the point is the mechanism.) -/
example : (1 : ℝ) < Sieve.Mk 3 := by
  have h := Mk_gt_of_symWeight_witness_computable (n := 2)
    ({![2, 1, 0], ![1, 1, 0]} : Finset (MultiIndex 3)) (fun _ => 1)
    (disjoint_of_histogram _ (by native_decide)) 1 (by native_decide)
  exact_mod_cast h

/-- **Same bound through the margin-bounded path.** Identical witness, but the Gram quotient
`native_decide` now runs over `gram*EntryBdd` — enumerating the bounded table `univ` (card
`∏ (min+1)`) instead of `(k+1)^(cells)`. This is the `native_decide` shape that actually scales:
e.g. `gramDenEntryBdd (![2,1] padded) (![2,1] padded)` at `k = 50` evaluates in seconds, whereas
the unbounded `gramDenEntry` (over `(51)⁹ ≈ 10¹⁵` tables) does not finish. -/
example : (1 : ℝ) < Sieve.Mk 3 := by
  have h := Mk_gt_of_symWeight_witness_bdd (n := 2)
    ({![2, 1, 0], ![1, 1, 0]} : Finset (MultiIndex 3)) (fun _ => 1)
    (disjoint_of_histogram _ (by native_decide)) 1 (by native_decide)
  exact_mod_cast h

/-- **Same bound through the Fréchet-windowed path.** Identical witness, but the Gram quotient
`native_decide` runs over `gram*EntryW` — the table `univ` here has the `0`-cell range Fréchet-capped
(`cellHi - cellLo + 1`), giving a fully `k`-independent enumeration. This is the shape that scales
to a real `Mk k > 4` witness at large `k`. -/
example : (1 : ℝ) < Sieve.Mk 3 := by
  have h := Mk_gt_of_symWeight_witness_W (n := 2)
    ({![2, 1, 0], ![1, 1, 0]} : Finset (MultiIndex 3)) (fun _ => 1)
    (disjoint_of_histogram _ (by native_decide)) 1 (by native_decide)
  exact_mod_cast h

/-- **Same bound through the filter-card-hoisted path (A.1).** Identical witness, but each Gram
entry is evaluated with margins supplied by `histArr 2` (the value-histogram materialized as an
`O(1)`-lookup array), so the `native_decide` never scans `Fin k` inside the table enumeration.
The agreement `hm` (`histArr 2 a` reproduces `a`'s fiber sizes) is itself a `native_decide`. This
is the box-feasible shape that makes a full `Mk k > 4` witness at large `k` tractable — without it
an img-4 orbit at `k = 300` (`~10⁵` tables × per-table `Fin k` scan) does not finish in minutes. -/
example : (1 : ℝ) < Sieve.Mk 3 := by
  have h := Mk_gt_of_symWeight_witness_WH (n := 2)
    ({![2, 1, 0], ![1, 1, 0]} : Finset (MultiIndex 3)) (fun _ => 1)
    (disjoint_of_histogram _ (by native_decide))
    (fun a => histArr 2 a) (by native_decide) 1 (by native_decide)
  exact_mod_cast h

/-- **Same bound through the matchings closed form (A.2).** Identical witness, but each Gram entry
is the `native_decide`-instant `matchNumForm`/`matchDenForm` — NO table enumeration at all. This is
the only box-feasible shape for the real `Mk k > 4` witness, since img-4 orbits make the windowed
enumeration (`~131072` tables/entry) intractable. Rests on the two bridge axioms
`gram*Entry_eq_match*Form` (numerically validated; the A.2 combinatorial identity is the open
target). The reps `![2,1,0], ![1,1,0]` are `ofParts [2,1]`, `ofParts [1,1]`. -/
example : (1 : ℝ) < Sieve.Mk 3 := by
  have h := Mk_gt_of_symWeight_witness_match (n := 2)
    ({![2, 1, 0], ![1, 1, 0]} : Finset (MultiIndex 3)) (fun _ => 1)
    (disjoint_of_histogram _ (by native_decide))
    (fun a => if a = ![2, 1, 0] then [2, 1] else [1, 1]) (by decide) 1 (by native_decide)
  exact_mod_cast h

end OrbitFree

end BoundedGaps
