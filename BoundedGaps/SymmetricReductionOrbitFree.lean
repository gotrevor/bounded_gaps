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

end OrbitFree

end BoundedGaps
