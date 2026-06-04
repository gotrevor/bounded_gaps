import BoundedGaps.SymmetricReductionOrbitFree

open Finset
open scoped Nat
open BoundedGaps.SymmetricReduction BoundedGaps.SievePolynomial

namespace BoundedGaps.OrbitFree

/-- `matchDenSum` re-expressed as a sum over `matchDataN` (via the projection). -/
lemma matchDenSum_dataN (La Lb : List ℕ) (m : ℕ) :
    (matchDenSum La Lb m : ℚ)
      = ((matchDataN La Lb).map
          (fun t => (m.descFactorial (La.length + Lb.length - t.1) : ℚ) * (t.2.1 : ℚ))).sum := by
  unfold matchDenSum
  rw [← matchDataN_proj La Lb, List.map_map]
  push_cast [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _; simp only [Function.comp_apply]; push_cast; ring

/-- Sum over a `flatMap` (`AddCommMonoid`-valued). -/
lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → List β) :
    (l.flatMap g).sum = (l.map (fun x => (g x).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

/-- `Finset.range` sum equals the `List.range`-map sum. -/
lemma sum_range_eq_list {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    (∑ i ∈ Finset.range n, f i) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-- `(range n).zip Lb` (with `n = |Lb|`) is the map `j ↦ (j, Lb.getD j 0)`. -/
lemma zip_range_eq_map (Lb : List ℕ) :
    (List.range Lb.length).zip Lb = (List.range Lb.length).map (fun j => (j, Lb.getD j 0)) := by
  apply List.ext_getElem
  · simp [List.length_zip]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_range, List.getElem_map]
    have hi : i < Lb.length := by simpa using h1
    rw [List.getD_eq_getElem Lb 0 hi]

/-- General per-element weight identity (the heart of the recursion). -/
lemma weight_elt (k c W S : ℕ) (G gw : ℚ) :
    (k.descFactorial (S + 1) : ℚ) * ((c * W : ℕ) : ℚ)
        * ((gw + G) + ((k - (S + 1) : ℕ) : ℚ) * gWeight 0 0)
      = (k : ℚ) * (c : ℚ) *
          ((((k - 1).descFactorial S : ℚ) * (W : ℚ) * (G + (((k - 1) - S : ℕ) : ℚ) * gWeight 0 0))
            + gw * (((k - 1).descFactorial S : ℚ) * (W : ℚ))) := by
  rw [descFactorial_succ_eq' k S]
  have h : (k - (S + 1) : ℕ) = ((k - 1) - S : ℕ) := by omega
  rw [h]; push_cast; ring

set_option maxHeartbeats 1000000 in
theorem matchNumSum_cons_eq2 (a : ℕ) (La Lb : List ℕ) (k : ℕ) :
    matchNumSum (a :: La) Lb k =
      k * (a.factorial * (matchNumSum La Lb (k - 1)
              + gWeight a 0 * (matchDenSum La Lb (k - 1) : ℚ))
        + ∑ j ∈ Finset.range Lb.length,
            (a + Lb.getD j 0).factorial * (matchNumSum La (Lb.eraseIdx j) (k - 1)
              + gWeight a (Lb.getD j 0) * (matchDenSum La (Lb.eraseIdx j) (k - 1) : ℚ))) := by
  -- the (a::La)-problem weight, inlined (defeq to matchNumSum's let-lambda)
  have hMNS : matchNumSum (a :: La) Lb k
      = ((matchDataN (a :: La) Lb).map (fun t =>
          (k.descFactorial ((a :: La).length + Lb.length - t.1) : ℚ) * t.2.1
            * (t.2.2 + ((k - ((a :: La).length + Lb.length - t.1)) : ℕ) * gWeight 0 0))).sum := rfl
  -- a single branch (offset pp in the pair-count): ∑ over the entry-transformed matchDataN
  have hbranch : ∀ (c pp : ℕ) (L' : List ℕ) (gw : ℚ),
      (a :: La).length + Lb.length = La.length + L'.length + 1 + pp →
      (((matchDataN La L').map (fun t => (t.1 + pp, c * t.2.1, gw + t.2.2))).map (fun t =>
          (k.descFactorial ((a :: La).length + Lb.length - t.1) : ℚ) * t.2.1
            * (t.2.2 + ((k - ((a :: La).length + Lb.length - t.1)) : ℕ) * gWeight 0 0))).sum
        = (k : ℚ) * ((c : ℚ) * (matchNumSum La L' (k - 1)
            + gw * (matchDenSum La L' (k - 1) : ℚ))) := by
    intro c pp L' gw hlen
    rw [List.map_map]
    rw [List.map_congr_left (g := fun t => (k : ℚ) * (c : ℚ) *
              ((((k - 1).descFactorial (La.length + L'.length - t.1) : ℚ) * (t.2.1 : ℚ)
                  * (t.2.2 + (((k - 1) - (La.length + L'.length - t.1)) : ℕ) * gWeight 0 0))
                + gw * (((k - 1).descFactorial (La.length + L'.length - t.1) : ℚ) * (t.2.1 : ℚ))))
        (fun t ht => by
          have hle := matchDataN_fst_le La L' t ht
          simp only [Function.comp_apply]
          rw [show (a :: La).length + Lb.length - (t.1 + pp) = (La.length + L'.length - t.1) + 1
            from by omega]
          exact weight_elt k c t.2.1 (La.length + L'.length - t.1) t.2.2 gw)]
    rw [List.sum_map_mul_left, List.sum_map_add, List.sum_map_mul_left]
    have e1 : ((matchDataN La L').map (fun t => ((k - 1).descFactorial (La.length + L'.length - t.1) : ℚ)
        * (t.2.1 : ℚ) * (t.2.2 + (((k - 1) - (La.length + L'.length - t.1)) : ℕ) * gWeight 0 0))).sum
        = matchNumSum La L' (k - 1) := rfl
    have e2 : ((matchDataN La L').map (fun t => ((k - 1).descFactorial (La.length + L'.length - t.1) : ℚ)
        * (t.2.1 : ℚ))).sum = (matchDenSum La L' (k - 1) : ℚ) := (matchDenSum_dataN La L' (k - 1)).symm
    rw [e1, e2]; ring
  rw [hMNS, matchDataN, List.map_append, List.sum_append]
  rw [show (fun t : ℕ × ℕ × ℚ => (t.1, a.factorial * t.2.1, gWeight a 0 + t.2.2))
        = (fun t : ℕ × ℕ × ℚ => (t.1 + 0, a.factorial * t.2.1, gWeight a 0 + t.2.2)) from by
      funext t; simp only [Nat.add_zero]]
  rw [hbranch a.factorial 0 Lb (gWeight a 0) (by simp only [List.length_cons]; omega)]
  rw [zip_range_eq_map, List.flatMap_map, List.map_flatMap, list_sum_flatMap]
  rw [show ((List.range Lb.length).map (fun j =>
        (((matchDataN La (Lb.eraseIdx j)).map
            (fun t => (t.1 + 1, (a + Lb.getD j 0).factorial * t.2.1, gWeight a (Lb.getD j 0) + t.2.2))).map
          (fun t => (k.descFactorial ((a :: La).length + Lb.length - t.1) : ℚ) * t.2.1
            * (t.2.2 + ((k - ((a :: La).length + Lb.length - t.1)) : ℕ) * gWeight 0 0))).sum))
      = (List.range Lb.length).map (fun j => (k : ℚ) * ((a + Lb.getD j 0).factorial : ℚ)
          * (matchNumSum La (Lb.eraseIdx j) (k - 1)
            + gWeight a (Lb.getD j 0) * (matchDenSum La (Lb.eraseIdx j) (k - 1) : ℚ)))
      from List.map_congr_left (fun j hj => by
        rw [List.mem_range] at hj
        rw [hbranch (a + Lb.getD j 0).factorial 1 (Lb.eraseIdx j) (gWeight a (Lb.getD j 0))
          (by rw [List.length_eraseIdx, if_pos hj]; simp only [List.length_cons]; omega)]
        ring)]
  rw [← sum_range_eq_list]
  conv_rhs => rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

end BoundedGaps.OrbitFree
