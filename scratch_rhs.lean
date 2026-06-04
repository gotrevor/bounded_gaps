import BoundedGaps.SymmetricReductionOrbitFree

open Finset
open scoped Nat

namespace BoundedGaps.OrbitFree

/-- The sum over all permutations of the product of factorials. -/
def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

/-! ## Unconditional descending-factorial front-factor identity -/

/-- `k.descFactorial (n+1) = k * (k-1).descFactorial n`, for ALL `k n`. -/
lemma descFactorial_succ_eq' (k n : ℕ) :
    k.descFactorial (n + 1) = k * (k - 1).descFactorial n := by
  induction n with
  | zero => simp [Nat.descFactorial]
  | succ n ih =>
    rw [Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
    have h : k - (n + 1) = k - 1 - n := by omega
    rw [h]; ring

/-! ## `matchData` first-coordinate bound + vanishing -/

lemma matchData_fst_le_la (La Lb : List ℕ) :
    ∀ pw ∈ matchData La Lb, pw.1 ≤ La.length := by
  induction La generalizing Lb with
  | nil => intro pw hpw; simp only [matchData, List.mem_singleton] at hpw; subst hpw; simp
  | cons a La ih =>
    intro pw hpw
    unfold matchData at hpw
    simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hpw
    rcases hpw with ⟨t, ht, rfl⟩ | ⟨jb, _, t, ht, rfl⟩
    · exact Nat.le_succ_of_le (ih Lb t ht)
    · exact Nat.succ_le_succ (ih (Lb.eraseIdx jb.1) t ht)

lemma matchDenSum_eq_zero_of_lt (La Lb : List ℕ) (k : ℕ) (h : k < Lb.length) :
    matchDenSum La Lb k = 0 := by
  unfold matchDenSum
  rw [List.sum_eq_zero]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨pw, hpw, rfl⟩ := hx
  have hle : pw.1 ≤ La.length := matchData_fst_le_la La Lb pw hpw
  have hlt : k < La.length + Lb.length - pw.1 := by omega
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.zero_mul]

/-! ## `matchDenSum` recursion (unconditional) -/

lemma matchDenSum_cons_eq' (a : ℕ) (La Lb : List ℕ) (k : ℕ) :
    matchDenSum (a :: La) Lb k =
      k * (a.factorial * matchDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * matchDenSum La (Lb.eraseIdx j) (k - 1)) := by
  unfold matchDenSum
  simp +decide [Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul]
  have h_descFactorial : ∀ pw ∈ matchData La Lb,
      k.descFactorial (La.length + 1 + Lb.length - pw.1)
        = k * (k - 1).descFactorial (La.length + Lb.length - pw.1) := by
    intro pw hpw
    have hle : pw.1 ≤ La.length := matchData_fst_le_la La Lb pw hpw
    rw [show La.length + 1 + Lb.length - pw.1 = (La.length + Lb.length - pw.1) + 1 from by omega]
    exact descFactorial_succ_eq' k _
  have h_descFactorial' : ∀ j ∈ List.range Lb.length, ∀ pw ∈ matchData La (Lb.eraseIdx j),
      k.descFactorial (La.length + Lb.length - pw.1)
        = k * (k - 1).descFactorial (La.length + (Lb.length - 1) - pw.1) := by
    intro j hj pw hpw
    rw [List.mem_range] at hj
    have hle : pw.1 ≤ La.length := matchData_fst_le_la La (Lb.eraseIdx j) pw hpw
    rw [show La.length + Lb.length - pw.1 = (La.length + (Lb.length - 1) - pw.1) + 1 from by omega]
    exact descFactorial_succ_eq' k _
  simp +decide [matchData, List.flatMap, List.sum_map_mul_left, List.sum_map_mul_right,
    h_descFactorial, h_descFactorial']
  congr! 1
  · rw [← mul_assoc, ← List.sum_map_mul_left]
    exact congr_arg _ (List.map_congr_left fun x hx => by
      rw [Function.comp_apply, h_descFactorial x hx]; ring)
  · refine congr_arg _ (List.ext_get ?_ ?_) <;> simp +decide [Function.comp]
    intro m hm
    rw [← mul_assoc, ← List.sum_map_mul_left]
    refine congr_arg _ (List.ext_get ?_ ?_) <;> simp +decide [Function.comp]
    grind

/-! ## Laplace expansion of `permDenSum` (the remaining hard core) -/

lemma permDenSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permDenSum (a :: La) Lb k =
      (k - Lb.length) * a.factorial * permDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * permDenSum La (Lb.eraseIdx j) (k - 1) := by
  sorry

/-! ## Base case of `rhs_eq_perm` -/

lemma permDenSum_nil (Lb : List ℕ) (k : ℕ) (hlen : Lb.length ≤ k) :
    permDenSum [] Lb k = k.factorial * (Lb.map Nat.factorial).prod := by
  unfold permDenSum
  simp only [ofParts]
  have h_prod : ∀ ρ : Equiv.Perm (Fin k),
      ∏ i : Fin k, ((([] : List ℕ).getD (i : Fin k).val 0) + Lb.getD (ρ i).val 0).factorial
        = (Lb.map Nat.factorial).prod := by
    intro ρ
    simp only [List.getD_nil, Nat.zero_add]
    have h_perm : ∏ i : Fin k, (Lb.getD (ρ i).val 0).factorial
               = ∏ i : Fin k, (Lb.getD i.val 0).factorial :=
      Equiv.prod_comp ρ (fun i => (Lb.getD (i : Fin k).val 0).factorial)
    rw [h_perm]
    exact prod_getD_fin Nat.factorial (by simp) k Lb hlen
  rw [Finset.sum_congr rfl (fun ρ _ => h_prod ρ)]
  simp [Finset.card_univ, Fintype.card_perm]

lemma rhs_eq_perm_nil (Lb : List ℕ) (k : ℕ)
    (hlenB : Lb.length ≤ k) (hposB : ∀ x ∈ Lb, 0 < x) :
    (k - ([] : List ℕ).length).factorial * (k - Lb.length).factorial *
      matchDenSum [] Lb k
      = k.factorial * permDenSum [] Lb k := by
  rw [permDenSum_nil Lb k hlenB, matchDenSum]
  simp only [matchData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.length_nil, Nat.sub_zero]
  rw [Nat.descFactorial_eq_factorial_mul_choose, ← Nat.choose_mul_factorial_mul_factorial hlenB]
  ring

/-! ## The induction -/

theorem rhs_eq_perm : ∀ (La Lb : List ℕ) (k : ℕ),
    La.length ≤ k → Lb.length ≤ k → (∀ x ∈ La, 0 < x) → (∀ x ∈ Lb, 0 < x) →
    (k - La.length).factorial * (k - Lb.length).factorial * matchDenSum La Lb k
      = k.factorial * permDenSum La Lb k := by
  intro La
  induction La with
  | nil => intro Lb k _ hlenB _ hposB; exact rhs_eq_perm_nil Lb k hlenB hposB
  | cons a La' ih =>
    intro Lb k hlenA hlenB hposA hposB
    have hapos : 0 < a := hposA a List.mem_cons_self
    have hposL : ∀ x ∈ La', 0 < x := fun x hx => hposA x (List.mem_cons_of_mem _ hx)
    have hlenA' : La'.length ≤ k - 1 := by simp only [List.length_cons] at hlenA; omega
    have hk1 : 1 ≤ k := by simp only [List.length_cons] at hlenA; omega
    have hk : k.factorial = k * (k - 1).factorial := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp [Nat.factorial_succ]
    rw [matchDenSum_cons_eq' a La' Lb k, permDenSum_laplace a La' Lb k hk1 hlenB]
    -- per-term identity over the matched sum
    have hB : ∀ j ∈ Finset.range Lb.length,
        (k - (a :: La').length).factorial * (k - Lb.length).factorial
          * (k * ((a + Lb.getD j 0).factorial * matchDenSum La' (Lb.eraseIdx j) (k - 1)))
          = k.factorial * ((a + Lb.getD j 0).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have heLen : (Lb.eraseIdx j).length = Lb.length - 1 := by
        rw [List.length_eraseIdx]; simp [hj]
      have hposE : ∀ x ∈ Lb.eraseIdx j, 0 < x := fun x hx => hposB x (List.mem_of_mem_eraseIdx hx)
      have heLen' : (Lb.eraseIdx j).length ≤ k - 1 := by rw [heLen]; omega
      have hIH := ih (Lb.eraseIdx j) (k - 1) hlenA' heLen' hposL hposE
      have hsub1 : k - 1 - La'.length = k - (a :: La').length := by
        simp only [List.length_cons]; omega
      have hsub2 : k - 1 - (Lb.eraseIdx j).length = k - Lb.length := by rw [heLen]; omega
      rw [hsub1, hsub2] at hIH
      rw [hk]
      calc (k - (a :: La').length).factorial * (k - Lb.length).factorial
            * (k * ((a + Lb.getD j 0).factorial * matchDenSum La' (Lb.eraseIdx j) (k - 1)))
          = k * (a + Lb.getD j 0).factorial
              * ((k - (a :: La').length).factorial * (k - Lb.length).factorial
                  * matchDenSum La' (Lb.eraseIdx j) (k - 1)) := by ring
        _ = k * (a + Lb.getD j 0).factorial * ((k - 1).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by rw [hIH]
        _ = k * (k - 1).factorial * ((a + Lb.getD j 0).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by ring
    -- first-term identity (handles |Lb| = k edge)
    have hA : (k - (a :: La').length).factorial * (k - Lb.length).factorial
          * (k * (a.factorial * matchDenSum La' Lb (k - 1)))
        = k.factorial * ((k - Lb.length) * a.factorial * permDenSum La' Lb (k - 1)) := by
      by_cases hLbk : Lb.length ≤ k - 1
      · have hIH := ih Lb (k - 1) hlenA' hLbk hposL hposB
        have hsub1 : k - 1 - La'.length = k - (a :: La').length := by
          simp only [List.length_cons]; omega
        rw [hsub1] at hIH
        have hfk : (k - Lb.length).factorial = (k - Lb.length) * (k - 1 - Lb.length).factorial := by
          have h1 : k - Lb.length = (k - 1 - Lb.length) + 1 := by omega
          rw [h1, Nat.factorial_succ]
        rw [hk, hfk]
        calc (k - (a :: La').length).factorial * ((k - Lb.length) * (k - 1 - Lb.length).factorial)
              * (k * (a.factorial * matchDenSum La' Lb (k - 1)))
            = k * (k - Lb.length) * a.factorial
                * ((k - (a :: La').length).factorial * (k - 1 - Lb.length).factorial
                    * matchDenSum La' Lb (k - 1)) := by ring
          _ = k * (k - Lb.length) * a.factorial * ((k - 1).factorial * permDenSum La' Lb (k - 1)) := by rw [hIH]
          _ = k * (k - 1).factorial * ((k - Lb.length) * a.factorial * permDenSum La' Lb (k - 1)) := by ring
      · have hzero : matchDenSum La' Lb (k - 1) = 0 :=
          matchDenSum_eq_zero_of_lt La' Lb (k - 1) (by omega)
        have hkLb : k - Lb.length = 0 := by omega
        rw [hzero, hkLb]; ring
    -- combine
    have hSum : (k - (a :: La').length).factorial * (k - Lb.length).factorial
          * (k * (∑ j ∈ Finset.range Lb.length,
              (a + Lb.getD j 0).factorial * matchDenSum La' (Lb.eraseIdx j) (k - 1)))
        = k.factorial * (∑ j ∈ Finset.range Lb.length,
            (a + Lb.getD j 0).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hB
    calc (k - (a :: La').length).factorial * (k - Lb.length).factorial
          * (k * (a.factorial * matchDenSum La' Lb (k - 1)
              + ∑ j ∈ Finset.range Lb.length,
                  (a + Lb.getD j 0).factorial * matchDenSum La' (Lb.eraseIdx j) (k - 1)))
        = (k - (a :: La').length).factorial * (k - Lb.length).factorial
              * (k * (a.factorial * matchDenSum La' Lb (k - 1)))
            + (k - (a :: La').length).factorial * (k - Lb.length).factorial
                * (k * (∑ j ∈ Finset.range Lb.length,
                    (a + Lb.getD j 0).factorial * matchDenSum La' (Lb.eraseIdx j) (k - 1))) := by ring
      _ = k.factorial * ((k - Lb.length) * a.factorial * permDenSum La' Lb (k - 1))
            + k.factorial * (∑ j ∈ Finset.range Lb.length,
                (a + Lb.getD j 0).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by rw [hA, hSum]
      _ = k.factorial * ((k - Lb.length) * a.factorial * permDenSum La' Lb (k - 1)
            + ∑ j ∈ Finset.range Lb.length,
                (a + Lb.getD j 0).factorial * permDenSum La' (Lb.eraseIdx j) (k - 1)) := by ring

end BoundedGaps.OrbitFree
