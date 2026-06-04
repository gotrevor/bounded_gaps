import BoundedGaps.SymmetricReductionOrbitFree

open Finset
open scoped Nat
open BoundedGaps.SymmetricReduction BoundedGaps.SievePolynomial

namespace BoundedGaps.OrbitFree

/-- The sum over all permutations of the product of factorials. -/
def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

/-! ### Orbit-sum ↔ permutation-sum bridge (from `ofParts_autParts_orbit_sum`) -/

lemma orbit_sum_eq_perm_sum {k : ℕ} (L : List ℕ) (f : MultiIndex k → ℕ)
    (hlen : L.length ≤ k) (hpos : ∀ x ∈ L, 0 < x) :
    autParts L * (k - L.length).factorial * ∑ p ∈ monoOrbit (ofParts L : MultiIndex k), f p
      = ∑ σ : Equiv.Perm (Fin k), f (fun i => ofParts L (σ i)) := by
  rw [ofParts_autParts_orbit_sum L hlen hpos f]
  simp only [smul_eq_mul]
  ring

/-! ### Laplace expansion of `permDenSum` (Aristotle `permDenSum_cons`, ported) -/

lemma permDenSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permDenSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), (a + ofParts Lb j).factorial *
        (∑ e : Equiv.Perm (Fin n),
          ∏ x : Fin n, (ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial) := by
  unfold permDenSum
  simp +decide only [ofParts, Fin.prod_univ_succ, Finset.mul_sum _ _ _]
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin.symm)]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => ⟨x.1, x.2⟩) ?_ ?_ ?_ ?_ <;> aesop

/-! ### Permutation invariance + column identity helpers -/

lemma permSum_perm_invariant {n : ℕ} (w c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, (w x + c (π (e x))).factorial)
      = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, (w x + c (e x)).factorial := by
  rw [← Equiv.sum_comp (Equiv.mulLeft π) (fun e : Equiv.Perm (Fin n) =>
        ∏ x : Fin n, (w x + c (e x)).factorial)]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.prod_congr rfl
  intro x _
  simp [Equiv.Perm.mul_apply]

lemma succAbove_val {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    (Fin.succAbove j x).val = if x.val < j.val then x.val else x.val + 1 := by
  rcases lt_or_ge (x.castSucc) j with h | h
  · rw [Fin.succAbove_of_castSucc_lt j x h]
    have : x.val < j.val := h
    simp [this, Fin.coe_castSucc]
  · rw [Fin.succAbove_of_le_castSucc j x h]
    have : ¬ x.val < j.val := by
      simp only [Fin.le_def, Fin.coe_castSucc] at h; omega
    simp [this, Fin.val_succ]

lemma eraseIdx_getD (Lb : List ℕ) (m i : ℕ) :
    (Lb.eraseIdx m).getD i 0 = if i < m then Lb.getD i 0 else Lb.getD (i + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : i < m
  · rw [if_pos h, List.getElem?_eraseIdx_of_lt h]
  · rw [if_neg h, List.getElem?_eraseIdx_of_ge (by omega)]

lemma ofParts_comp_succAbove {n : ℕ} (Lb : List ℕ) (j : Fin (n + 1)) :
    (fun x : Fin n => ofParts Lb (Fin.succAbove j x)) = ofParts (Lb.eraseIdx j.val) := by
  funext x
  show Lb.getD (Fin.succAbove j x).val 0 = (Lb.eraseIdx j.val).getD x.val 0
  rw [eraseIdx_getD, succAbove_val]
  by_cases h : x.val < j.val <;> simp [h]

/-! ### Laplace expansion of `permDenSum` -/

theorem permDenSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permDenSum (a :: La) Lb k =
      (k - Lb.length) * a.factorial * permDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * permDenSum La (Lb.eraseIdx j) (k - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [permDenSum_cons a La Lb n]
  have I_eq : ∀ j : Fin (n + 1),
      (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
          (ofParts La x + ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial)
        = permDenSum La (Lb.eraseIdx j.val) n := by
    intro j
    have hne : ∀ x : Fin n, Equiv.swap (0 : Fin (n + 1)) j (Fin.succ x) ≠ j := by
      intro x h
      have h2 := congrArg (Equiv.swap (0 : Fin (n + 1)) j) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h2
      exact Fin.succ_ne_zero x h2
    let g : Fin n → Fin n := fun x => (Fin.exists_succAbove_eq (hne x)).choose
    have hg : ∀ x, j.succAbove (g x) = Equiv.swap (0 : Fin (n + 1)) j (Fin.succ x) :=
      fun x => (Fin.exists_succAbove_eq (hne x)).choose_spec
    have hg_inj : Function.Injective g := by
      intro x1 x2 h12
      have heq : j.succAbove (g x1) = j.succAbove (g x2) := by rw [h12]
      rw [hg, hg] at heq
      exact Fin.succ_injective n ((Equiv.swap (0 : Fin (n + 1)) j).injective heq)
    let τ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective g ⟨hg_inj, Finite.injective_iff_surjective.mp hg_inj⟩
    have hτ : ∀ x, Equiv.swap (0 : Fin (n + 1)) j (Fin.succ x) = j.succAbove (τ x) :=
      fun x => (hg x).symm
    calc (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
            (ofParts La x + ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial)
        = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
            (ofParts La x + (fun y => ofParts Lb (j.succAbove y)) (τ (e x))).factorial := by
          apply Finset.sum_congr rfl; intro e _; apply Finset.prod_congr rfl; intro x _
          rw [hτ (e x)]
      _ = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
            (ofParts La x + (fun y => ofParts Lb (j.succAbove y)) (e x)).factorial :=
          permSum_perm_invariant (ofParts La) (fun y => ofParts Lb (j.succAbove y)) τ
      _ = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
            (ofParts La x + ofParts (Lb.eraseIdx j.val) (e x)).factorial := by
          rw [ofParts_comp_succAbove Lb j]
      _ = permDenSum La (Lb.eraseIdx j.val) n := rfl
  rw [Finset.sum_congr rfl (fun j _ => by rw [I_eq j])]
  have hfin : (∑ j : Fin (n + 1), (a + ofParts Lb j).factorial * permDenSum La (Lb.eraseIdx j.val) n)
      = ∑ i ∈ Finset.range (n + 1),
          (a + Lb.getD i 0).factorial * permDenSum La (Lb.eraseIdx i) n := by
    rw [← Fin.sum_univ_eq_sum_range
        (fun i => (a + Lb.getD i 0).factorial * permDenSum La (Lb.eraseIdx i) n) (n + 1)]
    rfl
  rw [hfin, ← Finset.sum_range_add_sum_Ico _ hlenB, add_comm]
  congr 1
  · have hconst : ∀ i ∈ Finset.Ico Lb.length (n + 1),
        (a + Lb.getD i 0).factorial * permDenSum La (Lb.eraseIdx i) n
          = a.factorial * permDenSum La Lb n := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h1 : Lb.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
      have h2 : Lb.eraseIdx i = Lb := List.eraseIdx_of_length_le (by omega)
      rw [h1, h2, Nat.add_zero]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    ring

/-! ### Unconditional descFactorial recursion + matchData bounds -/

lemma descFactorial_succ_eq' (k n : ℕ) :
    k.descFactorial (n + 1) = k * (k - 1).descFactorial n := by
  induction n with
  | zero => simp [Nat.descFactorial]
  | succ n ih =>
    rw [Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
    have h : k - (n + 1) = k - 1 - n := by omega
    rw [h]; ring

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

/-! ### `rhs_eq_perm` base case + induction -/

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

/-! ### `lhs_eq_perm` (Aristotle, monoOrbit) -/

lemma lhs_eq_perm (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    (k - La.length).factorial * (k - Lb.length).factorial *
      (autParts La * autParts Lb *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          ∏ i, (p i + q i).factorial))
      = k.factorial * permDenSum La Lb k := by
  have h1 : (k - La.length).factorial * autParts La *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          ∏ i, (p i + q i).factorial)
      = ∑ σ : Equiv.Perm (Fin k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          ∏ i, ((ofParts La (σ i)) + q i).factorial := by
    have := orbit_sum_eq_perm_sum La
      (fun p => ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k), ∏ i, (p i + q i).factorial) hlenA hposA
    rw [← this]; ring
  have h2 : ∀ σ : Equiv.Perm (Fin k),
      (k - Lb.length).factorial * autParts Lb *
        (∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k), ∏ i, ((ofParts La (σ i)) + q i).factorial)
      = ∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La (σ i)) + (ofParts Lb (τ i))).factorial := by
    intro σ
    have := orbit_sum_eq_perm_sum Lb
      (fun q => ∏ i, ((ofParts La (σ i)) + q i).factorial) hlenB hposB
    rw [← this]; ring
  have key : (k - La.length).factorial * (k - Lb.length).factorial *
      (autParts La * autParts Lb *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          ∏ i, (p i + q i).factorial))
      = (k - Lb.length).factorial * autParts Lb *
          (∑ σ : Equiv.Perm (Fin k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
            ∏ i, ((ofParts La (σ i)) + q i).factorial) := by
    rw [← h1]; ring
  rw [key, Finset.mul_sum, Finset.sum_congr rfl fun σ _ => h2 σ]
  have h_reindex : ∀ σ : Equiv.Perm (Fin k),
      (∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La (σ i)) + (ofParts Lb (τ i))).factorial)
        = ∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La i) + (ofParts Lb (τ i))).factorial := by
    intro σ
    apply Finset.sum_bij (fun τ _ => τ * σ⁻¹)
    · intro τ _; exact Finset.mem_univ _
    · intro τ1 _ τ2 _ h; exact mul_right_cancel h
    · intro τ _; exact ⟨τ * σ, Finset.mem_univ _, by simp [mul_assoc]⟩
    · intro τ _; rw [← Equiv.prod_comp σ⁻¹]; simp [Equiv.Perm.mul_apply]
  simp only [h_reindex, Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  simp [permDenSum]

/-! ### The denominator bridge (FULLY PROVEN) -/

theorem denom_bridge' {k : ℕ} (La Lb : List ℕ)
    (hLa : La.length ≤ k) (hLb : Lb.length ≤ k)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x) :
    autParts La * autParts Lb *
      (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb),
        ∏ i, (p i + q i).factorial)
      = matchDenSum La Lb k := by
  have h1 := lhs_eq_perm La Lb k hLa hLb hposa hposb
  have h2 := rhs_eq_perm La Lb k hLa hLb hposa hposb
  have hpos : 0 < (k - La.length).factorial * (k - Lb.length).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  -- both sides times the positive constant agree (h1, h2 share RHS k!*permDenSum)
  have hcomb : (k - La.length).factorial * (k - Lb.length).factorial *
      (autParts La * autParts Lb *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb),
          ∏ i, (p i + q i).factorial))
      = (k - La.length).factorial * (k - Lb.length).factorial * matchDenSum La Lb k := by
    rw [h1, ← h2]
  exact Nat.eq_of_mul_eq_mul_left hpos hcomb

end BoundedGaps.OrbitFree

#print axioms BoundedGaps.OrbitFree.denom_bridge'
