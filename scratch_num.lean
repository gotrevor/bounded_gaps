import BoundedGaps.SymmetricReductionOrbitFree

open Finset
open scoped Nat
open BoundedGaps.SymmetricReduction BoundedGaps.SievePolynomial

namespace BoundedGaps.OrbitFree

/-- Numerator permanent: the perm-sum of `∏(pᵢ+qᵢ)! · ∑ gWeight(pᵢ,qᵢ)`. -/
def permNumSum (La Lb : List ℕ) (k : ℕ) : ℚ :=
  ∑ ρ : Equiv.Perm (Fin k),
    (∏ i : Fin k, ((ofParts La i + ofParts Lb (ρ i)).factorial : ℚ))
      * (∑ i : Fin k, gWeight (ofParts La i) (ofParts Lb (ρ i)))

/-- ℚ-valued orbit-sum ↔ perm-sum bridge. -/
lemma orbit_sum_eq_perm_sum_Q {k : ℕ} (L : List ℕ) (f : MultiIndex k → ℚ)
    (hlen : L.length ≤ k) (hpos : ∀ x ∈ L, 0 < x) :
    (autParts L : ℚ) * ((k - L.length).factorial : ℚ) *
        ∑ p ∈ monoOrbit (ofParts L : MultiIndex k), f p
      = ∑ σ : Equiv.Perm (Fin k), f (fun i => ofParts L (σ i)) := by
  rw [ofParts_autParts_orbit_sum L hlen hpos f]
  simp only [nsmul_eq_mul]
  ring

/-! ### Mechanical recursions (sorried; Aristotle `d314bdc2` for matchNumSum_cons_eq') -/

lemma matchDataN_proj (La Lb : List ℕ) :
    (matchDataN La Lb).map (fun t => (t.1, t.2.1)) = matchData La Lb := by
  induction La generalizing Lb with
  | nil => rfl
  | cons a La ih =>
    rw [matchDataN, matchData, List.map_append]
    congr 1
    · rw [List.map_map, ← ih Lb, List.map_map]
      apply List.map_congr_left; intro t _; rfl
    · rw [List.map_flatMap]
      apply List.flatMap_congr
      intro jb _
      rw [List.map_map, ← ih (Lb.eraseIdx jb.1), List.map_map]
      apply List.map_congr_left; intro t _; rfl

/-- **`matchNumSum` recursion** (numerator analog of the proven `matchDenSum_cons_eq'`). The
`gWeight a (·)` of the new first row pulls out a `matchDenSum` term, so the recursion couples
`matchNumSum` and `matchDenSum` at `k-1`. Elementary list/recursion identity (no permanent theory);
NUMERICALLY VALIDATED by `native_decide` (`La=[2,1],Lb=[1,1],k=4` and `La=[3,2,1],Lb=[2,1],k=5`).
Disclosed `axiom` pending the mechanical port of the `matchDenSum_cons_eq'` proof (Aristotle
`d314bdc2`); this is the ONLY remaining gap on the numerator side. -/
axiom matchNumSum_cons_eq' (a : ℕ) (La Lb : List ℕ) (k : ℕ) :
    matchNumSum (a :: La) Lb k =
      k * (a.factorial * (matchNumSum La Lb (k - 1)
              + gWeight a 0 * (matchDenSum La Lb (k - 1) : ℚ))
        + ∑ j ∈ Finset.range Lb.length,
            (a + Lb.getD j 0).factorial * (matchNumSum La (Lb.eraseIdx j) (k - 1)
              + gWeight a (Lb.getD j 0) * (matchDenSum La (Lb.eraseIdx j) (k - 1) : ℚ)))

lemma permNumSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permNumSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), ((a + ofParts Lb j).factorial : ℚ) *
        (∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
            * (gWeight a (ofParts Lb j) +
                ∑ x : Fin n, gWeight (ofParts La x)
                  (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))))) := by
  unfold permNumSum
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin.symm), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [ofParts, List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  ring

/-! ### Inner-sum collapse (num + den), reusing the column machinery -/

/-- gWeight-weighted permutation invariance. -/
lemma permSum_gw_invariant {n : ℕ} (w c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    (∑ e : Equiv.Perm (Fin n),
        (∏ x : Fin n, ((w x + c (π (e x))).factorial : ℚ))
          * (∑ x : Fin n, gWeight (w x) (c (π (e x)))))
      = ∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((w x + c (e x)).factorial : ℚ))
            * (∑ x : Fin n, gWeight (w x) (c (e x))) := by
  rw [← Equiv.sum_comp (Equiv.mulLeft π) (fun e : Equiv.Perm (Fin n) =>
        (∏ x : Fin n, ((w x + c (e x)).factorial : ℚ)) * (∑ x : Fin n, gWeight (w x) (c (e x))))]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply]

/-- The numerator inner sum collapses to `permNumSum` on the column-removed list. -/
lemma inner_num_eq (La Lb : List ℕ) (n : ℕ) (j : Fin (n + 1)) :
    (∑ e : Equiv.Perm (Fin n),
        (∏ x : Fin n, ((ofParts La x +
          ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
          * (∑ x : Fin n, gWeight (ofParts La x)
              (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x))))))
      = permNumSum La (Lb.eraseIdx j.val) n := by
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
  calc (∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
            * (∑ x : Fin n, gWeight (ofParts La x)
                (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x))))))
      = ∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            (fun y => ofParts Lb (j.succAbove y)) (τ (e x))).factorial : ℚ))
            * (∑ x : Fin n, gWeight (ofParts La x)
                ((fun y => ofParts Lb (j.succAbove y)) (τ (e x)))) := by
        apply Finset.sum_congr rfl; intro e _
        congr 1
        · apply Finset.prod_congr rfl; intro x _; rw [hτ (e x)]
        · apply Finset.sum_congr rfl; intro x _; rw [hτ (e x)]
    _ = ∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            (fun y => ofParts Lb (j.succAbove y)) (e x)).factorial : ℚ))
            * (∑ x : Fin n, gWeight (ofParts La x)
                ((fun y => ofParts Lb (j.succAbove y)) (e x))) :=
        permSum_gw_invariant (ofParts La) (fun y => ofParts Lb (j.succAbove y)) τ
    _ = ∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x + ofParts (Lb.eraseIdx j.val) (e x)).factorial : ℚ))
            * (∑ x : Fin n, gWeight (ofParts La x) (ofParts (Lb.eraseIdx j.val) (e x))) := by
        rw [ofParts_comp_succAbove Lb j]
    _ = permNumSum La (Lb.eraseIdx j.val) n := rfl

/-- The denominator inner sum collapses to `permDenSum` on the column-removed list (ℚ-cast). -/
lemma inner_den_eq (La Lb : List ℕ) (n : ℕ) (j : Fin (n + 1)) :
    (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
        ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
      = (permDenSum La (Lb.eraseIdx j.val) n : ℚ) := by
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
  have hQ : (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
        (fun y => ofParts Lb (j.succAbove y)) (τ (e x))).factorial : ℚ))
      = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
        (fun y => ofParts Lb (j.succAbove y)) (e x)).factorial : ℚ) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft τ) (fun e : Equiv.Perm (Fin n) =>
          ∏ x : Fin n, ((ofParts La x + (fun y => ofParts Lb (j.succAbove y)) (e x)).factorial : ℚ))]
    apply Finset.sum_congr rfl; intro e _
    apply Finset.prod_congr rfl; intro x _; simp [Equiv.Perm.mul_apply]
  calc (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
          ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
      = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
          (fun y => ofParts Lb (j.succAbove y)) (τ (e x))).factorial : ℚ) := by
        apply Finset.sum_congr rfl; intro e _; apply Finset.prod_congr rfl; intro x _; rw [hτ (e x)]
    _ = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
          (fun y => ofParts Lb (j.succAbove y)) (e x)).factorial : ℚ) := hQ
    _ = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n,
          ((ofParts La x + ofParts (Lb.eraseIdx j.val) (e x)).factorial : ℚ) := by
        rw [ofParts_comp_succAbove Lb j]
    _ = (permDenSum La (Lb.eraseIdx j.val) n : ℚ) := by
        unfold permDenSum; push_cast; rfl

/-! ### Laplace expansion of `permNumSum` -/

theorem permNumSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permNumSum (a :: La) Lb k =
      ((k - Lb.length : ℕ) : ℚ) * (a.factorial : ℚ)
          * (permNumSum La Lb (k - 1) + gWeight a 0 * (permDenSum La Lb (k - 1) : ℚ))
      + ∑ j ∈ Finset.range Lb.length,
          ((a + Lb.getD j 0).factorial : ℚ)
            * (permNumSum La (Lb.eraseIdx j) (k - 1)
                + gWeight a (Lb.getD j 0) * (permDenSum La (Lb.eraseIdx j) (k - 1) : ℚ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [permNumSum_cons a La Lb n]
  have hcollapse : ∀ j : Fin (n + 1),
      ((a + ofParts Lb j).factorial : ℚ) *
        (∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
            * (gWeight a (ofParts Lb j) +
                ∑ x : Fin n, gWeight (ofParts La x)
                  (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x))))))
      = ((a + ofParts Lb j).factorial : ℚ) *
          (gWeight a (ofParts Lb j) * (permDenSum La (Lb.eraseIdx j.val) n : ℚ)
            + permNumSum La (Lb.eraseIdx j.val) n) := by
    intro j
    congr 1
    have hsplit : (∑ e : Equiv.Perm (Fin n),
          (∏ x : Fin n, ((ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
            * (gWeight a (ofParts Lb j) +
                ∑ x : Fin n, gWeight (ofParts La x)
                  (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x))))))
        = gWeight a (ofParts Lb j) *
            (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, ((ofParts La x +
              ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
          + (∑ e : Equiv.Perm (Fin n),
              (∏ x : Fin n, ((ofParts La x +
                ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial : ℚ))
                * (∑ x : Fin n, gWeight (ofParts La x)
                    (ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro e _; ring
    rw [hsplit, inner_den_eq, inner_num_eq]
  rw [Finset.sum_congr rfl (fun j _ => hcollapse j)]
  have hfin : (∑ j : Fin (n + 1), ((a + ofParts Lb j).factorial : ℚ) *
        (gWeight a (ofParts Lb j) * (permDenSum La (Lb.eraseIdx j.val) n : ℚ)
          + permNumSum La (Lb.eraseIdx j.val) n))
      = ∑ i ∈ Finset.range (n + 1), ((a + Lb.getD i 0).factorial : ℚ) *
          (gWeight a (Lb.getD i 0) * (permDenSum La (Lb.eraseIdx i) n : ℚ)
            + permNumSum La (Lb.eraseIdx i) n) := by
    rw [← Fin.sum_univ_eq_sum_range
        (fun i => ((a + Lb.getD i 0).factorial : ℚ) *
          (gWeight a (Lb.getD i 0) * (permDenSum La (Lb.eraseIdx i) n : ℚ)
            + permNumSum La (Lb.eraseIdx i) n)) (n + 1)]
    rfl
  rw [hfin, ← Finset.sum_range_add_sum_Ico _ hlenB, add_comm]
  congr 1
  · have hconst : ∀ i ∈ Finset.Ico Lb.length (n + 1),
        ((a + Lb.getD i 0).factorial : ℚ) *
            (gWeight a (Lb.getD i 0) * (permDenSum La (Lb.eraseIdx i) n : ℚ)
              + permNumSum La (Lb.eraseIdx i) n)
          = (a.factorial : ℚ) *
              (gWeight a 0 * (permDenSum La Lb n : ℚ) + permNumSum La Lb n) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have h1 : Lb.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
      have h2 : Lb.eraseIdx i = Lb := List.eraseIdx_of_length_le (by omega)
      rw [h1, h2, Nat.add_zero]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    push_cast; ring
  · apply Finset.sum_congr rfl
    intro j _; ring

/-! ### Vanishing + nil base case -/

lemma matchDataN_fst_le (La Lb : List ℕ) :
    ∀ t ∈ matchDataN La Lb, t.1 ≤ La.length := by
  intro t ht
  have hmem : (t.1, t.2.1) ∈ matchData La Lb := by
    rw [← matchDataN_proj La Lb]; exact List.mem_map_of_mem ht
  exact matchData_fst_le_la La Lb (t.1, t.2.1) hmem

lemma matchNumSum_eq_zero_of_lt (La Lb : List ℕ) (k : ℕ) (h : k < Lb.length) :
    matchNumSum La Lb k = 0 := by
  unfold matchNumSum
  rw [List.sum_eq_zero]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hle : t.1 ≤ La.length := matchDataN_fst_le La Lb t ht
  have hlt : k < La.length + Lb.length - t.1 := by omega
  simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero, zero_mul]

lemma permNumSum_nil (Lb : List ℕ) (k : ℕ) (hlen : Lb.length ≤ k) :
    permNumSum [] Lb k = (k.factorial : ℚ) *
      (((Lb.map Nat.factorial).prod : ℚ) *
        ((Lb.map (fun b => gWeight 0 b)).sum + ((k - Lb.length : ℕ) : ℚ) * gWeight 0 0)) := by
  unfold permNumSum
  have hterm : ∀ ρ : Equiv.Perm (Fin k),
      (∏ i : Fin k, ((ofParts [] i + ofParts Lb (ρ i)).factorial : ℚ))
          * (∑ i : Fin k, gWeight (ofParts [] i) (ofParts Lb (ρ i)))
        = ((Lb.map Nat.factorial).prod : ℚ) *
            ((Lb.map (fun b => gWeight 0 b)).sum + ((k - Lb.length : ℕ) : ℚ) * gWeight 0 0) := by
    intro ρ
    have hp : (∏ i : Fin k, ((ofParts [] i + ofParts Lb (ρ i)).factorial : ℚ))
        = ((Lb.map Nat.factorial).prod : ℚ) := by
      rw [show (∏ i : Fin k, ((ofParts [] i + ofParts Lb (ρ i)).factorial : ℚ))
            = ∏ i : Fin k, ((ofParts Lb (ρ i)).factorial : ℚ) from
        Finset.prod_congr rfl (fun i _ => by simp [ofParts])]
      rw [Equiv.prod_comp ρ (fun j => ((ofParts Lb j).factorial : ℚ)), ← Nat.cast_prod]
      norm_cast
      exact prod_getD_fin Nat.factorial (by simp) k Lb hlen
    have hs : (∑ i : Fin k, gWeight (ofParts [] i) (ofParts Lb (ρ i)))
        = (Lb.map (fun b => gWeight 0 b)).sum + ((k - Lb.length : ℕ) : ℚ) * gWeight 0 0 := by
      rw [show (∑ i : Fin k, gWeight (ofParts [] i) (ofParts Lb (ρ i)))
            = ∑ i : Fin k, gWeight 0 (ofParts Lb (ρ i)) from
        Finset.sum_congr rfl (fun i _ => by simp [ofParts])]
      rw [Equiv.sum_comp ρ (fun j => gWeight 0 (ofParts Lb j))]
      simp only [ofParts]
      rw [sum_getD_fin_gen (fun b => gWeight 0 b) k Lb hlen, nsmul_eq_mul]
    rw [hp, hs]
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma rhs_num_nil (Lb : List ℕ) (k : ℕ)
    (hlenB : Lb.length ≤ k) (hposB : ∀ x ∈ Lb, 0 < x) :
    ((k - ([] : List ℕ).length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ) *
        matchNumSum [] Lb k
      = (k.factorial : ℚ) * permNumSum [] Lb k := by
  rw [permNumSum_nil Lb k hlenB]
  have hM : matchNumSum [] Lb k = ((k.descFactorial Lb.length : ℕ) : ℚ) *
      (((Lb.map Nat.factorial).prod : ℚ) *
        ((Lb.map (fun b => gWeight 0 b)).sum + ((k - Lb.length : ℕ) : ℚ) * gWeight 0 0)) := by
    simp only [matchNumSum, matchDataN, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Nat.zero_add, Nat.sub_zero, List.length_nil]
    push_cast; ring
  rw [hM]
  have hfd : ((k - Lb.length).factorial : ℚ) * (k.descFactorial Lb.length : ℚ) = (k.factorial : ℚ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial hlenB]
  set V : ℚ := ((Lb.map Nat.factorial).prod : ℚ) *
      ((Lb.map (fun b => gWeight 0 b)).sum + ((k - Lb.length : ℕ) : ℚ) * gWeight 0 0) with hVdef
  simp only [List.length_nil, Nat.sub_zero]
  calc (k.factorial : ℚ) * ((k - Lb.length).factorial : ℚ) * ((k.descFactorial Lb.length : ℚ) * V)
      = ((k - Lb.length).factorial : ℚ) * (k.descFactorial Lb.length : ℚ) * ((k.factorial : ℚ) * V) := by ring
    _ = (k.factorial : ℚ) * ((k.factorial : ℚ) * V) := by rw [hfd]

/-! ### `rhs_num` induction -/

theorem rhs_num : ∀ (La Lb : List ℕ) (k : ℕ),
    La.length ≤ k → Lb.length ≤ k → (∀ x ∈ La, 0 < x) → (∀ x ∈ Lb, 0 < x) →
    ((k - La.length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ) * matchNumSum La Lb k
      = (k.factorial : ℚ) * permNumSum La Lb k := by
  intro La
  induction La with
  | nil => intro Lb k _ hlenB _ hposB; exact rhs_num_nil Lb k hlenB hposB
  | cons a La' ih =>
    intro Lb k hlenA hlenB hposA hposB
    have hposL : ∀ x ∈ La', 0 < x := fun x hx => hposA x (List.mem_cons_of_mem _ hx)
    have hlenA' : La'.length ≤ k - 1 := by simp only [List.length_cons] at hlenA; omega
    have hk1 : 1 ≤ k := by simp only [List.length_cons] at hlenA; omega
    have hkc : (k.factorial : ℚ) = (k : ℚ) * ((k - 1).factorial : ℚ) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]; push_cast; ring
    -- combined num+den atom: IH(num) + rhs_eq_perm(den)
    have hatom : ∀ (Lb' : List ℕ) (g : ℚ), Lb'.length ≤ k - 1 → (∀ x ∈ Lb', 0 < x) →
        ((k - 1 - La'.length).factorial : ℚ) * ((k - 1 - Lb'.length).factorial : ℚ)
            * (matchNumSum La' Lb' (k - 1) + g * (matchDenSum La' Lb' (k - 1) : ℚ))
          = ((k - 1).factorial : ℚ)
              * (permNumSum La' Lb' (k - 1) + g * (permDenSum La' Lb' (k - 1) : ℚ)) := by
      intro Lb' g hlen' hpos'
      have hN := ih Lb' (k - 1) hlenA' hlen' hposL hpos'
      have hD := rhs_eq_perm La' Lb' (k - 1) hlenA' hlen' hposL hpos'
      have hDQ : ((k - 1 - La'.length).factorial : ℚ) * ((k - 1 - Lb'.length).factorial : ℚ)
          * (matchDenSum La' Lb' (k - 1) : ℚ)
          = ((k - 1).factorial : ℚ) * (permDenSum La' Lb' (k - 1) : ℚ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℚ)) hD
      have hexp : ((k - 1 - La'.length).factorial : ℚ) * ((k - 1 - Lb'.length).factorial : ℚ)
            * (matchNumSum La' Lb' (k - 1) + g * (matchDenSum La' Lb' (k - 1) : ℚ))
          = (((k - 1 - La'.length).factorial : ℚ) * ((k - 1 - Lb'.length).factorial : ℚ)
                * matchNumSum La' Lb' (k - 1))
            + g * (((k - 1 - La'.length).factorial : ℚ) * ((k - 1 - Lb'.length).factorial : ℚ)
                * (matchDenSum La' Lb' (k - 1) : ℚ)) := by ring
      rw [hexp, hN, hDQ]; ring
    rw [matchNumSum_cons_eq' a La' Lb k, permNumSum_laplace a La' Lb k hk1 hlenB]
    -- j-term identity
    have hB : ∀ j ∈ Finset.range Lb.length,
        ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
          * ((k : ℚ) * (((a + Lb.getD j 0).factorial : ℚ)
              * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                  + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))))
          = (k.factorial : ℚ) * (((a + Lb.getD j 0).factorial : ℚ)
              * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                  + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have heLen : (Lb.eraseIdx j).length = Lb.length - 1 := by rw [List.length_eraseIdx]; simp [hj]
      have hposE : ∀ x ∈ Lb.eraseIdx j, 0 < x := fun x hx => hposB x (List.mem_of_mem_eraseIdx hx)
      have heLen' : (Lb.eraseIdx j).length ≤ k - 1 := by rw [heLen]; omega
      have hA1 := hatom (Lb.eraseIdx j) (gWeight a (Lb.getD j 0)) heLen' hposE
      have hsub1 : k - 1 - La'.length = k - (a :: La').length := by
        simp only [List.length_cons]; omega
      have hsub2 : k - 1 - (Lb.eraseIdx j).length = k - Lb.length := by rw [heLen]; omega
      rw [hsub1, hsub2] at hA1
      rw [hkc]
      calc ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
            * ((k : ℚ) * (((a + Lb.getD j 0).factorial : ℚ)
                * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                    + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))))
          = (k : ℚ) * ((a + Lb.getD j 0).factorial : ℚ)
              * (((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
                  * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                      + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by ring
        _ = (k : ℚ) * ((a + Lb.getD j 0).factorial : ℚ)
              * (((k - 1).factorial : ℚ)
                  * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                      + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by rw [hA1]
        _ = (k : ℚ) * ((k - 1).factorial : ℚ) * (((a + Lb.getD j 0).factorial : ℚ)
              * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                  + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by ring
    -- first-term identity (|Lb| = k edge handled by vanishing)
    have hA : ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
          * ((k : ℚ) * (((a).factorial : ℚ)
              * (matchNumSum La' Lb (k - 1) + gWeight a 0 * (matchDenSum La' Lb (k - 1) : ℚ))))
        = (k.factorial : ℚ) * (((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
            * (permNumSum La' Lb (k - 1) + gWeight a 0 * (permDenSum La' Lb (k - 1) : ℚ))) := by
      by_cases hLbk : Lb.length ≤ k - 1
      · have hA1 := hatom Lb (gWeight a 0) hLbk hposB
        have hsub1 : k - 1 - La'.length = k - (a :: La').length := by
          simp only [List.length_cons]; omega
        rw [hsub1] at hA1
        have hfk : ((k - Lb.length).factorial : ℚ)
            = ((k - Lb.length : ℕ) : ℚ) * ((k - 1 - Lb.length).factorial : ℚ) := by
          have h1 : k - Lb.length = (k - 1 - Lb.length) + 1 := by omega
          rw [h1, Nat.factorial_succ]; push_cast; congr 2 <;> omega
        rw [hkc, hfk]
        calc ((k - (a :: La').length).factorial : ℚ)
              * (((k - Lb.length : ℕ) : ℚ) * ((k - 1 - Lb.length).factorial : ℚ))
              * ((k : ℚ) * (((a).factorial : ℚ)
                  * (matchNumSum La' Lb (k - 1) + gWeight a 0 * (matchDenSum La' Lb (k - 1) : ℚ))))
            = (k : ℚ) * ((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
                * (((k - (a :: La').length).factorial : ℚ) * ((k - 1 - Lb.length).factorial : ℚ)
                    * (matchNumSum La' Lb (k - 1) + gWeight a 0 * (matchDenSum La' Lb (k - 1) : ℚ))) := by ring
          _ = (k : ℚ) * ((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
                * (((k - 1).factorial : ℚ)
                    * (permNumSum La' Lb (k - 1) + gWeight a 0 * (permDenSum La' Lb (k - 1) : ℚ))) := by rw [hA1]
          _ = (k : ℚ) * ((k - 1).factorial : ℚ) * (((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
                * (permNumSum La' Lb (k - 1) + gWeight a 0 * (permDenSum La' Lb (k - 1) : ℚ))) := by ring
      · have hzN : matchNumSum La' Lb (k - 1) = 0 := matchNumSum_eq_zero_of_lt La' Lb (k - 1) (by omega)
        have hzD : matchDenSum La' Lb (k - 1) = 0 := matchDenSum_eq_zero_of_lt La' Lb (k - 1) (by omega)
        have hkLb : ((k - Lb.length : ℕ) : ℚ) = 0 := by
          have : k - Lb.length = 0 := by omega
          rw [this]; simp
        rw [hzN, hzD, hkLb]; push_cast; ring
    -- combine
    have hSum : ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
          * ((k : ℚ) * (∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
              * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                  + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))))
        = (k.factorial : ℚ) * (∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
            * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hB
    calc ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
          * ((k : ℚ) * (((a).factorial : ℚ)
              * (matchNumSum La' Lb (k - 1) + gWeight a 0 * (matchDenSum La' Lb (k - 1) : ℚ))
            + ∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
                * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                    + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))))
        = (((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
              * ((k : ℚ) * (((a).factorial : ℚ)
                  * (matchNumSum La' Lb (k - 1) + gWeight a 0 * (matchDenSum La' Lb (k - 1) : ℚ)))))
          + ((k - (a :: La').length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ)
              * ((k : ℚ) * (∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
                  * (matchNumSum La' (Lb.eraseIdx j) (k - 1)
                      + gWeight a (Lb.getD j 0) * (matchDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ)))) := by ring
      _ = (k.factorial : ℚ) * (((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
              * (permNumSum La' Lb (k - 1) + gWeight a 0 * (permDenSum La' Lb (k - 1) : ℚ)))
          + (k.factorial : ℚ) * (∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
              * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                  + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by rw [hA, hSum]
      _ = (k.factorial : ℚ) * (((k - Lb.length : ℕ) : ℚ) * ((a).factorial : ℚ)
              * (permNumSum La' Lb (k - 1) + gWeight a 0 * (permDenSum La' Lb (k - 1) : ℚ))
            + ∑ j ∈ Finset.range Lb.length, ((a + Lb.getD j 0).factorial : ℚ)
                * (permNumSum La' (Lb.eraseIdx j) (k - 1)
                    + gWeight a (Lb.getD j 0) * (permDenSum La' (Lb.eraseIdx j) (k - 1) : ℚ))) := by ring

/-! ### `lhs_num` -/

lemma lhs_num (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    ((k - La.length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ) *
      ((autParts La : ℚ) * (autParts Lb : ℚ) *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i))))
      = (k.factorial : ℚ) * permNumSum La Lb k := by
  have h1 : ((k - La.length).factorial : ℚ) * (autParts La : ℚ) *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i)))
      = ∑ σ : Equiv.Perm (Fin k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          (∏ m, ((ofParts La (σ m) + q m).factorial : ℚ))
            * (∑ i, gWeight (ofParts La (σ i)) (q i)) := by
    have := orbit_sum_eq_perm_sum_Q La
      (fun p => ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
        (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i))) hlenA hposA
    rw [← this]; ring
  have h2 : ∀ σ : Equiv.Perm (Fin k),
      ((k - Lb.length).factorial : ℚ) * (autParts Lb : ℚ) *
        (∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          (∏ m, ((ofParts La (σ m) + q m).factorial : ℚ)) * (∑ i, gWeight (ofParts La (σ i)) (q i)))
      = ∑ τ : Equiv.Perm (Fin k),
          (∏ m, ((ofParts La (σ m) + ofParts Lb (τ m)).factorial : ℚ))
            * (∑ i, gWeight (ofParts La (σ i)) (ofParts Lb (τ i))) := by
    intro σ
    have := orbit_sum_eq_perm_sum_Q Lb
      (fun q => (∏ m, ((ofParts La (σ m) + q m).factorial : ℚ))
        * (∑ i, gWeight (ofParts La (σ i)) (q i))) hlenB hposB
    rw [← this]; ring
  have key : ((k - La.length).factorial : ℚ) * ((k - Lb.length).factorial : ℚ) *
      ((autParts La : ℚ) * (autParts Lb : ℚ) *
        (∑ p ∈ monoOrbit (ofParts La : MultiIndex k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
          (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i))))
      = ((k - Lb.length).factorial : ℚ) * (autParts Lb : ℚ) *
          (∑ σ : Equiv.Perm (Fin k), ∑ q ∈ monoOrbit (ofParts Lb : MultiIndex k),
            (∏ m, ((ofParts La (σ m) + q m).factorial : ℚ))
              * (∑ i, gWeight (ofParts La (σ i)) (q i))) := by
    rw [← h1]; ring
  rw [key, Finset.mul_sum, Finset.sum_congr rfl fun σ _ => h2 σ]
  have h_reindex : ∀ σ : Equiv.Perm (Fin k),
      (∑ τ : Equiv.Perm (Fin k),
          (∏ m, ((ofParts La (σ m) + ofParts Lb (τ m)).factorial : ℚ))
            * (∑ i, gWeight (ofParts La (σ i)) (ofParts Lb (τ i))))
        = ∑ τ : Equiv.Perm (Fin k),
            (∏ m, ((ofParts La m + ofParts Lb (τ m)).factorial : ℚ))
              * (∑ i, gWeight (ofParts La i) (ofParts Lb (τ i))) := by
    intro σ
    apply Finset.sum_bij (fun τ _ => τ * σ⁻¹)
    · intro τ _; exact Finset.mem_univ _
    · intro τ1 _ τ2 _ h; exact mul_right_cancel h
    · intro τ _; exact ⟨τ * σ, Finset.mem_univ _, by simp [mul_assoc]⟩
    · intro τ _
      congr 1
      · rw [← Equiv.prod_comp σ⁻¹]; apply Finset.prod_congr rfl; intro m _
        simp [Equiv.Perm.mul_apply]
      · rw [← Equiv.sum_comp σ⁻¹]; apply Finset.sum_congr rfl; intro i _
        simp [Equiv.Perm.mul_apply]
  simp only [h_reindex, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [permNumSum]

/-! ### The numerator bridge (FULLY PROVEN modulo `matchNumSum_cons_eq'`) -/

theorem num_bridge' {n : ℕ} (La Lb : List ℕ)
    (hLa : La.length ≤ n + 1) (hLb : Lb.length ≤ n + 1)
    (hposa : ∀ x ∈ La, 0 < x) (hposb : ∀ x ∈ Lb, 0 < x) :
    (autParts La : ℚ) * (autParts Lb : ℚ) *
      (∑ p ∈ monoOrbit (ofParts La : MultiIndex (n + 1)), ∑ q ∈ monoOrbit (ofParts Lb),
        (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i)))
      = matchNumSum La Lb (n + 1) := by
  have h1 := lhs_num La Lb (n + 1) hLa hLb hposa hposb
  have h2 := rhs_num La Lb (n + 1) hLa hLb hposa hposb
  have hpos : (0 : ℚ) < ((n + 1 - La.length).factorial : ℚ) * ((n + 1 - Lb.length).factorial : ℚ) := by
    have : (0 : ℕ) < (n + 1 - La.length).factorial * (n + 1 - Lb.length).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    exact_mod_cast this
  have hcomb : ((n + 1 - La.length).factorial : ℚ) * ((n + 1 - Lb.length).factorial : ℚ) *
        ((autParts La : ℚ) * (autParts Lb : ℚ) *
          (∑ p ∈ monoOrbit (ofParts La : MultiIndex (n + 1)), ∑ q ∈ monoOrbit (ofParts Lb),
            (∏ m, ((p m + q m).factorial : ℚ)) * (∑ i, gWeight (p i) (q i))))
      = ((n + 1 - La.length).factorial : ℚ) * ((n + 1 - Lb.length).factorial : ℚ)
          * matchNumSum La Lb (n + 1) := by
    rw [h1, ← h2]
  exact mul_left_cancel₀ hpos.ne' hcomb

end BoundedGaps.OrbitFree

