import Mathlib

open Finset
open scoped Nat

def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

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

def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

axiom permDenSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permDenSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), (a + ofParts Lb j).factorial *
        (∑ e : Equiv.Perm (Fin n),
          ∏ x : Fin n, (ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial)

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
