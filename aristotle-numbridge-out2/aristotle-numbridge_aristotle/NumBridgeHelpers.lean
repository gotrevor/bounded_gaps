import Mathlib

open Finset
open scoped Nat

def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

def orbitFin (L : List ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Finset.image (fun σ : Equiv.Perm (Fin k) => fun i => (ofParts L) (σ i)) Finset.univ

def autParts (L : List ℕ) : ℕ := (L.dedup.map (fun v => (L.count v).factorial)).prod

def gWeight (a b : ℕ) : ℚ :=
  ((a + b + 2).factorial : ℚ) / ((a + 1) * (b + 1) * (a + b).factorial : ℚ)

def matchDataN : List ℕ → List ℕ → List (ℕ × ℕ × ℚ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod, (Lb.map (fun b => gWeight 0 b)).sum)]
  | (a :: La), Lb =>
      (matchDataN La Lb).map (fun t => (t.1, a.factorial * t.2.1, gWeight a 0 + t.2.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchDataN La (Lb.eraseIdx jb.1)).map
            (fun t => (t.1 + 1, (a + jb.2).factorial * t.2.1, gWeight a jb.2 + t.2.2)))

def matchNumSum (La Lb : List ℕ) (k : ℕ) : ℚ :=
  ((matchDataN La Lb).map (fun t =>
    let T := La.length + Lb.length - t.1
    (k.descFactorial T : ℚ) * t.2.1 * (t.2.2 + (k - T : ℕ) * gWeight 0 0))).sum

/-! ## Proved helper lemmas -/

lemma autParts_nil : autParts [] = 1 := by rfl

lemma orbitFin_nil (k : ℕ) :
    orbitFin [] k = {fun _ => 0} := by
  ext f; simp [orbitFin, ofParts]; exact eq_comm

lemma prod_factorial_perm_invariant {k : ℕ} (f : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    ∏ i, ((f (σ i)).factorial : ℚ) = ∏ i, ((f i).factorial : ℚ) := by
  conv_rhs => rw [← Equiv.prod_comp σ]

lemma sum_gWeight_perm_invariant {k : ℕ} (f : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    ∑ i, gWeight 0 (f (σ i)) = ∑ i, gWeight 0 (f i) := by
  conv_rhs => rw [← Equiv.sum_comp σ]

lemma orbit_prod_eq (L : List ℕ) (k : ℕ) (q : Fin k → ℕ) (hq : q ∈ orbitFin L k) :
    ∏ i : Fin k, ((q i).factorial : ℚ) = ∏ i : Fin k, ((ofParts L i).factorial : ℚ) := by
  obtain ⟨σ, hσ⟩ := Finset.mem_image.mp hq
  convert prod_factorial_perm_invariant (ofParts L) σ using 1; aesop

lemma orbit_gsum_eq (L : List ℕ) (k : ℕ) (q : Fin k → ℕ) (hq : q ∈ orbitFin L k) :
    ∑ i : Fin k, gWeight 0 (q i) = ∑ i : Fin k, gWeight 0 (ofParts L i) := by
  obtain ⟨σ, hσ⟩ := Finset.mem_image.mp hq
  rw [← hσ.2, sum_gWeight_perm_invariant]

lemma prod_ofParts_factorial (L : List ℕ) (k : ℕ) (hlen : L.length ≤ k) :
    ∏ i : Fin k, ((ofParts L i).factorial : ℚ) = (L.map Nat.factorial).prod := by
  induction' k with k ih generalizing L
  · cases L <;> aesop
  · rcases L with (_ | ⟨a, L⟩) <;> simp_all +decide [Fin.prod_univ_succ, ofParts]

lemma sum_gWeight_ofParts (L : List ℕ) (k : ℕ) (hlen : L.length ≤ k) :
    (∑ i : Fin k, gWeight 0 (ofParts L i) : ℚ) =
    (L.map (fun b => gWeight 0 b)).sum + (k - L.length : ℕ) * gWeight 0 0 := by
  induction' k with k ihk generalizing L
  · cases L <;> aesop
  · rcases L with (_ | ⟨a, L⟩) <;> simp_all +decide [Fin.sum_univ_succ, ofParts]
    ring

/-! ## Orbit-stabilizer sub-lemmas -/

/-
All fibers of the orbit map have the same size.
-/
lemma fiber_size_constant (L : List ℕ) (k : ℕ)
    (f : Fin k → ℕ) (hf : f ∈ orbitFin L k) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
      (fun i => ofParts L (σ i)) = f)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
      (fun i => ofParts L (σ i)) = (fun i => ofParts L i))).card := by
  -- By definition of $f$ being in the orbit of $L$, there exists a permutation $\sigma_0$ such that $f = \text{ofParts } L \circ \sigma_0$.
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Equiv.Perm (Fin k), f = fun i => ofParts L (σ₀ i) := by
    unfold orbitFin at hf; aesop;
  fapply Finset.card_bij (fun σ _ => σ * σ₀⁻¹);
  · simp +contextual [ funext_iff, hσ₀ ];
  · aesop;
  · simp +decide [ funext_iff, hσ₀ ];
    intro b hb; use b * σ₀; aesop;

/-
Size of the stabilizer of `ofParts L` under the permutation action.
The stabilizer consists of permutations that map each position to another position with the
same value. Its size is `autParts L * (k - L.length)!`.
-/
set_option maxHeartbeats 800000 in
lemma stabilizer_size (L : List ℕ) (k : ℕ) (hlen : L.length ≤ k)
    (hpos : ∀ x ∈ L, 0 < x) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
      (fun i => ofParts L (σ i)) = (fun i => ofParts L i))).card =
    autParts L * (k - L.length).factorial := by
  induction' k with k ih generalizing L;
  · cases L <;> aesop;
  · rcases L with ( _ | ⟨ a, L ⟩ ) <;> simp_all +decide;
    · simp +decide [ ofParts, autParts ];
      simp +decide [ Fintype.card_perm ];
    · -- We split the stabilizer into two parts: the permutations that fix `0` and those that do not.
      have h_split : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin (k + 1)) => (fun i => ofParts (a :: L) (σ i)) = (fun i => ofParts (a :: L) i)) Finset.univ) =
        Finset.card (Finset.filter (fun i : Fin (k + 1) => ofParts (a :: L) i = a) Finset.univ) *
        Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin k) => (fun i => ofParts L (σ i)) = (fun i => ofParts L i)) Finset.univ) := by
          have h_split : Finset.filter (fun σ : Equiv.Perm (Fin (k + 1)) => (fun i => ofParts (a :: L) (σ i)) = (fun i => ofParts (a :: L) i)) Finset.univ =
            Finset.biUnion (Finset.filter (fun i : Fin (k + 1) => ofParts (a :: L) i = a) Finset.univ) (fun i => Finset.image (fun σ : Equiv.Perm (Fin (k + 1)) => σ * Equiv.swap 0 i) (Finset.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = 0 ∧ (fun i => ofParts (a :: L) (σ i)) = (fun i => ofParts (a :: L) i)) Finset.univ)) := by
              ext σ; simp +decide [ funext_iff ] ;
              constructor;
              · intro hσ
                obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), σ i = 0 ∧ ofParts (a :: L) i = a := by
                  use σ.symm 0; simp [hσ];
                  convert hσ ( σ.symm 0 ) |> Eq.symm using 1 ; simp +decide [ ofParts ];
                grind;
              · rintro ⟨ i, hi, hi', hi'' ⟩ x; specialize hi'' ( Equiv.swap 0 i x ) ; aesop;
          rw [ h_split, Finset.card_biUnion ];
          · rw [ Finset.sum_congr rfl fun x hx => Finset.card_image_of_injective _ fun y z h => by simpa using h ] ; simp +decide [ mul_comm ];
            refine Or.inl <| Finset.card_bij ( fun σ hσ => ?_ ) ?_ ?_ ?_;
            exact Equiv.ofBijective ( fun i => Fin.pred ( σ ( Fin.succ i ) ) ( by
              intro h; have := σ.injective ( h.trans ( Finset.mem_filter.mp hσ |>.2.1.symm ) ) ; aesop; ) ) ⟨ by
              intro i j hij; simp_all +decide [ Fin.pred_eq_iff_eq_succ ] ;, by
              intro x; use Fin.pred ( σ.symm ( Fin.succ x ) ) ( by
                grind ) ; simp +decide [ Fin.ext_iff ] ; ⟩;
            · simp +decide [ funext_iff, Fin.forall_fin_succ ];
              grind +locals;
            · simp +decide [ funext_iff, Equiv.Perm.ext_iff ];
              intro σ₁ hσ₁ hσ₁' σ₂ hσ₂ hσ₂' hσ₁₂ x; induction x using Fin.inductionOn <;> aesop;
            · intro σ hσ; use Equiv.ofBijective ( fun i => Fin.cases 0 ( fun i => Fin.succ ( σ i ) ) i ) ⟨ by
                intro i j; induction i using Fin.inductionOn <;> induction j using Fin.inductionOn <;> simp +decide [ * ] ;
                exact fun h => absurd h ( ne_of_lt ( Fin.succ_pos _ ) ), by
                intro x; induction x using Fin.inductionOn <;> simp +decide [ * ] ;
                · exact ⟨ 0, rfl ⟩;
                · exact ⟨ Fin.succ ( σ.symm ‹_› ), by simp +decide ⟩ ⟩ ; simp +decide [ funext_iff, Fin.forall_fin_succ ] at hσ ⊢;
              exact ⟨ fun i => by simpa [ ofParts ] using hσ i, by ext; rfl ⟩;
          · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
            intro σ hi₁ hi₂ hj₁ hj₂; have := σ.injective ( hi₁.trans hj₁.symm ) ; aesop;
      -- The number of positions `i` such that `ofParts (a :: L) i = a` is equal to `1 + List.count a L`.
      have h_count : Finset.card (Finset.filter (fun i : Fin (k + 1) => ofParts (a :: L) i = a) Finset.univ) = 1 + List.count a L := by
        have h_count : Finset.card (Finset.filter (fun i : Fin (k + 1) => ofParts (a :: L) i = a) Finset.univ) = Finset.card (Finset.filter (fun i : Fin (L.length + 1) => ofParts (a :: L) i = a) Finset.univ) := by
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : Fin ( L.length + 1 ) => Fin.castLE ( by linarith ) i ) Finset.univ ) ) ];
          · rw [ Finset.sum_image ] ; aesop;
            exact fun i _ j _ hij => by simpa [ Fin.ext_iff ] using hij;
          · simp +decide [ Fin.ext_iff, ofParts ];
            intro x hx; contrapose! hx;
            use ⟨ x.val, by
              grind ⟩;
        convert congr_arg Finset.card ( show Finset.filter ( fun i : Fin ( L.length + 1 ) => ofParts ( a :: L ) i = a ) Finset.univ = Finset.image ( fun i : Fin ( L.length ) => Fin.succ i ) ( Finset.filter ( fun i : Fin ( L.length ) => L[i] = a ) Finset.univ ) ∪ { 0 } from ?_ ) using 1;
        · rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
          rw [ add_comm, Finset.card_filter ];
          have h_count : ∀ (L : List ℕ), List.count a L = ∑ i ∈ Finset.range L.length, if L[i]! = a then 1 else 0 := by
            intro L; induction L <;> simp +decide [ *, Finset.sum_range_succ' ] ;
            rw [ Finset.card_filter ];
            rw [ Finset.sum_range_succ' ] ; aesop;
          rw [ h_count, Finset.sum_range ];
          grind;
        · ext ( _ | i ) <;> simp +decide [ ofParts ];
          constructor <;> intro h;
          · exact ⟨ ⟨ i, by linarith ⟩, by simpa [ List.getElem?_eq_getElem ( by linarith : i < L.length ) ] using h, rfl ⟩;
          · grind;
      simp_all +decide [ autParts ];
      by_cases ha : a ∈ L <;> simp_all +decide [ List.count_cons ];
      · have h_prod : (List.map (fun v => (List.count v L + if a = v then 1 else 0)!) L.dedup).prod = (List.map (fun v => (List.count v L)!) L.dedup).prod * (1 + List.count a L) := by
          have h_split : (List.map (fun v => (List.count v L + if a = v then 1 else 0)!) L.dedup).prod = (∏ v ∈ L.dedup.toFinset, (List.count v L + if a = v then 1 else 0)!) := by
            rw [ List.prod_toFinset ];
            exact List.nodup_dedup _
          rw [ h_split, Finset.prod_eq_mul_prod_diff_singleton <| show a ∈ L.dedup.toFinset from by aesop ] ; ring;
          rw [ show ( List.map ( fun v => ( List.count v L ) ! ) L.dedup ).prod = ( ∏ x ∈ L.dedup.toFinset, ( List.count x L ) ! ) from ?_ ];
          · rw [ Finset.prod_eq_prod_diff_singleton_mul <| show a ∈ L.dedup.toFinset from by aesop ] ; simp +decide [ Nat.factorial_succ, mul_comm, mul_assoc, mul_left_comm, Finset.prod_mul_distrib ] ; ring;
            exact congrArg₂ ( · + · ) ( by rw [ Finset.prod_congr rfl ] ; intros x hx; aesop ) ( by rw [ Finset.prod_congr rfl ] ; intros x hx; aesop );
          · rw [ List.prod_toFinset ];
            exact List.nodup_dedup _;
        rw [ h_prod, mul_comm ];
        ring;
      · simp_all +decide [ List.count_eq_zero_of_not_mem ha, add_comm ];
        exact Or.inl ( by rw [ List.map_congr_left ] ; aesop )

/-- Combining fiber_size_constant and stabilizer_size. -/
lemma orbit_fiber_size (L : List ℕ) (k : ℕ) (hlen : L.length ≤ k)
    (hpos : ∀ x ∈ L, 0 < x) :
    ∀ f ∈ orbitFin L k,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
        (fun i => ofParts L (σ i)) = f)).card = autParts L * (k - L.length).factorial := by
  intro f hf
  rw [fiber_size_constant L k f hf, stabilizer_size L k hlen hpos]

/-- Orbit-stabilizer: `autParts L * (orbitFin L k).card = k.descFactorial L.length` -/
lemma orbit_stabilizer (L : List ℕ) (k : ℕ) (hlen : L.length ≤ k)
    (hpos : ∀ x ∈ L, 0 < x) :
    (autParts L : ℚ) * (orbitFin L k).card = k.descFactorial L.length := by
  rw_mod_cast [Nat.descFactorial_eq_factorial_mul_choose]
  have h1 : (Finset.univ : Finset (Equiv.Perm (Fin k))).card =
      ∑ f ∈ orbitFin L k,
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
          (fun i => ofParts L (σ i)) = f)).card := by
    simp +decide only [card_filter]
    rw [Finset.sum_comm]
    simp +decide [Finset.sum_ite]
    exact congr_arg Finset.card (Finset.ext fun x => by simp +decide [orbitFin])
  rw [Finset.sum_congr rfl fun x hx => orbit_fiber_size L k hlen hpos x hx] at h1
  norm_num [Fintype.card_perm] at *
  rw [← Nat.choose_mul_factorial_mul_factorial hlen, mul_assoc] at h1
  nlinarith [Nat.factorial_pos (k - L.length)]