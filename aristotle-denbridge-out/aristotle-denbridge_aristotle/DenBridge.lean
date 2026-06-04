import Mathlib

/-!
# Denominator bridge: orbit-sum of products of factorials = the matchings sum

This is the combinatorial heart of a bounded-gaps formalization. We encode a monomial's exponent
vector over `k` variables as `ofParts L i = L.getD i 0` (positive parts `L`, padded with zeros).
The "orbit" of such a vector is its set of distinct coordinate-permutations.

The Gram-matrix denominator entry is, up to a constant factorial, the **orbit sum**
`∑_{p ∈ orbit La} ∑_{q ∈ orbit Lb} ∏_i (p i + q i)!`. We claim it equals a **matchings sum** that
is independent of the enumeration: a sum over partial matchings of the parts of `La` to the parts
of `Lb`, weighted by a falling factorial `k.descFactorial T` and a product `W` of factorials.

THE IDENTITY (verified numerically — `La=[2,1], Lb=[1,1], k=3`: orbit-sum `= 132`,
`autParts La = 1`, `autParts Lb = 2`, `matchDenSum = 264 = 1·2·132`):

  `autParts La * autParts Lb * (∑_{p ∈ orbitFin La k} ∑_{q ∈ orbitFin Lb k} ∏ i, (p i + q i)!)`
    `= matchDenSum La Lb k`.

`orbitFin L k` = the image of `Fin k`-permutations acting on `ofParts L` (a `Finset (Fin k → ℕ)`,
deduplicated). `matchData` is a bijective enumeration of partial matchings (each `La`-head is left
unmatched — `×a!` — or matched to a current `Lb` entry — erase it, `×(a+b)!`, `numPairs+1`).
`autParts L = ∏_v (multiplicity of v in L)!`.

Prove `denom_bridge`. This is a genuine permanent/rook-polynomial expansion (the permanent of the
matrix `[(La_iᵢ + Lb_jⱼ)!]` grouped by overlap pattern); expect to need induction on `La` mirroring
`matchData`'s recursion, plus the orbit↔permutation bookkeeping (`autParts` accounts for repeated
parts via the orbit-stabilizer count). It is HARD — partial progress / key lemmas are valuable.
Standard mathlib; no axioms expected. (`hpos*` say the parts are positive; `hlen*` that they fit.)
-/

open Finset
open scoped Nat

/-- Padded parts-list multi-index. -/
def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

/-- The orbit of `ofParts L`: distinct coordinate-permutations, as a `Finset (Fin k → ℕ)`. -/
def orbitFin (L : List ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Finset.image (fun σ : Equiv.Perm (Fin k) => fun i => (ofParts L) (σ i)) Finset.univ

/-- `aut L = ∏_v (multiplicity of value v in L)!`. -/
def autParts (L : List ℕ) : ℕ := (L.dedup.map (fun v => (L.count v).factorial)).prod

/-- Bijective enumeration of partial matchings of `La`-parts to `Lb`-parts: `(numPairs, W)` with
`W = ∏ paired (a+b)! · ∏ unmatched a! · ∏ unmatched b!`. -/
def matchData : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod)]
  | (a :: La), Lb =>
      (matchData La Lb).map (fun pw => (pw.1, a.factorial * pw.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchData La (Lb.eraseIdx jb.1)).map (fun pw => (pw.1 + 1, (a + jb.2).factorial * pw.2)))

/-- `matchDenSum = ∑_M k.descFactorial (|La|+|Lb|-numPairs) · W(M)`. -/
def matchDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ((matchData La Lb).map
    (fun pw => k.descFactorial (La.length + Lb.length - pw.1) * pw.2)).sum

/-! ## Helper lemmas -/

lemma autParts_nil : autParts [] = 1 := by rfl

lemma orbitFin_nil (k : ℕ) : orbitFin ([] : List ℕ) k = {fun _ => 0} := by
  unfold orbitFin; ext; aesop

lemma prod_comp_perm {k : ℕ} (f : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    ∏ i, f (σ i) = ∏ i, f i :=
  Equiv.prod_comp σ f

lemma prod_ofParts_factorial {k : ℕ} (L : List ℕ) (hlen : L.length ≤ k) :
    ∏ i : Fin k, (ofParts L i).factorial = (L.map Nat.factorial).prod := by
  induction' k with k ihk generalizing L
  · cases L <;> trivial
  · rcases L with ( _ | ⟨ a, L ⟩ ) <;> simp_all +decide [ Fin.prod_univ_succ, ofParts ]

lemma orbitFin_prod_factorial_eq {k : ℕ} (L : List ℕ) (q : Fin k → ℕ)
    (hq : q ∈ orbitFin L k) (hlen : L.length ≤ k) :
    ∏ i, (q i).factorial = (L.map Nat.factorial).prod := by
  obtain ⟨ σ, hσ ⟩ := Finset.mem_image.mp hq
  simp +decide [ ← hσ.2, prod_ofParts_factorial L hlen, prod_comp_perm ]
  rw [ ← prod_ofParts_factorial L hlen ]
  exact Equiv.prod_comp σ fun i => ( ofParts L i ) !

/-! ### Orbit-stabilizer decomposition -/

/-
`autParts (a :: L) = (L.count a + 1) * autParts L` when all parts are positive.
-/
lemma autParts_cons (a : ℕ) (L : List ℕ) (ha : 0 < a) (hpos : ∀ x ∈ L, 0 < x) :
    autParts (a :: L) = (L.count a + 1) * autParts L := by
      -- By definition of `autParts`, we can split the product into two parts: one for `a` and one for the rest of the list `L`.
      have h_autParts_split : List.prod (List.map (fun v => (List.count v (a :: L)).factorial) (List.dedup (a :: L))) = List.prod (List.map (fun v => (List.count v L).factorial) (List.dedup L)) * (List.count a (a :: L)).factorial / (List.count a L).factorial := by
        by_cases haL : a ∈ L <;> simp_all +decide [ List.count_cons ];
        · have h_prod_split : List.prod (List.map (fun v => (List.count v L + if a = v then 1 else 0)!) (List.dedup L)) = List.prod (List.map (fun v => (List.count v L)!) (List.dedup L)) * (List.count a L + 1)! / (List.count a L)! := by
            have h_prod_split_step : ∀ {l : List ℕ}, (∀ x ∈ l, x ∈ List.dedup L) → List.prod (List.map (fun v => (List.count v L + if a = v then 1 else 0)!) l) = List.prod (List.map (fun v => (List.count v L)!) l) * (List.prod (List.map (fun v => if a = v then (List.count v L + 1)! / (List.count v L)! else 1) l)) := by
              intros l hl; induction l <;> simp_all +decide [ Nat.factorial_ne_zero, Nat.factorial_succ ] ;
              split_ifs <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm ]
            convert h_prod_split_step fun x hx => hx using 1;
            rw [ Nat.div_eq_of_eq_mul_left ] <;> norm_num [ Nat.factorial_pos ];
            simp +decide [ mul_assoc, Nat.factorial_ne_zero ];
            rw [ List.prod_map_eq_pow_single a ] <;> simp +contextual [ Nat.factorial_ne_zero ];
            · rw [ List.count_dedup ];
              rw [ if_pos haL, pow_one, Nat.div_mul_cancel ( Nat.factorial_dvd_factorial ( Nat.le_succ _ ) ) ];
            · grind +qlia;
          exact h_prod_split;
        · simp_all +decide [ List.count_eq_zero_of_not_mem, mul_comm ];
          exact congr_arg _ ( List.map_congr_left fun x hx => by aesop );
      simp_all +decide [ Nat.factorial_succ, autParts ];
      exact Nat.div_eq_of_eq_mul_left ( Nat.factorial_pos _ ) ( by ring )

/-
Orbit count of a positive value v: the number of positions i with f i = v,
for f in the orbit, equals L.count v.
-/
lemma orbit_count_val {k : ℕ} (L : List ℕ) (f : Fin k → ℕ)
    (hf : f ∈ orbitFin L k) (v : ℕ) (hv : 0 < v) (hlen : L.length ≤ k)
    (hpos : ∀ x ∈ L, 0 < x) :
    (Finset.univ.filter (fun i => f i = v)).card = L.count v := by
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), ∀ i, f i = ofParts L (σ i) := by
        unfold orbitFin at hf; aesop;
      have h_card_eq : Finset.card (Finset.filter (fun i => ofParts L i = v) (Finset.univ : Finset (Fin k))) = List.count v L := by
        have h_count : Finset.card (Finset.filter (fun i => ofParts L i = v) (Finset.univ : Finset (Fin k))) = Finset.card (Finset.filter (fun i => L[i]! = v) (Finset.range L.length)) := by
          refine' Finset.card_bij ( fun i hi => i ) _ _ _ <;> simp +decide [ Fin.ext_iff, ofParts ];
          · grind;
          · exact fun b hb hb' => ⟨ ⟨ b, by linarith ⟩, hb', rfl ⟩;
        have h_count_eq : ∀ {L : List ℕ}, (∀ x ∈ L, 0 < x) → List.count v L = Finset.card (Finset.filter (fun i => L[i]! = v) (Finset.range L.length)) := by
          intros L hpos; induction' L with hd tl ih <;> simp_all +decide [ List.count_cons ] ;
          rw [ Finset.card_filter, Finset.card_filter ];
          rw [ Finset.sum_range_succ' ] ; aesop;
        rw [ h_count, h_count_eq hpos ];
      rw [ ← h_card_eq, Finset.card_filter, Finset.card_filter ];
      conv_rhs => rw [ ← Equiv.sum_comp σ ] ;
      aesop

/-
Orbit count of zero: the number of zero positions equals k - L.length.
-/
lemma orbit_count_zero {k : ℕ} (L : List ℕ) (f : Fin k → ℕ)
    (hf : f ∈ orbitFin L k) (hlen : L.length ≤ k) (hpos : ∀ x ∈ L, 0 < x) :
    (Finset.univ.filter (fun i => f i = 0)).card = k - L.length := by
      -- By definition of `orbitFin`, there exists a permutation `σ` such that `f = ofParts L ∘ σ`.
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), f = ofParts L ∘ σ := by
        unfold orbitFin at hf; aesop;
      -- Since `σ` is a permutation, the set of indices where `f i = 0` is the same as the set of indices where `ofParts L j = 0`.
      have h_set_eq : Finset.filter (fun i => f i = 0) Finset.univ = Finset.image (fun j => σ.symm j) (Finset.filter (fun j => ofParts L j = 0) Finset.univ) := by
        ext i; aesop;
      -- The set of indices where `ofParts L j = 0` is exactly the set of indices `j` such that `j ≥ L.length`.
      have h_set_zero : Finset.filter (fun j => ofParts L j = 0) Finset.univ = Finset.univ \ Finset.image (fun i : Fin L.length => Fin.castLE hlen i) Finset.univ := by
        ext j; simp [ofParts];
        by_cases hj : j.val < L.length <;> simp_all +decide [ Fin.ext_iff ];
        · exact iff_of_false ( ne_of_gt ( hpos _ ( by simp ) ) ) fun h => h ⟨ j, hj ⟩ rfl;
        · exact fun x => ne_of_lt ( lt_of_lt_of_le x.2 hj );
      simp_all +decide [ Finset.card_sdiff, Finset.card_image_of_injective, Function.Injective ]

/-
Characterization of orbit membership: `f ∈ orbitFin L k` iff for each value `v`,
the number of `i` with `f i = v` equals the number of `j` with `ofParts L j = v`.
-/
lemma mem_orbitFin_iff_count {k : ℕ} (L : List ℕ) (f : Fin k → ℕ) :
    f ∈ orbitFin L k ↔
      ∀ v : ℕ, ((Finset.univ : Finset (Fin k)).filter (fun i => f i = v)).card =
               ((Finset.univ : Finset (Fin k)).filter (fun i => ofParts L i = v)).card := by
                 constructor <;> intro h <;> simp_all +decide [ orbitFin ];
                 · obtain ⟨ a, rfl ⟩ := h; intro v; rw [ Finset.card_filter, Finset.card_filter ] ;
                   conv_rhs => rw [ ← Equiv.sum_comp a ] ;
                 · -- By definition of $ofParts$, we know that $ofParts L$ is a function from $Fin k$ to $ℕ$.
                   set g : Fin k → ℕ := ofParts L;
                   -- Since $f$ and $g$ have the same counts for each value, there exists a bijection $\sigma$ between the indices such that $f(i) = g(\sigma(i))$ for all $i$.
                   have h_bij : ∃ σ : Fin k ≃ Fin k, ∀ i, f i = g (σ i) := by
                     have h_eq_counts : ∀ v, Finset.card (Finset.filter (fun i => f i = v) Finset.univ) = Finset.card (Finset.filter (fun i => g i = v) Finset.univ) := by
                       assumption
                     -- By definition of $f$ and $g$, we can construct a bijection $\sigma$ between the indices such that $f(i) = g(\sigma(i))$ for all $i$.
                     have h_bij : ∃ σ : Fin k → Fin k, Function.Injective σ ∧ ∀ i, f i = g (σ i) := by
                       have h_bij : ∀ (v : ℕ), ∃ σ : Finset.filter (fun i => f i = v) Finset.univ → Finset.filter (fun i => g i = v) Finset.univ, Function.Injective σ := by
                         intro v
                         have h_card_eq : Finset.card (Finset.filter (fun i => f i = v) Finset.univ) = Finset.card (Finset.filter (fun i => g i = v) Finset.univ) := h_eq_counts v
                         generalize_proofs at *; (
                         have h_bij : Nonempty (Finset.filter (fun i => f i = v) Finset.univ ≃ Finset.filter (fun i => g i = v) Finset.univ) := by
                           exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_card_eq ⟩
                         generalize_proofs at *; (
                         exact ⟨ _, h_bij.some.injective ⟩))
                       generalize_proofs at *; (
                       choose σ hσ using h_bij
                       generalize_proofs at *; (
                       use fun i => σ (f i) ⟨i, by
                         grind +revert⟩
                       generalize_proofs at *; (
                       refine' ⟨ _, _ ⟩
                       all_goals generalize_proofs at *;
                       · intro i j hij; have := hσ ( f i ) ; have := hσ ( f j ) ; simp_all +decide [ Function.Injective.eq_iff ] ;
                         grind;
                       · grind +splitIndPred)))
                     generalize_proofs at *; (
                     exact ⟨ Equiv.ofBijective h_bij.choose ( ⟨ h_bij.choose_spec.1, Finite.injective_iff_surjective.mp h_bij.choose_spec.1 ⟩ ), h_bij.choose_spec.2 ⟩)
                   generalize_proofs at *; (
                   exact ⟨ h_bij.choose, funext fun i => h_bij.choose_spec i ▸ rfl ⟩)

/-
Removing one occurrence of `a` from an orbit element of `(a :: L)` yields an orbit element of `L`.
-/
lemma orbit_update_zero_mem {k : ℕ} (a : ℕ) (L : List ℕ) (f : Fin k → ℕ) (j : Fin k)
    (hf : f ∈ orbitFin (a :: L) k) (hj : f j = a) (ha : 0 < a)
    (hlen : L.length < k) (hpos : ∀ x ∈ L, 0 < x) :
    Function.update f j 0 ∈ orbitFin L k := by
      convert mem_orbitFin_iff_count L ( Function.update f j 0 ) |>.2 ?_;
      intro v
      by_cases hv : v = a;
      · have h_count_a : ((Finset.univ : Finset (Fin k)).filter (fun i => f i = a)).card = L.count a + 1 := by
          convert orbit_count_val ( a :: L ) f hf a ha ( by simpa ) ( by aesop ) using 1;
          rw [ List.count_cons ] ; aesop;
        have h_count_L : ((Finset.univ : Finset (Fin k)).filter (fun i => ofParts L i = a)).card = L.count a := by
          convert orbit_count_val L ( fun i => L.getD i 0 ) _ a ha _ hpos using 1;
          · exact Finset.mem_image.mpr ⟨ Equiv.refl _, Finset.mem_univ _, rfl ⟩;
          · grind;
        simp_all +decide [ Finset.filter_congr, Function.update_apply ];
        rw [ show ( Finset.filter ( fun i => ( if i = j then 0 else f i ) = a ) Finset.univ ) = Finset.filter ( fun i => f i = a ) Finset.univ \ { j } from ?_, Finset.card_sdiff ] <;> aesop;
      · by_cases hv0 : v = 0 <;> simp_all +decide [ Function.update_apply ];
        · convert congr_arg ( fun x : ℕ => x + 1 ) ( orbit_count_zero ( a :: L ) f hf ( by simpa using by linarith ) ( by aesop ) ) using 1;
          · rw [ show ( Finset.univ.filter fun i => ¬i = j → f i = 0 ) = Finset.univ.filter ( fun i => f i = 0 ) ∪ { j } from ?_, Finset.card_union ] <;> norm_num [ Finset.filter_ne', Finset.filter_eq', hj ];
            · rw [ Finset.inter_singleton ] ; aesop;
            · grind;
          · convert orbit_count_zero L ( fun i => ofParts L i ) _ _ _ using 1;
            · grind;
            · exact Finset.mem_image.mpr ⟨ Equiv.refl _, Finset.mem_univ _, rfl ⟩;
            · linarith;
            · assumption;
        · convert orbit_count_val ( a :: L ) f hf v ( Nat.pos_of_ne_zero hv0 ) ( by simpa using hlen ) ( by aesop ) using 1;
          · congr 1 with i ; aesop;
          · convert orbit_count_val L ( fun i => L.getD i 0 ) ?_ v ( Nat.pos_of_ne_zero hv0 ) ?_ hpos using 1;
            · rw [ List.count_cons_of_ne ] ; aesop;
            · exact Finset.mem_image.mpr ⟨ Equiv.refl _, Finset.mem_univ _, rfl ⟩;
            · linarith

/-
Inserting `a` at a zero position of an orbit element of `L` yields an orbit element of `(a :: L)`.
-/
lemma orbit_update_val_mem {k : ℕ} (a : ℕ) (L : List ℕ) (g : Fin k → ℕ) (j : Fin k)
    (hg : g ∈ orbitFin L k) (hj : g j = 0) (ha : 0 < a)
    (hlen : L.length < k) (hpos : ∀ x ∈ L, 0 < x) :
    Function.update g j a ∈ orbitFin (a :: L) k := by
      convert mem_orbitFin_iff_count ( a :: L ) ( Function.update g j a ) |>.2 _;
      intro v
      by_cases hv : v = a;
      · -- For v = a, count the number of i in the updated function where Function.update g j a i = a.
        have h_count_a : Finset.card (Finset.filter (fun i => Function.update g j a i = a) Finset.univ) = L.count a + 1 := by
          have h_count_a : Finset.card (Finset.filter (fun i => Function.update g j a i = a) Finset.univ) = Finset.card (Finset.filter (fun i => g i = a) Finset.univ) + 1 := by
            rw [ show ( Finset.filter ( fun i => Function.update g j a i = a ) Finset.univ ) = Finset.filter ( fun i => g i = a ) Finset.univ ∪ { j } from ?_, Finset.card_union ] <;> norm_num [ hj, ha.ne' ];
            · rw [ Finset.inter_singleton ] ; aesop;
            · grind;
          rw [ h_count_a, orbit_count_val L g hg a ha ( by linarith ) hpos ];
        convert h_count_a using 1;
        · rw [ hv ];
        · convert orbit_count_val ( a :: L ) ( ofParts ( a :: L ) ) _ a ha _ using 1;
          any_goals exact k;
          · simp_all +decide [ List.count_cons ];
          · exact Finset.mem_image.mpr ⟨ Equiv.refl _, Finset.mem_univ _, rfl ⟩;
          · grind;
      · by_cases hv' : v = 0 <;> simp_all +decide [ Finset.ext_iff, Function.update_apply ];
        · have h_count_zero : (Finset.univ.filter (fun i => g i = 0)).card = k - L.length := by
            convert orbit_count_zero L g hg ( by linarith ) hpos using 1;
          convert congr_arg ( · - 1 ) h_count_zero using 1;
          · rw [ show ( Finset.univ.filter fun i => ( if i = j then a else g i ) = 0 ) = Finset.univ.filter ( fun i => g i = 0 ) \ { j } from ?_, Finset.card_sdiff ] <;> aesop;
          · convert orbit_count_zero ( a :: L ) ( fun i => ofParts ( a :: L ) i ) _ _ _ using 1;
            · exact Finset.mem_image.mpr ⟨ Equiv.refl _, Finset.mem_univ _, rfl ⟩;
            · grind;
            · aesop;
        · -- By mem_orbitFin_iff_count applied to hg, for all v, the count of v in g equals the count of v in ofParts L.
          have h_count_eq : ∀ v, ((Finset.univ : Finset (Fin k)).filter (fun i => g i = v)).card = ((Finset.univ : Finset (Fin k)).filter (fun i => ofParts L i = v)).card := by
            exact fun v => mem_orbitFin_iff_count _ _ |>.1 hg v;
          convert h_count_eq v using 1;
          · congr 1 with i ; aesop;
          · refine' Finset.card_bij ( fun i hi => ⟨ i - 1, _ ⟩ ) _ _ _ <;> simp_all +decide [ Fin.ext_iff, ofParts ];
            · exact lt_of_le_of_lt ( Nat.pred_le _ ) i.2;
            · grind +splitImp;
            · grind;
            · intro b hb; use ⟨ b + 1, by
                grind ⟩ ; aesop;

/-
Orbit size recursion: adding element `a` to `L` multiplied by its new multiplicity
gives `(k - L.length)` times the old orbit size.
-/
lemma orbit_card_cons (a : ℕ) (L : List ℕ) (k : ℕ) (ha : 0 < a)
    (hlen : L.length < k) (hpos : ∀ x ∈ L, 0 < x) :
    (L.count a + 1) * (orbitFin (a :: L) k).card = (k - L.length) * (orbitFin L k).card := by
  revert a;
  intro a ha
  set S := Finset.biUnion (orbitFin (a :: L) k) (fun f => Finset.image (fun j => (f, j)) (Finset.univ.filter (fun j => f j = a))) with hS_def
  have hS_card : S.card = (orbitFin (a :: L) k).card * (L.count a + 1) := by
    rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => Finset.card_image_of_injective _ fun y z h => by injection h ];
      rw [ Finset.sum_const_nat ];
      intro f hf; have := orbit_count_val ( a :: L ) f hf a ha; aesop;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
  -- Define the bijection between S and T.
  have h_bij : S = Finset.biUnion (orbitFin L k) (fun g => Finset.image (fun j => (Function.update g j a, j)) (Finset.univ.filter (fun j => g j = 0))) := by
    ext ⟨f, j⟩; simp [S, hS_def];
    constructor <;> intro h;
    · use Function.update f j 0;
      exact ⟨ orbit_update_zero_mem a L f j h.1 h.2 ha hlen hpos, by simp +decide, by ext i; by_cases hi : i = j <;> aesop ⟩;
    · rcases h with ⟨ g, hg₁, hg₂, rfl ⟩ ; exact ⟨ orbit_update_val_mem a L g j hg₁ hg₂ ha hlen hpos, by simp +decide [ hg₂ ] ⟩ ;
  -- By definition of $T$, we know that its cardinality is $(orbitFin L k).card * (k - L.length)$.
  have hT_card : S.card = (orbitFin L k).card * (k - L.length) := by
    rw [ h_bij, Finset.card_biUnion ];
    · rw [ Finset.sum_const_nat ];
      intro g hg; rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; rw [ ← orbit_count_zero L g hg ( by linarith ) hpos ] ;
    · intros g hg g' hg' hgg'; simp_all +decide [ Finset.disjoint_left ] ;
      intro i hi j hj hij; contrapose! hgg'; ext x; by_cases hx : x = i <;> by_cases hx' : x = j <;> simp_all +decide [ Function.update_apply ] ;
      replace hij := congr_fun hij x; aesop;
  grind

/-- **Orbit-stabilizer counting**: `autParts L * |orbitFin L k| = k.descFactorial L.length`. -/
lemma orbit_card_mul_aut (L : List ℕ) (k : ℕ)
    (hlen : L.length ≤ k) (hpos : ∀ x ∈ L, 0 < x) :
    autParts L * (orbitFin L k).card = k.descFactorial L.length := by
  induction L with
  | nil =>
    simp [autParts_nil, orbitFin_nil, Finset.card_singleton, Nat.descFactorial_zero]
  | cons a L ih =>
    have hapos : 0 < a := hpos a List.mem_cons_self
    have hposL : ∀ x ∈ L, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hlenL : L.length ≤ k := Nat.le_of_succ_le hlen
    have hlenLk : L.length < k := Nat.lt_of_succ_le hlen
    rw [autParts_cons a L hapos hposL]
    simp only [List.length_cons]
    rw [Nat.descFactorial_succ]
    -- Need: (L.count a + 1) * autParts L * (orbitFin (a :: L) k).card
    --     = (k - L.length) * k.descFactorial L.length
    calc (L.count a + 1) * autParts L * (orbitFin (a :: L) k).card
        = autParts L * ((L.count a + 1) * (orbitFin (a :: L) k).card) := by ring
      _ = autParts L * ((k - L.length) * (orbitFin L k).card) := by
            rw [orbit_card_cons a L k hapos hlenLk hposL]
      _ = (k - L.length) * (autParts L * (orbitFin L k).card) := by ring
      _ = (k - L.length) * k.descFactorial L.length := by rw [ih hlenL hposL]

/-! ### Base case -/

lemma denom_bridge_nil (Lb : List ℕ) (k : ℕ) (hlenB : Lb.length ≤ k)
    (hposB : ∀ x ∈ Lb, 0 < x) :
    autParts [] * autParts Lb *
      (∑ p ∈ orbitFin [] k, ∑ q ∈ orbitFin Lb k, ∏ i, (p i + q i).factorial)
      = matchDenSum [] Lb k := by
  rw [orbitFin_nil]
  simp +zetaDelta at *
  rw [Finset.sum_congr rfl fun x hx => orbitFin_prod_factorial_eq Lb x hx hlenB]
  simp +decide [autParts_nil, orbit_card_mul_aut Lb k hlenB hposB, matchDenSum]
  convert congr_arg (· * (List.map Nat.factorial Lb |> List.prod))
    (orbit_card_mul_aut Lb k hlenB hposB) using 1
  ring!

/-! ### Permutation sum approach -/

/-- The sum over all permutations of the product of factorials. -/
def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

/-
Orbit-stabilizer for sums: the weighted orbit sum equals the permutation sum
up to stabilizer scaling.
-/
lemma orbit_sum_eq_perm_sum {k : ℕ} (L : List ℕ) (f : (Fin k → ℕ) → ℕ)
    (hlen : L.length ≤ k) (hpos : ∀ x ∈ L, 0 < x) :
    autParts L * (k - L.length).factorial * ∑ p ∈ orbitFin L k, f p =
      ∑ σ : Equiv.Perm (Fin k), f (fun i => ofParts L (σ i)) := by
        rw [ Finset.mul_sum _ _ _ ];
        rw [ ← Finset.sum_congr rfl fun x hx => ?_ ];
        swap;
        exact fun x => ∑ σ : Equiv.Perm ( Fin k ), if ( fun i => ofParts L ( σ i ) ) = x then f x else 0;
        · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
          unfold orbitFin; aesop;
        · simp +decide [ Finset.sum_ite ];
          have h_orbit_stabilizer : ∀ p ∈ orbitFin L k, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin k) => (fun i => ofParts L (σ i)) = p) Finset.univ) = Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin k) => (fun i => ofParts L (σ i)) = ofParts L) Finset.univ) := by
            intro p hp
            obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin k), (fun i => ofParts L (σ i)) = p := by
              unfold orbitFin at hp; aesop;
            refine' Finset.card_bij ( fun τ hτ => τ * σ⁻¹ ) _ _ _ <;> simp_all +decide [ funext_iff ];
            · grind;
            · intro b hb; use b * σ; aesop;
          have h_orbit_stabilizer : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin k) => (fun i => ofParts L (σ i)) = ofParts L) Finset.univ) * (orbitFin L k).card = Nat.factorial k := by
            have h_orbit_stabilizer : ∑ p ∈ orbitFin L k, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin k) => (fun i => ofParts L (σ i)) = p) Finset.univ) = Nat.factorial k := by
              rw [ ← Finset.card_biUnion ];
              · convert Finset.card_univ ( α := Equiv.Perm ( Fin k ) ) using 2;
                · ext σ; simp [orbitFin];
                · simp +decide [ Fintype.card_perm ];
              · exact fun p hp q hq hpq => Finset.disjoint_left.mpr fun σ hσ₁ hσ₂ => hpq <| by aesop;
            rw [ ← h_orbit_stabilizer, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
          have h_orbit_stabilizer : autParts L * (orbitFin L k).card = Nat.descFactorial k L.length := by
            convert orbit_card_mul_aut L k hlen hpos using 1;
          simp_all +decide [ Nat.descFactorial_eq_factorial_mul_choose ];
          rw [ ← Nat.choose_mul_factorial_mul_factorial hlen ] at *;
          exact Or.inl ( mul_left_cancel₀ ( show ( orbitFin L k ).card ≠ 0 from Finset.card_ne_zero_of_mem hx ) <| by nlinarith )

/-
Step 1: LHS times excess factorials equals k! * permDenSum.
-/
lemma lhs_eq_perm (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    (k - La.length).factorial * (k - Lb.length).factorial *
      (autParts La * autParts Lb *
        (∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k, ∏ i, (p i + q i).factorial))
      = k.factorial * permDenSum La Lb k := by
        -- Apply orbit_sum_eq_perm_sum with La:
        have h1 : (k - La.length)! * autParts La * ∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k, ∏ i, (p i + q i).factorial = ∑ σ : Equiv.Perm (Fin k), ∑ q ∈ orbitFin Lb k, ∏ i, ((ofParts La (σ i)) + q i).factorial := by
          convert orbit_sum_eq_perm_sum La ( fun p => ∑ q ∈ orbitFin Lb k, ∏ i, ( p i + q i ) ! ) hlenA hposA using 1 ; ring!;
        -- Apply orbit_sum_eq_perm_sum with Lb to the inner sum:
        have h2 : ∀ σ : Equiv.Perm (Fin k), (k - Lb.length)! * autParts Lb * ∑ q ∈ orbitFin Lb k, ∏ i, ((ofParts La (σ i)) + q i).factorial = ∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La (σ i)) + (ofParts Lb (τ i))).factorial := by
          intro σ
          have := orbit_sum_eq_perm_sum Lb (fun q => ∏ i, ((ofParts La (σ i)) + q i).factorial) hlenB hposB
          simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        convert congr_arg ( fun x => ( k - Lb.length ) ! * autParts Lb * x ) h1 using 1;
        · ring;
        · rw [ Finset.mul_sum _ _ _, Finset.sum_congr rfl fun σ _ => h2 σ ];
          -- By reindexing the double sum over (σ, τ) with i ↦ σ⁻¹ i, we can simplify it to k! * permDenSum.
          have h_reindex : ∀ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La (σ i)) + (ofParts Lb (τ i))).factorial = ∑ τ : Equiv.Perm (Fin k), ∏ i, ((ofParts La i) + (ofParts Lb (τ i))).factorial := by
            intro σ;
            apply Finset.sum_bij (fun τ _ => τ * σ⁻¹);
            · simp;
            · aesop;
            · exact fun b _ => ⟨ b * σ, Finset.mem_univ _, by simp +decide ⟩;
            · intro τ _; rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ Equiv.Perm.mul_apply ] ;
          simp +decide only [h_reindex, sum_const, card_univ, Fintype.card_perm];
          simp +decide [ permDenSum ]

/-
`permDenSum [] Lb k = k! * (Lb.map (·!)).prod`
-/
lemma permDenSum_nil (Lb : List ℕ) (k : ℕ) (hlen : Lb.length ≤ k) :
    permDenSum [] Lb k = k.factorial * (Lb.map Nat.factorial).prod := by
      unfold permDenSum;
      simp +decide [ ofParts ];
      have h_prod : ∀ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (Lb[ρ i]?.getD 0)! = (Lb.map Nat.factorial).prod := by
        intro ρ
        have h_perm : ∏ i : Fin k, (Lb[ρ i]?.getD 0)! = ∏ i : Fin k, (Lb.getD i 0)! := by
          convert Equiv.prod_comp ρ fun i => ( Lb.getD ( i : Fin k ) 0 ) ! using 1;
        convert prod_ofParts_factorial Lb hlen using 1;
      simp_all +decide [ Finset.card_univ, Fintype.card_perm ]

/-- `n.descFactorial m * (n - m)! = n!` -/
lemma descFactorial_mul_factorial (n m : ℕ) (h : m ≤ n) :
    n.descFactorial m * (n - m).factorial = n.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ]
    have hm : m ≤ n := Nat.le_of_succ_le h
    have hsub : n - (m + 1) + 1 = n - m := by omega
    calc (n - m) * n.descFactorial m * (n - (m + 1)).factorial
        = n.descFactorial m * ((n - m) * (n - (m + 1)).factorial) := by ring
      _ = n.descFactorial m * (n - m).factorial := by
            congr 1; rw [← hsub, Nat.factorial_succ, mul_comm]
      _ = n.factorial := ih hm

/-
Step 2, base case: when La = [].
-/
lemma rhs_eq_perm_nil (Lb : List ℕ) (k : ℕ)
    (hlenB : Lb.length ≤ k) (hposB : ∀ x ∈ Lb, 0 < x) :
    (k - ([] : List ℕ).length).factorial * (k - Lb.length).factorial *
      matchDenSum [] Lb k
      = k.factorial * permDenSum [] Lb k := by
        rw [ permDenSum_nil, matchDenSum ];
        · erw [ List.map_singleton, List.sum_singleton ] ; simp +decide [ Nat.descFactorial_eq_factorial_mul_choose ] ; ring!;
          rw [ ← Nat.choose_mul_factorial_mul_factorial hlenB ] ; ring;
        · assumption

/-
Laplace expansion of permDenSum along the first row (using decomposeFin).
-/
lemma permDenSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permDenSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), (a + ofParts Lb j).factorial *
        (∑ e : Equiv.Perm (Fin n),
          ∏ x : Fin n, (ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial) := by
              unfold permDenSum;
              simp +decide only [ofParts, Fin.prod_univ_succ, Finset.mul_sum _ _ _];
              rw [ ← Equiv.sum_comp ( Equiv.Perm.decomposeFin.symm ) ];
              rw [ Finset.sum_sigma' ];
              refine' Finset.sum_bij ( fun x _ => ⟨ x.1, x.2 ⟩ ) _ _ _ _ <;> aesop

/-
Key identity: `k.descFactorial (n + 1) = k * (k - 1).descFactorial n` when `n < k`.
-/
lemma descFactorial_succ_eq (k n : ℕ) (h : n < k) :
    k.descFactorial (n + 1) = k * (k - 1).descFactorial n := by
      cases k <;> cases n <;> simp_all +decide [ Nat.descFactorial ];
      rename_i k n;
      induction' n with n ih generalizing k <;> simp_all +decide [ Nat.succ_sub, Nat.descFactorial_succ ];
      · ring;
      · grind

/-
matchDenSum recursion in terms of (k-1).
-/
lemma matchDenSum_cons_eq (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : La.length + Lb.length < k) :
    matchDenSum (a :: La) Lb k =
      k * (a.factorial * matchDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * matchDenSum La (Lb.eraseIdx j) (k - 1)) := by
            unfold matchDenSum; simp +decide [ *, Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
            -- Apply the descFactorial_succ_eq lemma to rewrite the descFactorial terms.
            have h_descFactorial : ∀ pw ∈ matchData La Lb, k.descFactorial (La.length + 1 + Lb.length - pw.1) = k * (k - 1).descFactorial (La.length + Lb.length - pw.1) := by
              intros pw hpw;
              convert descFactorial_succ_eq k ( La.length + Lb.length - pw.1 ) _ using 1;
              · rw [ show La.length + 1 + Lb.length - pw.1 = La.length + Lb.length - pw.1 + 1 from tsub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show pw.1 ≤ La.length + Lb.length from by
                                                                                                                                                              have h_pw1_le : ∀ (La Lb : List ℕ) (pw : ℕ × ℕ), pw ∈ matchData La Lb → pw.1 ≤ La.length + Lb.length := by
                                                                                                                                                                intros La Lb pw hpw
                                                                                                                                                                induction' La with a La ih generalizing Lb pw;
                                                                                                                                                                · cases Lb <;> simp_all +decide [ matchData ];
                                                                                                                                                                · unfold matchData at hpw; simp +decide at hpw;
                                                                                                                                                                  grind;
                                                                                                                                                              exact h_pw1_le La Lb pw hpw ] ];
              · exact lt_of_le_of_lt ( Nat.sub_le _ _ ) hk;
            have h_descFactorial' : ∀ j ∈ List.range Lb.length, ∀ pw ∈ matchData La (Lb.eraseIdx j), k.descFactorial (La.length + Lb.length - pw.1) = k * (k - 1).descFactorial (La.length + (Lb.length - 1) - pw.1) := by
              intros j hj pw hpw
              have h_len : pw.1 ≤ La.length + (Lb.length - 1) := by
                have h_len : ∀ La Lb : List ℕ, ∀ pw ∈ matchData La Lb, pw.1 ≤ La.length + Lb.length := by
                  intros La Lb pw hpw; induction' La with a La ih generalizing Lb pw <;> simp_all +decide [ matchData ] ;
                  grind;
                grind;
              convert descFactorial_succ_eq k ( La.length + ( Lb.length - 1 ) - pw.1 ) _ using 1;
              · grind;
              · omega;
            simp +decide [ matchData, List.flatMap, List.sum_map_mul_left, List.sum_map_mul_right, h_descFactorial, h_descFactorial' ];
            congr! 1;
            · rw [ ← mul_assoc, ← List.sum_map_mul_left ];
              exact congr_arg _ ( List.map_congr_left fun x hx => by rw [ Function.comp_apply, h_descFactorial x hx ] ; ring );
            · refine' congr_arg _ ( List.ext_get _ _ ) <;> simp +decide [ Function.comp ];
              intro n hn; rw [ ← mul_assoc, ← List.sum_map_mul_left ] ; refine' congr_arg _ ( List.ext_get _ _ ) <;> simp +decide [ Function.comp ] ;
              grind

/-- Laplace expansion of permDenSum in terms of (k-1) permanents. -/
lemma permDenSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permDenSum (a :: La) Lb k =
      (k - Lb.length) * a.factorial * permDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * permDenSum La (Lb.eraseIdx j) (k - 1) := by sorry

/-- Step 2: RHS times excess factorials equals k! * permDenSum. -/
lemma rhs_eq_perm (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    (k - La.length).factorial * (k - Lb.length).factorial *
      matchDenSum La Lb k
      = k.factorial * permDenSum La Lb k := by sorry

/-- **The denominator bridge: orbit-sum of `∏(pᵢ+qᵢ)!` equals the matchings sum** (up to the
`aut` over-count from repeated parts). -/
theorem denom_bridge (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    autParts La * autParts Lb *
      (∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k, ∏ i, (p i + q i).factorial)
      = matchDenSum La Lb k := by
  have h1 := lhs_eq_perm La Lb k hlenA hlenB hposA hposB
  have h2 := rhs_eq_perm La Lb k hlenA hlenB hposA hposB
  have hpos : 0 < (k - La.length).factorial * (k - Lb.length).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith