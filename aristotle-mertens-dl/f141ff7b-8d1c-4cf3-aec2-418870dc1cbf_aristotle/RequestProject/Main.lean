import Mathlib

open ArithmeticFunction Finset UniqueFactorizationMonoid

noncomputable def mertensSummand (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

/-! ## Basic properties of mertensSummand -/

lemma mertensSummand_nonneg (n : ℕ) : 0 ≤ mertensSummand n := by
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

lemma mertensSummand_of_squarefree {n : ℕ} (hn : Squarefree n) (hn0 : 0 < n) :
    mertensSummand n = 1 / (Nat.totient n : ℝ) := by
  unfold mertensSummand
  simp [hn0, hn]
  norm_num [← pow_mul]

lemma mertensSummand_of_not_squarefree {n : ℕ} (hn : ¬Squarefree n) :
    mertensSummand n = 0 := by
  exact div_eq_zero_iff.mpr <| Or.inl <| by aesop

/-! ## Properties of radical (squarefree kernel) -/

lemma radical_le_of_pos (n : ℕ) (hn : 0 < n) : radical n ≤ n :=
  Nat.le_of_dvd hn radical_dvd_self

lemma radical_mem_Icc {n N : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    radical n ∈ Finset.Icc 1 N := by
  simp only [Finset.mem_Icc] at hn ⊢
  exact ⟨Nat.radical_pos n, le_trans (radical_le_of_pos n hn.1) hn.2⟩

/-! ## Geometric series helper -/

lemma geom_partial_sum_le {p : ℕ} (hp : Nat.Prime p) (M : ℕ) :
    ∑ k ∈ Finset.range M, (1 / (p : ℝ)) ^ (k + 1) ≤ 1 / ((p : ℝ) - 1) := by
  ring_nf
  rw [← Finset.mul_sum _ _ _, geom_sum_eq]
  · rcases p with (_ | _ | p) <;> norm_num at *
    field_simp
    rw [div_le_iff_of_neg] <;>
      nlinarith [pow_le_pow_right₀ (by linarith : 1 ≤ (p : ℝ) + 1 + 1)
        (show M ≥ 0 by positivity)]
  · aesop

/-! ## Key helper lemmas for fiber inequality -/

/-
For squarefree d with prime p ∈ primeFactors d, d / p is squarefree, positive,
    and has φ(d) = (p-1) * φ(d/p).
-/
lemma squarefree_div_prime {d p : ℕ} (hd : Squarefree d) (hp : Nat.Prime p) (hpdvd : p ∣ d) :
    Squarefree (d / p) ∧ 0 < d / p ∧ d / p < d ∧
    d.totient = (p - 1) * (d / p).totient := by
  obtain ⟨ k, hk ⟩ := hpdvd;
  rcases p with ( _ | _ | p ) <;> rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.squarefree_mul_iff ];
  · exact Nat.totient_prime hp;
  · rw [ Nat.totient_mul, Nat.totient_prime hp ];
    · grind;
    · tauto

/-
For m ≥ 1 with radical m = d and prime p dividing d,
    p divides m and radical (m / p ^ (m.factorization p)) = d / p.
-/
lemma radical_factor_split {m d p : ℕ} (hm : 0 < m) (hrad : radical m = d)
    (hp : Nat.Prime p) (hpdvd : p ∣ d) :
    p ∣ m ∧ 0 < m.factorization p ∧
    radical (m / p ^ m.factorization p) = d / p ∧
    m / p ^ m.factorization p < m := by
  refine' ⟨ _, _, _, Nat.div_lt_self hm ( pow_lt_pow_right₀ hp.one_lt ( Nat.pos_of_ne_zero _ ) ) ⟩;
  · refine' dvd_trans hpdvd _;
    exact hrad ▸ radical_dvd_self;
  · by_contra h_contra;
    simp_all +decide [ Finset.prod_eq_zero_iff, Nat.factorization_eq_zero_iff ];
    contrapose! h_contra;
    exact ⟨ dvd_trans hpdvd ( hrad ▸ radical_dvd_self ), hm.ne' ⟩;
  · have h_radical_div : radical (p ^ (Nat.factorization m p) * (m / p ^ (Nat.factorization m p))) = p * radical (m / p ^ (Nat.factorization m p)) := by
      convert radical_mul _ using 1;
      · have h_radical_def : radical (p ^ (m.factorization p)) = p := by
          rw [ radical_pow ] <;> norm_num [ hp ];
          · convert radical_of_prime hp.prime;
            simp +decide [ hp.ne_zero, hp.ne_one, normalize_apply ];
          · simp_all +decide [ Nat.factorization_eq_zero_iff, pos_iff_ne_zero ];
            grind +suggestions;
        rw [ h_radical_def ];
      · convert Nat.coprime_iff_isRelPrime.mp ( Nat.Coprime.pow_left _ <| Nat.coprime_ordCompl ( hp ) hm.ne' ) using 1;
    simp_all +decide [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ];
    rw [ Nat.mul_div_cancel_left _ hp.pos ];
  · have h_div : p ∣ m := by
      subst hrad;
      apply_rules [ dvd_trans hpdvd, radical_dvd_self ];
    rw [ Ne.eq_def, Nat.factorization_eq_zero_iff ] ; aesop

/-
The sum 1/m over {m ∈ [1,N] : radical m = d} can be bounded by
    splitting off powers of a prime p | d.
-/
lemma fiber_sum_split {N d p : ℕ} (hd : Squarefree d) (hd0 : 0 < d) (hd1 : 1 < d)
    (hp : Nat.Prime p) (hpdvd : p ∣ d) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤
    (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) *
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m) := by
  -- For each $m$ in the fiber (m ∈ Icc 1 N with radical m = d), by radical_factor_split we have p | m, a = m.factorization p ≥ 1, and m' = m / p^a has radical m' = d/p and m' < m.
  have h_factor : ∀ m ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N), ∃ a ∈ Finset.range N, ∃ m' ∈ Finset.filter (fun m => radical m = d / p) (Finset.Icc 1 N), m = p ^ (a + 1) * m' := by
    intro m hm;
    -- By radical_factor_split, we have p ∣ m, a = m.factorization p ≥ 1, and m' = m / p^a has radical m' = d/p and m' < m.
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a, 0 < a ∧ a ≤ N ∧ m = p ^ a * (m / p ^ a) ∧ radical (m / p ^ a) = d / p := by
      have := radical_factor_split ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) hp hpdvd;
      refine' ⟨ m.factorization p, this.2.1, _, Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ), this.2.2.1 ⟩;
      exact le_trans ( Nat.le_of_lt ( Nat.factorization_lt _ ( by aesop ) ) ) ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ] );
    refine' ⟨ a - 1, _, m / p ^ a, _, _ ⟩ <;> rcases a with ( _ | a ) <;> norm_num at *;
    · linarith;
    · exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd hm.1.1 ( ha₂.2.1.symm ▸ dvd_mul_right _ _ ) ) ( pow_pos hp.pos _ ), Nat.le_trans ( Nat.div_le_self _ _ ) hm.1.2 ⟩, ha₂.2.2 ⟩;
    · exact ha₂.2.1;
  -- By grouping the sum by the value of $a = m.factorization p$, we can bound the sum.
  have h_group : ∑ m ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N), (1 / m : ℝ) ≤ ∑ a ∈ Finset.range N, ∑ m' ∈ Finset.filter (fun m => radical m = d / p) (Finset.Icc 1 N), (if p ^ (a + 1) * m' ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N) then (1 / (p ^ (a + 1) * m') : ℝ) else 0) := by
    have h_group : ∑ m ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N), (1 / m : ℝ) ≤ ∑ m ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N), ∑ a ∈ Finset.range N, ∑ m' ∈ Finset.filter (fun m => radical m = d / p) (Finset.Icc 1 N), (if m = p ^ (a + 1) * m' then (1 / (p ^ (a + 1) * m') : ℝ) else 0) := by
      refine Finset.sum_le_sum fun m hm => ?_;
      obtain ⟨ a, ha, m', hm', rfl ⟩ := h_factor m hm; simp +decide [ Finset.sum_ite ] ;
      refine' le_trans _ ( Finset.single_le_sum ( fun x _ => Finset.sum_nonneg fun y _ => by positivity ) ha );
      refine' le_trans _ ( Finset.single_le_sum ( fun x _ => by positivity ) ( show m' ∈ _ from _ ) ) <;> aesop;
    refine le_trans h_group ?_;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro a ha; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
  refine le_trans h_group ?_;
  rw [ Finset.sum_mul _ _ _ ];
  gcongr ; norm_num [ Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun x hx => by split_ifs <;> first | positivity | rw [ mul_comm ] ;

/-
The fiber inequality: for squarefree d > 0, the sum of 1/m over
    {m ∈ [1,N] : radical m = d} is at most 1/φ(d).

    By strong induction on d using fiber_sum_split and geom_partial_sum_le.
-/
lemma fiber_sum_le (N : ℕ) (d : ℕ) (hd : Squarefree d) (hd0 : 0 < d) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤
    1 / (Nat.totient d : ℝ) := by
  induction' d using Nat.strong_induction_on with d ih generalizing N;
  by_cases hd1 : 1 < d;
  · -- By fiber_sum_split: the fiber sum ≤ (∑ geom) * (fiber sum for d/p).
    obtain ⟨p, hp_prime, hp_dvd⟩ : ∃ p, Nat.Prime p ∧ p ∣ d := by
      exact Nat.exists_prime_and_dvd hd1.ne'
    have h_fiber_split : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤ (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) * (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m) := by
      apply fiber_sum_split hd hd0 hd1 hp_prime hp_dvd;
    -- By IH (using d/p < d): fiber sum for d/p ≤ 1/φ(d/p).
    have h_fiber_ind : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m ≤ 1 / (d / p).totient := by
      apply ih (d / p) (Nat.div_lt_self hd0 hp_prime.one_lt) N (by
      exact hd.squarefree_of_dvd ( Nat.div_dvd_of_dvd hp_dvd )) (by
      exact Nat.div_pos ( Nat.le_of_dvd hd0 hp_dvd ) hp_prime.pos);
    -- By geom_partial_sum_le: ∑ geom ≤ 1/(p-1).
    have h_geom_partial_sum : (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) ≤ 1 / ((p : ℝ) - 1) := by
      convert geom_partial_sum_le hp_prime N using 1;
    -- By squarefree_div_prime: d.totient = (p-1) * (d/p).totient.
    have h_totient : d.totient = (p - 1) * (d / p).totient := by
      have := squarefree_div_prime hd hp_prime hp_dvd; aesop;
    rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.succ_div ];
    exact h_fiber_split.trans ( by rw [ mul_comm ] ; gcongr );
  · interval_cases d ; norm_num;
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => by positivity ) _;
    exact { 1 };
    · intro m hm; simp_all +decide [ radical_eq_one_iff ] ;
      grind;
    · norm_num

/-
The fiber sum for any d is at most mertensSummand d.
-/
lemma fiber_le_mertensSummand (N d : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤
    mertensSummand d := by
  unfold mertensSummand;
  by_cases hd : Squarefree d <;> by_cases hd0 : d = 0 <;> simp_all +decide;
  · convert fiber_sum_le N d hd ( Nat.pos_of_ne_zero hd0 ) using 1 ; norm_num [ mertensSummand_of_squarefree hd ( Nat.pos_of_ne_zero hd0 ) ];
    norm_num [ ← pow_mul ];
  · convert Finset.sum_nonpos _;
    · infer_instance;
    · simp +zetaDelta at *;
      exact fun i hi₁ hi₂ hi₃ => False.elim <| hd <| hi₃ ▸ squarefree_radical

/-
For every N, the aggregate inequality holds.
-/
theorem mertens_crux (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n := by
  convert Finset.sum_le_sum fun x hx => fiber_le_mertensSummand N x using 1;
  convert Finset.sum_fiberwise_of_maps_to ( fun n hn => radical_mem_Icc hn ) ( fun n => 1 / ( n : ℝ ) ) using 1;
  rw [ Finset.sum_fiberwise_of_maps_to ];
  · exact fun i a => radical_mem_Icc a
  · convert Finset.sum_fiberwise_of_maps_to ( fun n hn => radical_mem_Icc hn ) ( fun n => 1 / ( n : ℝ ) ) using 1