import BoundedGaps.Mertens
open ArithmeticFunction Finset BoundedGaps.Mertens

theorem mertensSummand_eq_prod {n : ℕ} (hsf : Squarefree n) :
    mertensSummand n = ∏ p ∈ n.primeFactors, (1 / ((p : ℝ) - 1)) := by
  have hn0 : n ≠ 0 := hsf.ne_zero
  have hpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
  have htot : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors n
    rw [hprod] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm n _))
  rw [mertensSummand_of_squarefree hsf hpos, htot, Nat.cast_prod,
      Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub hp1, Nat.cast_one]

theorem mertens_prod_upper (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, mertensSummand n ≤
      ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  set P : Finset ℕ := (Finset.Icc 2 N).filter Nat.Prime with hP
  set g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1) with hg
  -- RHS expands to a powerset sum.
  rw [show (∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1))) = ∑ t ∈ P.powerset, ∏ p ∈ t, g p from
      Finset.prod_one_add P]
  -- Restrict LHS to squarefree n.
  set S : Finset ℕ := (Finset.Icc 1 N).filter Squarefree with hS
  have hrestrict : ∑ n ∈ Finset.Icc 1 N, mertensSummand n = ∑ n ∈ S, mertensSummand n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hxIcc hxS
    have hns : ¬ Squarefree x := by
      rw [Finset.mem_filter] at hxS
      exact fun hsf => hxS ⟨hxIcc, hsf⟩
    exact mertensSummand_of_not_squarefree hns
  rw [hrestrict]
  -- Each squarefree summand is a product over its prime factors.
  have hterm : ∀ n ∈ S, mertensSummand n = ∏ p ∈ n.primeFactors, g p := by
    intro n hnS
    rw [hS, Finset.mem_filter] at hnS
    have hsf : Squarefree n := hnS.2
    simpa [hg] using mertensSummand_eq_prod hsf
  rw [Finset.sum_congr rfl hterm]
  -- Reindex by n ↦ primeFactors n (injective on squarefree n).
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x.primeFactors = y.primeFactors → x = y := by
    intro x hxS y hyS hxy
    rw [hS, Finset.mem_filter] at hxS hyS
    have hsfx : Squarefree x := hxS.2
    have hsfy : Squarefree y := hyS.2
    calc x = ∏ p ∈ x.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsfx).symm
      _ = ∏ p ∈ y.primeFactors, p := by rw [hxy]
      _ = y := Nat.prod_primeFactors_of_squarefree hsfy
  -- Reindex the squarefree sum as a sum over the image set of prime-factor sets.
  -- (State `key` in the image-on-the-left orientation so the summand function is
  --  pinned by a Miller pattern; rewriting `←` then matches first-order.)
  have key : ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, g p
      = ∑ n ∈ S, ∏ p ∈ n.primeFactors, g p :=
    Finset.sum_image hinj
  rw [← key]
  -- The image lands inside P.powerset; dropped terms are nonnegative.
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨n, hnS, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    rw [hS, Finset.mem_filter] at hnS
    have hnIcc : n ∈ Finset.Icc 1 N := hnS.1
    rw [Finset.mem_Icc] at hnIcc
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hpdvd) hnIcc.2
    rw [hP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpprime.two_le, hple⟩, hpprime⟩
  · intro t htP _
    rw [Finset.mem_powerset] at htP
    refine Finset.prod_nonneg ?_
    intro p hp
    have hpP : p ∈ P := htP hp
    have hp2 : 2 ≤ p := by
      rw [hP, Finset.mem_filter, Finset.mem_Icc] at hpP
      exact hpP.1.1
    have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    rw [hg]
    positivity
