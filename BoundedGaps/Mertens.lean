import Mathlib

/-!
# A Mertens-type lower bound: `log N ≤ ∑_{n ≤ N} μ²(n)/φ(n)`

This file proves the **unconditional, EH-free lower half** of the classical Mertens
estimate `∑_{n≤N} μ²(n)/φ(n) ~ log N`:

  `mertens_lower : Real.log N ≤ ∑ n ∈ Finset.Icc 1 N, μ²(n)/φ(n)`.

It is the first concrete analytic brick of the sieve-side burn-down
(`ANALYTIC_AXIOM_BURNDOWN.md`): the GPY/Maynard singular-series → integral
asymptotic (sub-step (c)) that gates the `s1_*_holds_from_nonprime_asym` axioms
in `Sieve.lean` needs exactly this kind of `∑ μ²/φ` summation as its 1-dimensional
core.

## Structure

The two endpoints are mathlib one-liners:
* `log_le_harmonic`  : `log N ≤ harmonic N`  (from `log_le_harmonic_floor`);
* `harmonic_eq_icc_sum` : `harmonic N = ∑_{Icc 1 N} 1/n`  (range↔Icc reindex).

The content is the middle inequality `mertens_crux`:

  `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)`,

which is **false termwise** (e.g. at `n = 4`) but true in aggregate. Proof by the
radical-fiber rearrangement: group `[1,N]` by squarefree kernel
`d = radical m` (`Finset.sum_fiberwise_of_maps_to`), and bound each fiber

  `∑_{radical m = d, m ≤ N} 1/m ≤ 1/φ(d) = μ²(d)/φ(d)`

by strong induction on `d`, peeling a prime `p ∣ d` and summing the geometric
tail `∑_k p^{-(k+1)} ≤ 1/(p-1)` (`fiber_sum_le`, `fiber_sum_split`,
`geom_partial_sum_le`).

## Provenance

`mertens_crux` and its helper lemmas were proven by Harmonic's Aristotle
(project `6c45fd6b`, the analytic-NT on-ramp bet recorded in
`ANALYTIC_AXIOM_BURNDOWN.md`), then ported and re-verified in this repo's
mathlib `v4.29.1`: one `grind` regression in `radical_factor_split` (the
`radical (p^k) = p` step) was replaced by an explicit
`radical_pow`/`radical_of_prime` derivation. `#print axioms mertens_lower =
[propext, Classical.choice, Quot.sound]` — fully kernel-clean, no `native_decide`.
-/

set_option linter.style.longLine false

namespace BoundedGaps.Mertens

open ArithmeticFunction Finset UniqueFactorizationMonoid

/-- The Mertens summand `μ²(n)/φ(n)` (zero off the squarefree numbers). -/
noncomputable def mertensSummand (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

/-! ## Basic properties of `mertensSummand` -/

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

/-! ## Properties of `radical` (squarefree kernel) -/

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

/-! ## Key helper lemmas for the fiber inequality -/

/-- For squarefree `d` with prime `p ∣ d`, the quotient `d / p` is squarefree,
positive, smaller than `d`, and `φ(d) = (p-1)·φ(d/p)`. -/
lemma squarefree_div_prime {d p : ℕ} (hd : Squarefree d) (hp : Nat.Prime p) (hpdvd : p ∣ d) :
    Squarefree (d / p) ∧ 0 < d / p ∧ d / p < d ∧
    d.totient = (p - 1) * (d / p).totient := by
  obtain ⟨ k, hk ⟩ := hpdvd;
  rcases p with ( _ | _ | p ) <;> rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.squarefree_mul_iff ];
  · exact Nat.totient_prime hp;
  · rw [ Nat.totient_mul, Nat.totient_prime hp ];
    · grind;
    · tauto

/-- For `m ≥ 1` with `radical m = d` and prime `p ∣ d`: `p ∣ m`, the exponent
`m.factorization p` is positive, `radical (m / p^(m.factorization p)) = d / p`, and
that quotient is `< m`. -/
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
      · have hpm : p ∣ m := dvd_trans hpdvd (hrad ▸ radical_dvd_self)
        have hfp : m.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hm.ne' hpm).ne'
        have h_radical_def : radical (p ^ (m.factorization p)) = p := by
          rw [radical_pow _ hfp, radical_of_prime hp.prime]; simp
        rw [ h_radical_def ];
      · convert Nat.coprime_iff_isRelPrime.mp ( Nat.Coprime.pow_left _ <| Nat.coprime_ordCompl ( hp ) hm.ne' ) using 1;
    simp_all +decide [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ];
    rw [ Nat.mul_div_cancel_left _ hp.pos ];
  · have h_div : p ∣ m := by
      subst hrad;
      apply_rules [ dvd_trans hpdvd, radical_dvd_self ];
    rw [ Ne.eq_def, Nat.factorization_eq_zero_iff ] ; aesop

/-- The radical-fiber sum over `{m ≤ N : radical m = d}` is bounded by splitting off
powers of a prime `p ∣ d`: a geometric factor times the fiber sum at `d / p`. -/
lemma fiber_sum_split {N d p : ℕ} (hd : Squarefree d) (hd0 : 0 < d) (hd1 : 1 < d)
    (hp : Nat.Prime p) (hpdvd : p ∣ d) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤
    (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) *
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m) := by
  have h_factor : ∀ m ∈ Finset.filter (fun m => radical m = d) (Finset.Icc 1 N), ∃ a ∈ Finset.range N, ∃ m' ∈ Finset.filter (fun m => radical m = d / p) (Finset.Icc 1 N), m = p ^ (a + 1) * m' := by
    intro m hm;
    obtain ⟨a, ha₁, ha₂⟩ : ∃ a, 0 < a ∧ a ≤ N ∧ m = p ^ a * (m / p ^ a) ∧ radical (m / p ^ a) = d / p := by
      have := radical_factor_split ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) hp hpdvd;
      refine' ⟨ m.factorization p, this.2.1, _, Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ), this.2.2.1 ⟩;
      exact le_trans ( Nat.le_of_lt ( Nat.factorization_lt _ ( by aesop ) ) ) ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ] );
    refine' ⟨ a - 1, _, m / p ^ a, _, _ ⟩ <;> rcases a with ( _ | a ) <;> norm_num at *;
    · linarith;
    · exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd hm.1.1 ( ha₂.2.1.symm ▸ dvd_mul_right _ _ ) ) ( pow_pos hp.pos _ ), Nat.le_trans ( Nat.div_le_self _ _ ) hm.1.2 ⟩, ha₂.2.2 ⟩;
    · exact ha₂.2.1;
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

/-- The fiber inequality: for squarefree `d > 0`, the sum of `1/m` over
`{m ≤ N : radical m = d}` is at most `1/φ(d)`. Strong induction on `d` via
`fiber_sum_split` + `geom_partial_sum_le`. -/
lemma fiber_sum_le (N : ℕ) (d : ℕ) (hd : Squarefree d) (hd0 : 0 < d) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤
    1 / (Nat.totient d : ℝ) := by
  induction' d using Nat.strong_induction_on with d ih generalizing N;
  by_cases hd1 : 1 < d;
  · obtain ⟨p, hp_prime, hp_dvd⟩ : ∃ p, Nat.Prime p ∧ p ∣ d := by
      exact Nat.exists_prime_and_dvd hd1.ne'
    have h_fiber_split : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d), (1 : ℝ) / m ≤ (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) * (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m) := by
      apply fiber_sum_split hd hd0 hd1 hp_prime hp_dvd;
    have h_fiber_ind : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m = d / p), (1 : ℝ) / m ≤ 1 / (d / p).totient := by
      apply ih (d / p) (Nat.div_lt_self hd0 hp_prime.one_lt) N (by
      exact hd.squarefree_of_dvd ( Nat.div_dvd_of_dvd hp_dvd )) (by
      exact Nat.div_pos ( Nat.le_of_dvd hd0 hp_dvd ) hp_prime.pos);
    have h_geom_partial_sum : (∑ k ∈ Finset.range N, (1 / (p : ℝ)) ^ (k + 1)) ≤ 1 / ((p : ℝ) - 1) := by
      convert geom_partial_sum_le hp_prime N using 1;
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

/-- Each radical-fiber sum is at most `mertensSummand d` (equal `1/φ(d)` for
squarefree `d`, while the fiber is empty and the summand `0` otherwise). -/
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

/-- **The crux** (Aristotle `6c45fd6b`): `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)`.
Sum-over-fibers of the radical map, each fiber bounded by `fiber_le_mertensSummand`. -/
theorem mertens_crux (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n := by
  convert Finset.sum_le_sum fun x hx => fiber_le_mertensSummand N x using 1;
  convert Finset.sum_fiberwise_of_maps_to ( fun n hn => radical_mem_Icc hn ) ( fun n => 1 / ( n : ℝ ) ) using 1;
  rw [ Finset.sum_fiberwise_of_maps_to ];
  · exact fun i a => radical_mem_Icc a
  · convert Finset.sum_fiberwise_of_maps_to ( fun n hn => radical_mem_Icc hn ) ( fun n => 1 / ( n : ℝ ) ) using 1

/-! ## Endpoints and assembled lower bound -/

/-- `harmonic N` (a `ℚ` range-sum) equals the `ℝ` `Icc 1 N` sum of `1/n`. Induction
on `N` via `harmonic_succ` + `Finset.sum_Icc_succ_top`. -/
theorem harmonic_eq_icc_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
  induction N with
  | zero => simp [harmonic]
  | succ n ih =>
    rw [harmonic_succ, Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ n + 1)]
    rw [Rat.cast_add, ih]
    congr 1
    push_cast
    rw [one_div]

/-- The EH-free endpoint `log N ≤ harmonic N` (mathlib `log_le_harmonic_floor`). -/
theorem log_le_harmonic (N : ℕ) : Real.log N ≤ (harmonic N : ℝ) := by
  have h := log_le_harmonic_floor (N : ℝ) (by positivity)
  rwa [Nat.floor_natCast] at h

/-- **Mertens lower bound.** `log N ≤ ∑_{n≤N} μ²(n)/φ(n)`. Fully kernel-clean
(`#print axioms = [propext, Classical.choice, Quot.sound]`). -/
theorem mertens_lower (N : ℕ) :
    Real.log N ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n :=
  calc Real.log N ≤ (harmonic N : ℝ) := log_le_harmonic N
    _ = ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := harmonic_eq_icc_sum N
    _ ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n := mertens_crux N

/-- `μ²(n)/φ(n) ≤ 1/φ(n)` (since `μ²(n) ∈ {0,1}`). -/
lemma mertensSummand_le_inv_totient (n : ℕ) :
    mertensSummand n ≤ 1 / (Nat.totient n : ℝ) := by
  have hμ : (ArithmeticFunction.moebius n : ℤ) ^ 2 ≤ 1 := by
    by_cases hsf : Squarefree n
    · exact le_of_eq (moebius_sq_eq_one_of_squarefree hsf)
    · rw [moebius_eq_zero_of_not_squarefree hsf]; norm_num
  have hμr : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 ≤ 1 := by exact_mod_cast hμ
  unfold mertensSummand
  rcases Nat.eq_zero_or_pos (Nat.totient n) with h | h
  · simp [h]
  · gcongr

/-- **Corollary** (lower bound on the totient harmonic sum):
`log N ≤ ∑_{n≤N} 1/φ(n)`. Immediate from `mertens_lower` and `μ²(n) ≤ 1`. -/
theorem log_le_sum_inv_totient (N : ℕ) :
    Real.log N ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (Nat.totient n : ℝ) :=
  (mertens_lower N).trans
    (Finset.sum_le_sum fun n _ => mertensSummand_le_inv_totient n)

/-- **Corollary** (divergence): the partial sums of `∑ μ²(n)/φ(n)` tend to `+∞`
(they dominate `log N → ∞`). -/
theorem tendsto_sum_mertensSummand_atTop :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, mertensSummand n)
      Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono mertens_lower
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ## The Euler-product upper bound

The companion *upper* half of the Mertens estimate. For squarefree `n` the summand
factors over the prime divisors,
  `μ²(n)/φ(n) = ∏_{p ∣ n} 1/(p-1)`,
and summing over all squarefree `n ≤ N` is dominated by the finite Euler product
`∏_{p ≤ N} (1 + 1/(p-1))`, because `n ↦ primeFactors n` injects the squarefree
numbers `≤ N` into the powerset of the primes `≤ N`. -/

/-- For squarefree `n`, the Mertens summand is the product `∏_{p ∣ n} 1/(p-1)`. -/
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

/-- **Mertens upper bound** (Euler product form): the partial sum `∑_{n≤N} μ²(n)/φ(n)`
is dominated by the finite Euler product `∏_{p ≤ N} (1 + 1/(p-1))`. -/
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

/-! ## Chebyshev's first estimate

The foundational prime-density input for turning the Euler-product upper bound
`mertens_prod_upper` into a genuine `O(log N)` estimate: `θ(N) = ∑_{p≤N} log p ≤
N · log 4`. This is the first brick of the sub-ladder
(Chebyshev θ → Mertens `∑ 1/p` → `∏(1+1/(p-1)) = O(log N)` → `∑ μ²/φ = Θ(log N)`)
recorded in `ANALYTIC_AXIOM_BURNDOWN.md`. It is immediate from mathlib's
`primorial_le_four_pow` (`primorial N ≤ 4^N`) by taking logarithms. -/

/-- **Chebyshev's first estimate (upper bound)**: the Chebyshev function
`θ(N) = ∑_{p ≤ N} log p` satisfies `θ(N) ≤ N · log 4`. -/
theorem chebyshev_theta_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)
      ≤ (N : ℝ) * Real.log 4 := by
  have hcast : ((primorial N : ℕ) : ℝ)
      = ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℝ) := by
    rw [primorial, Nat.cast_prod]
  have hne : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℝ) ≠ 0 := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact_mod_cast hpp.pos.ne'
  have hlogeq : Real.log (primorial N)
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [hcast, Real.log_prod hne]
  have hbound : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
    exact_mod_cast primorial_le_four_pow N
  have hpos : (0 : ℝ) < (primorial N : ℝ) := by exact_mod_cast primorial_pos N
  have hlogle : Real.log (primorial N) ≤ Real.log ((4 : ℝ) ^ N) :=
    Real.log_le_log hpos hbound
  rw [hlogeq, Real.log_pow] at hlogle
  exact hlogle

/-- Chebyshev's θ-bound in **partial-sum / indicator form**: summing the indicator
`[n prime]·log n` over `Icc 1 n` gives `θ(n) ≤ n · log 4`. This is the shape needed
as the partial-sum hypothesis for the Abel-summation step
(`∑_{p≤N} (log p)/p = O(log N)`). -/
theorem chebyshev_theta_le' (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) else 0)
      ≤ (n : ℝ) * Real.log 4 := by
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  have hexpand : ∑ k ∈ Finset.range (n + 1), (if k.Prime then Real.log (k : ℝ) else 0)
      = ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) else 0) := by
    refine (Finset.sum_subset hsub ?_).symm
    intro x hxr hxIcc
    rw [Finset.mem_range] at hxr
    rw [Finset.mem_Icc] at hxIcc
    have hx0 : x = 0 := by omega
    subst hx0; simp
  calc ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) else 0)
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
        rw [Finset.sum_filter]; exact hexpand.symm
    _ ≤ (n : ℝ) * Real.log 4 := chebyshev_theta_le n

/-! ## Telescoping tail (for `∑ 1/(p-1) = ∑ 1/p + O(1)`)

The Euler-product upper bound is controlled by `∑_{p≤N} 1/(p-1)`, which differs
from the prime harmonic sum `∑_{p≤N} 1/p` by the convergent tail `∑ 1/(p(p-1))`.
This is bounded by the telescoping sum `∑_{2≤n≤N} (1/(n-1) − 1/n) = 1 − 1/N ≤ 1`. -/

/-- Telescoping identity: `∑_{2 ≤ n ≤ N} (1/(n-1) − 1/n) = 1 − 1/N` (for `N ≥ 1`). -/
theorem telescope_tail_eq : ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 2 N, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) = 1 - 1 / (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1), ih]
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    simp only [add_sub_cancel_right]
    field_simp
    ring

/-- Telescoping bound: `∑_{2 ≤ n ≤ N} (1/(n-1) − 1/n) ≤ 1`. -/
theorem telescope_tail_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [telescope_tail_eq N h]
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- The prime-restricted tail: `∑_{p ≤ N} (1/(p-1) − 1/p) ≤ 1`. Hence
`∑_{p≤N} 1/(p-1) ≤ ∑_{p≤N} 1/p + 1`: the gap between the Euler-product exponent
and the prime harmonic sum is `O(1)`. -/
theorem prime_tail_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)) ≤ 1 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (telescope_tail_le N)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, by omega⟩
  · intro p hp _
    rw [Finset.mem_Icc] at hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h2 : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
    have : 1 / (p : ℝ) ≤ 1 / ((p : ℝ) - 1) := one_div_le_one_div_of_le h1 h2
    linarith

/-! ## Mertens' first theorem (upper bound)

Discrete Abel summation turns the Chebyshev θ-bound into the Mertens estimate
`∑_{p≤N} (log p)/p = O(log N)`. The Abel-summation lemma `abel_div_le` was proved
by Harmonic's Aristotle (project `32baa99f`, summation-by-parts) and verified
kernel-clean under v4.29.1. -/

/-- **Discrete Abel summation bound.** If the partial sums `∑_{1 ≤ k ≤ n} a k` are
bounded by `c · n` (and `c ≥ 0`), then `∑_{1 ≤ n ≤ N} a n / n ≤ c · ∑_{1 ≤ n ≤ N} 1/n`.
Proved by Aristotle (`32baa99f`); the nonnegativity hypothesis `ha` is unused by the
upper bound but kept to document the intended (Chebyshev) application. -/
theorem abel_div_le (N : ℕ) (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0 ≤ a n)
    (hA : ∀ n, ∑ k ∈ Finset.Icc 1 n, a k ≤ c * (n : ℝ)) :
    ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) ≤ c * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
  have h_abel : ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) = (∑ n ∈ Finset.Icc 1 N, a n) / N + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) / (n * (n + 1)) := by
    induction N <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring;
    cases ‹ℕ› <;> norm_num [ Finset.sum_Ioc_succ_top ] at * ; ring;
    grind;
  have h_bound : (∑ n ∈ Finset.Icc 1 N, a n) / N + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) / (n * (n + 1)) ≤ c + ∑ n ∈ Finset.Icc 1 (N - 1), c / (n + 1) := by
    refine' add_le_add _ ( Finset.sum_le_sum fun n hn => _ );
    · exact div_le_of_le_mul₀ ( Nat.cast_nonneg _ ) hc ( hA N );
    · rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 1 by exact_mod_cast Finset.mem_Icc.mp hn |>.1, hA n, hc ];
  rcases N with ( _ | N ) <;> simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
  exact h_bound.trans ( by erw [ Finset.sum_Ico_eq_sum_range _ _ ] ; erw [ Finset.sum_Ico_eq_sum_range _ _ ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ] )

/-- **Mertens' first theorem (upper bound)**: `∑_{p≤N} (log p)/p ≤ log 4 · (1 + log N)`.
Instantiates `abel_div_le` with `a n = [n prime]·log n` (`c = log 4`), using
`chebyshev_theta_le'` for the partial-sum hypothesis and mathlib's
`harmonic_le_one_add_log` for the harmonic upper bound. -/
theorem mertens_first_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      ≤ Real.log 4 * (1 + Real.log N) := by
  set a : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) else 0 with ha_def
  have hc : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    rw [ha_def]
    by_cases hp : n.Prime
    · simp only [hp, if_true]
      exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · simp [hp]
  have hA : ∀ n, ∑ k ∈ Finset.Icc 1 n, a k ≤ Real.log 4 * (n : ℝ) := by
    intro n
    rw [mul_comm]
    exact chebyshev_theta_le' n
  have hkey := abel_div_le N a (Real.log 4) hc ha hA
  have hLHS : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) := by
    have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
      intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
    have hexpand : ∑ n ∈ Finset.range (N + 1), a n / (n : ℝ)
        = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) := by
      refine (Finset.sum_subset hsub ?_).symm
      intro x hxr hxIcc
      rw [Finset.mem_range] at hxr
      rw [Finset.mem_Icc] at hxIcc
      have hx0 : x = 0 := by omega
      subst hx0; simp [ha_def]
    rw [← hexpand]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [ha_def]
    by_cases hp : n.Prime <;> simp [hp]
  rw [hLHS]
  refine hkey.trans ?_
  rw [← harmonic_eq_icc_sum]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hc

/-- Mertens' first theorem in **partial-sum / indicator form**: the partial sums
of `[k prime]·(log k)/k` over `Icc 1 n` are `≤ log 4 · (1 + log n)`. This is the
partial-sum hypothesis for the *second* Abel-summation step (weight `1/log p`)
that yields Mertens' second theorem `∑_{p≤N} 1/p = O(log log N)`. -/
theorem mertens_first_le' (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0)
      ≤ Real.log 4 * (1 + Real.log n) := by
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  have hexpand : ∑ k ∈ Finset.range (n + 1), (if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0)
      = ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0) := by
    refine (Finset.sum_subset hsub ?_).symm
    intro x hxr hxIcc
    rw [Finset.mem_range] at hxr
    rw [Finset.mem_Icc] at hxIcc
    have hx0 : x = 0 := by omega
    subst hx0; simp
  calc ∑ k ∈ Finset.Icc 1 n, (if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0)
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        rw [Finset.sum_filter]; exact hexpand.symm
    _ ≤ Real.log 4 * (1 + Real.log n) := mertens_first_le n

/-! ## The Mertens-2nd analytic core: `∑ 1/(n log n) = O(log log N)`

The second Abel step (weight `1/log p`) toward `∑_{p≤N} 1/p` reduces to bounding
`∑_{n} 1/(n log n)`, which is `log log N + O(1)` by comparison with
`∫ dt/(t log t) = log(log t)`. These are the analytic-input lemmas. -/

/-- `(log ∘ log)' = 1/(t log t)` for `t > 1` (chain rule). -/
theorem hasDerivAt_log_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => Real.log (Real.log x)) (1 / (t * Real.log t)) t := by
  have ht0 : t ≠ 0 := by positivity
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
  have h2 : HasDerivAt Real.log (Real.log t)⁻¹ (Real.log t) := Real.hasDerivAt_log hlog
  have hcomp := h2.comp t h1
  convert hcomp using 1
  rw [one_div, mul_inv, mul_comm]

/-- `fun x => 1/(x log x)` is continuous on `[2, N]` (denominator nonzero there). -/
theorem continuousOn_one_div_x_log_x {N : ℕ} :
    ContinuousOn (fun x : ℝ => 1 / (x * Real.log x)) (Set.Icc 2 (N : ℝ)) := by
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_id.mul (Real.continuousOn_log.mono (by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.1]))
  · intro x hx
    simp only [Set.mem_Icc] at hx
    have hx2 : (1 : ℝ) < x := by linarith [hx.1]
    have : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx2)
    have hxpos : (0 : ℝ) < x := by linarith [hx.1]
    positivity

/-- The integral `∫_2^N 1/(x log x) dx = log(log N) − log(log 2)` (for `2 ≤ N`). -/
theorem integral_one_div_x_log_x {N : ℕ} (hN : 2 ≤ N) :
    ∫ x in (2 : ℝ)..(N : ℝ), 1 / (x * Real.log x)
      = Real.log (Real.log N) - Real.log (Real.log 2) := by
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun x => Real.log (Real.log x)) (1 / (x * Real.log x)) x := by
    intro x hx
    rw [Set.uIcc_of_le h2N, Set.mem_Icc] at hx
    exact hasDerivAt_log_log (by linarith [hx.1])
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x * Real.log x)) MeasureTheory.volume 2 N := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h2N]
    exact continuousOn_one_div_x_log_x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- `fun x => 1/(x log x)` is antitone on `[2, N]`. -/
theorem antitoneOn_one_div_x_log_x {N : ℕ} :
    AntitoneOn (fun x : ℝ => 1 / (x * Real.log x)) (Set.Icc 2 (N : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  have hx1 : (1 : ℝ) < x := by linarith [hx.1]
  have hy1 : (1 : ℝ) < y := by linarith [hy.1]
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hdenx : (0 : ℝ) < x * Real.log x := by positivity
  have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  have hdenle : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy hlogle (le_of_lt hlogx) (by linarith)
  simp only
  exact one_div_le_one_div_of_le hdenx hdenle

/-- **Mertens-2nd analytic core**: `∑_{n=3}^{N} 1/(n log n) ≤ log log N − log log 2`
(sum-integral comparison for the antitone `1/(x log x)`). -/
theorem sum_one_div_n_log_n_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Finset.Ico 2 N, 1 / (((i : ℝ) + 1) * Real.log ((i : ℝ) + 1))
      ≤ Real.log (Real.log N) - Real.log (Real.log 2) := by
  have h := AntitoneOn.sum_le_integral_Ico (a := 2) (b := N) hN antitoneOn_one_div_x_log_x
  simp only [Nat.cast_ofNat] at h
  rw [integral_one_div_x_log_x hN] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring_nf

/-- **General Abel summation identity** (summation by parts): with partial sums
`A n = ∑_{1 ≤ k ≤ n} a k`,
`∑_{1≤n≤N} a n · w n = A N · w N − ∑_{1≤n≤N-1} A n · (w (n+1) − w n)`.
Proved by Aristotle (`431512dd`, induction on `N`); verified kernel-clean under
v4.29.1. The general-weight tool for the second Mertens Abel step (weight `1/log p`). -/
theorem abel_summation_identity (N : ℕ) (a w : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, a n * w n
      = (∑ k ∈ Finset.Icc 1 N, a k) * w N
        - ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) * (w (n + 1) - w n) := by
  induction' N with N ih <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ; ring!;
  cases N <;> norm_num [ add_comm, Finset.sum_Ioc_succ_top ] at * ; linarith!;

/-- **Mertens-2nd term bound.** For `n ≥ 2`,
`(1 + log n)·(1/log n − 1/log (n+1)) ≤ (1 + 1/log 2)/(n · log n)`. Bounds each
summand of the difference-sum in the second Abel step toward `∑_{p≤N} 1/p`:
`log(n+1)−log n = log(1+1/n) ≤ 1/n`, `1 + log n ≤ (1+1/log 2)·log n` for `n ≥ 2`. -/
theorem mertens_second_term_bound (n : ℕ) (hn : 2 ≤ n) :
    (1 + Real.log n) * (1 / Real.log n - 1 / Real.log (n + 1))
      ≤ (1 + 1 / Real.log 2) / ((n : ℝ) * Real.log n) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) < Real.log n := Real.log_pos hn1
  have hlogn1 : (0 : ℝ) < Real.log (n + 1) := Real.log_pos (by linarith)
  have hle : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hn0 (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hdiff : Real.log (n + 1) - Real.log n ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have heq : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by field_simp
    rw [heq]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have hfac2 : 1 / Real.log n - 1 / Real.log (n + 1) ≤ (1 / (n : ℝ)) / (Real.log n) ^ 2 := by
    rw [div_sub_div _ _ (ne_of_gt hlogn) (ne_of_gt hlogn1)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh : (Real.log (n + 1) - Real.log n) * Real.log n ≤ (1 / (n : ℝ)) * Real.log (n + 1) := by
      calc (Real.log (n + 1) - Real.log n) * Real.log n
          ≤ (1 / (n : ℝ)) * Real.log n := by nlinarith [hdiff, hlogn]
        _ ≤ (1 / (n : ℝ)) * Real.log (n + 1) := by nlinarith [hle, hn0]
    nlinarith [hh, hlogn, hlogn1, mul_pos hlogn hlogn1]
  have hfac1 : 1 + Real.log n ≤ (1 + 1 / Real.log 2) * Real.log n := by
    have h1 : 1 ≤ (1 / Real.log 2) * Real.log n := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2]; linarith
    nlinarith [h1]
  have hfac2pos : (0 : ℝ) ≤ 1 / Real.log n - 1 / Real.log (n + 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hlogn hle
  have hcoef : (0 : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log n :=
    mul_nonneg (by positivity) (le_of_lt hlogn)
  calc (1 + Real.log n) * (1 / Real.log n - 1 / Real.log (n + 1))
      ≤ ((1 + 1 / Real.log 2) * Real.log n) * ((1 / (n : ℝ)) / (Real.log n) ^ 2) :=
        mul_le_mul hfac1 hfac2 hfac2pos hcoef
    _ = (1 + 1 / Real.log 2) / ((n : ℝ) * Real.log n) := by
        field_simp

/-! ## Stirling-type bounds on `∑ log m = log(N!)` (for the *sharp* Mertens route)

The von Mangoldt approach to the **sharp** Mertens 1st theorem
(`∑_{p≤N}(log p)/p = log N + O(1)`, coefficient exactly 1 — unlike the lossy
`log 4` of `mertens_first_le`) needs `∑_{m≤N} log m = N log N + O(N)`. Both sides
follow from comparison with `∫ log x dx = x log x − x` (mathlib `integral_log`). -/

/-- `∑_{m≤N} log m ≤ N log N` (each summand `≤ log N`). -/
theorem sum_log_le {N : ℕ} :
    ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) ≤ (N : ℝ) * Real.log N := by
  calc ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact Real.log_le_log (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- `N log N − N + 1 ≤ ∑_{m≤N} log m` (lower bound by `∫_1^N log x dx = N log N − N + 1`). -/
theorem le_sum_log {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N + 1 ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  have hmono : MonotoneOn (fun x : ℝ => Real.log x) (Set.Icc 1 ((1 : ℝ) + (N - 1 : ℕ))) := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    exact Real.log_le_log (by linarith [hx.1]) hxy
  have h := MonotoneOn.integral_le_sum hmono
  have hNcast : (1 : ℝ) + ((N - 1 : ℕ) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN]; simp
  rw [hNcast, integral_log] at h
  simp only [Real.log_one, mul_zero, sub_zero] at h
  refine le_trans h ?_
  have hreindex : ∑ i ∈ Finset.range (N - 1), Real.log (1 + ((i + 1 : ℕ) : ℝ))
      = ∑ m ∈ Finset.Icc 2 N, Real.log (m : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1) (fun i _ => ?_)
    congr 1
    push_cast
    ring
  rw [hreindex]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro m hm _
    rw [Finset.mem_Icc] at hm
    exact Real.log_nonneg (by exact_mod_cast hm.1)

/-! ### Floor decomposition `⌊N/n⌋ = N/n − frac`

To pass from `∑_n Λ(n)·⌊N/n⌋` (the hyperbola identity) to `N·∑_n Λ(n)/n`, one uses
`(N:ℝ)/n − 1 ≤ ⌊N/n⌋ ≤ (N:ℝ)/n`; the `O(1)·n` slack is controlled by the Chebyshev
`ψ(N) = ∑_{n≤N} Λ(n) = O(N)` bound (next sharp-route brick). -/

/-- `⌊N/n⌋ ≤ N/n` over `ℝ`. -/
theorem cast_div_le_self (N n : ℕ) : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) :=
  Nat.cast_div_le

/-- `N/n − 1 ≤ ⌊N/n⌋` over `ℝ` (for `1 ≤ n`). -/
theorem sub_one_le_cast_div (N n : ℕ) (hn : 1 ≤ n) :
    (N : ℝ) / (n : ℝ) - 1 ≤ ((N / n : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdm : n * (N / n) + N % n = N := Nat.div_add_mod N n
  have hmod : N % n < n := Nat.mod_lt N hn
  have hlt : (N : ℝ) < (n : ℝ) * ((N / n : ℕ) : ℝ) + (n : ℝ) := by
    have h1 : (N : ℝ) = (n : ℝ) * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) := by exact_mod_cast hdm.symm
    have h2 : ((N % n : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hmod
    linarith
  rw [div_sub_one (ne_of_gt hn0), div_le_iff₀ hn0]
  nlinarith [hlt]

/-! ### Von Mangoldt hyperbola identity (sharp Mertens 1st)

`∑_{1≤n≤N} Λ(n)·⌊N/n⌋ = ∑_{1≤m≤N} log m  (= log N!)`, via `⌊N/n⌋ = #{m≤N : n∣m}`,
interchange of summation, and `ArithmeticFunction.vonMangoldt_sum` (`∑_{i∣m} Λ i = log m`).
Proved by Aristotle (`cc0dfbaf`); verified kernel-clean under v4.29.1. This is the entry
point to the SHARP `∑_{p≤N}(log p)/p = log N + O(1)` (coefficient 1) — see
`PENDING_WORK.md §C` for the sharp/crude split. -/
theorem vonMangoldt_hyperbola (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) := by
  have h_interchange : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) * (Finset.card (Finset.filter (fun m => n ∣ m) (Finset.Icc 1 N))) = ∑ m ∈ Finset.Icc 1 N, (∑ n ∈ Finset.filter (fun n => n ∣ m) (Finset.Icc 1 N), (ArithmeticFunction.vonMangoldt n)) := by
    simp +decide only [card_filter, sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Nat.cast_sum ] ; rw [ Finset.mul_sum ] ; congr ; ext ; aesop;
  have h_filter : ∀ m ∈ Finset.Icc 1 N, (Finset.filter (fun n => n ∣ m) (Finset.Icc 1 N)) = (Nat.divisors m) := by
    simp +contextual [ Finset.ext_iff, Nat.mem_divisors ];
    exact fun m hm₁ hm₂ a => ⟨ fun h => ⟨ h.2, by linarith ⟩, fun h => ⟨ ⟨ Nat.pos_of_dvd_of_pos h.1 hm₁, Nat.le_trans ( Nat.le_of_dvd hm₁ h.1 ) hm₂ ⟩, h.1 ⟩ ⟩;
  convert h_interchange using 1;
  · convert rfl;
    convert Nat.Ioc_filter_dvd_card_eq_div N ‹_› using 1;
  · rw [ Finset.sum_congr rfl ];
    intro m hm; rw [ ← ArithmeticFunction.vonMangoldt_sum ] ; aesop;

/-- **Sharp `∑ Λ(n)/n` lower bound**: `log N − 1 ≤ ∑_{1≤n≤N} Λ(n)/n`. From the
hyperbola identity `∑Λ(n)⌊N/n⌋ = ∑log m`, with `⌊N/n⌋ ≤ N/n` (and `Λ ≥ 0`) giving
`∑log m ≤ N·∑Λ(n)/n`, combined with the Stirling lower bound `le_sum_log`. This is
the lower half of the sharp Mertens 1st intermediate `∑Λ(n)/n = log N + O(1)`
(coefficient exactly 1 — the upper half needs `ψ(N) = ∑Λ(n) ≤ C·N`). -/
theorem mertens_vonMangoldt_lower (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := cast_div_le_self N n
    calc ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ)
        ≤ ArithmeticFunction.vonMangoldt n * ((N : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hfloor hΛ
      _ = (N : ℝ) * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by ring
  rw [vonMangoldt_hyperbola] at hstep
  have hlow := le_sum_log (N := N) hN
  have hcomb : (N : ℝ) * (Real.log N - 1)
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    nlinarith [le_trans hlow hstep]
  exact le_of_mul_le_mul_left hcomb hpos

/-- **Sharp `∑ Λ(n)/n` upper bound**: `∑_{1≤n≤N} Λ(n)/n ≤ log N + (log 4 + 4)`. From the
hyperbola identity with `⌊N/n⌋ ≥ N/n − 1`, the Stirling upper bound `sum_log_le`, and the
Chebyshev `ψ`-bound `Chebyshev.psi_le_const_mul_self` (`∑_{n≤N} Λ(n) ≤ (log 4 + 4)·N`). -/
theorem mertens_vonMangoldt_upper (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ Real.log N + (Real.log 4 + 4) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  set S := ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) with hS
  set P := ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n with hP
  have hstep : (N : ℝ) * S - P
      ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) := by
    rw [hS, hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hfloor : (N : ℝ) / (n : ℝ) - 1 ≤ ((N / n : ℕ) : ℝ) := sub_one_le_cast_div N n hn.1
    have hmul : ArithmeticFunction.vonMangoldt n * ((N : ℝ) / n - 1)
        ≤ ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hfloor hΛ
    calc (N : ℝ) * (ArithmeticFunction.vonMangoldt n / n) - ArithmeticFunction.vonMangoldt n
        = ArithmeticFunction.vonMangoldt n * ((N : ℝ) / n - 1) := by ring
      _ ≤ _ := hmul
  rw [vonMangoldt_hyperbola] at hstep
  have hsl := sum_log_le (N := N)
  have hPle : P ≤ (Real.log 4 + 4) * (N : ℝ) := by
    have hpsi : Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n := by
      rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    have hsub : P ≤ Chebyshev.psi (N : ℝ) := by
      rw [hP, hpsi]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
      · intro i _ _; exact ArithmeticFunction.vonMangoldt_nonneg
    exact le_trans hsub (Chebyshev.psi_le_const_mul_self (by positivity))
  have hfin : (N : ℝ) * S ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith [le_trans hstep hsl, hPle]
  exact le_of_mul_le_mul_left hfin hpos

/-- **Sharp Mertens' first theorem (von Mangoldt form)**: `∑_{1≤n≤N} Λ(n)/n = log N + O(1)`,
with explicit `|·− log N| ≤ log 4 + 4`. This is the COEFFICIENT-1 estimate (unlike the
Chebyshev-`θ`-based `mertens_first_le`, whose constant is the lossy `log 4`), and the right
base for the sharp `∑_{p≤N}(log p)/p = log N + O(1)` (drop the convergent prime-power tail)
and ultimately `∑μ²/φ = Θ(log N)`. -/
theorem mertens_vonMangoldt_two_sided (N : ℕ) (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log N|
      ≤ Real.log 4 + 4 := by
  have hlo := mertens_vonMangoldt_lower N hN
  have hhi := mertens_vonMangoldt_upper N hN
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-- **von Mangoldt → prime split.** The full `∑_{n≤N} Λ(n)/n` decomposes as the prime
contribution `∑_{p≤N} (log p)/p` plus the proper-prime-power tail
`∑_{n≤N, IsPrimePow n ∧ ¬Prime n} Λ(n)/n`. Non-prime-powers contribute nothing
(`Λ = 0`), and on primes `Λ(p) = log p`. -/
theorem vonMangoldt_split_prime (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  have hprime : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt p / (p : ℝ)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  have htail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.2⟩
    · intro x hx hxni
      rw [Finset.mem_filter] at hx hxni
      have hnotPP : ¬ IsPrimePow x := fun hpp => hxni ⟨hx.1, hpp, hx.2⟩
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnotPP, zero_div]
  calc ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ArithmeticFunction.vonMangoldt p / (p : ℝ))
          + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
        (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime _).symm
    _ = _ := by rw [hprime, ← htail]

/-- **Sharp `∑_{p≤N}(log p)/p = log N + O(1)`, conditional on the prime-power tail bound.**
Given the convergent proper-prime-power tail bound (the in-flight `prime_power_tail_le`,
`∑_{n≤N, IsPrimePow ∧ ¬Prime} Λ(n)/n ≤ 1`), the sharp coefficient-1 estimate
`|∑_{p≤N}(log p)/p − log N| ≤ log 4 + 5` follows from `mertens_vonMangoldt_two_sided`
and `vonMangoldt_split_prime`. This is the COEFFICIENT-1 prime-sum estimate (unlike the
crude `mertens_first_le` with its lossy `log 4` constant). -/
theorem mertens_prime_log_two_sided_of (N : ℕ) (hN : 1 ≤ N)
    (htail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ 1) :
    |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) - Real.log N|
      ≤ Real.log 4 + 5 := by
  have hsplit := vonMangoldt_split_prime N
  have htwo := mertens_vonMangoldt_two_sided N hN
  have htail0 : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n),
      ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    refine Finset.sum_nonneg (fun n _ => ?_)
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  rw [abs_le] at htwo ⊢
  constructor <;> linarith [htwo.1, htwo.2]

/-! ## Sharp Mertens' second theorem `∑_{p≤N} 1/p = log log N + O(1)` (coefficient 1)

The **second** Abel-summation step (weight `1/log n`) turns the sharp coefficient-1
estimate `A n := ∑_{p≤n}(log p)/p = log n + O(1)` into the prime harmonic asymptotic
`∑_{p≤N} 1/p = log log N + O(1)`, again with the *correct* coefficient `1` on
`log log N` (the crude `mertens_second_term_bound` route loses it to `1 + 1/log 2`).
This is exactly what makes the Euler product `∏_{p≤N}(1 + 1/(p−1)) = O(log N)`
(hence `∑ μ²/φ = O(log N)`), since `exp(log log N + O(1)) = O(log N)` to the first
power. The bound is stated conditionally on the sharp prime-log upper half
(`A n ≤ log n + C`), which `mertens_prime_log_two_sided_of` supplies once the
prime-power tail bound lands. -/

/-- log-telescope identity: `∑_{2 ≤ n ≤ M}(1/log n − 1/log(n+1)) = 1/log 2 − 1/log(M+1)`. -/
theorem log_telescope_eq : ∀ M : ℕ, 1 ≤ M →
    ∑ n ∈ Finset.Icc 2 M, (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      = 1 / Real.log 2 - 1 / Real.log ((M : ℝ) + 1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
    have : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; ring

/-- log-telescope bound: `∑_{2 ≤ n ≤ N}(1/log n − 1/log(n+1)) ≤ 1/log 2`. -/
theorem log_telescope_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      ≤ 1 / Real.log 2 := by
  rcases Nat.lt_or_ge N 1 with h | h
  · have hN0 : N = 0 := by omega
    subst hN0; simp only [show Finset.Icc 2 0 = ∅ from rfl, Finset.sum_empty]; positivity
  · rw [log_telescope_eq N h]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have hlogpos : (0 : ℝ) < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
    have : (0 : ℝ) ≤ 1 / Real.log ((N : ℝ) + 1) := by positivity
    linarith

/-- per-term leading bound: for `n ≥ 2`, `log n·(1/log n − 1/log(n+1)) ≤ 1/(n log n)`. -/
theorem leading_term_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n : ℝ) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hL' : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hLL : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  have hdiff : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have heq : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by field_simp
    rw [heq]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have hlhs : Real.log (n : ℝ) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      = (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / Real.log ((n : ℝ) + 1) := by field_simp
  rw [hlhs]
  calc (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / Real.log ((n : ℝ) + 1)
      ≤ (1 / (n : ℝ)) / Real.log ((n : ℝ) + 1) := by gcongr
    _ = 1 / ((n : ℝ) * Real.log ((n : ℝ) + 1)) := by rw [div_div]
    _ ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- reindex: `∑_{m∈Icc 3 N} 1/(m log m) = ∑_{i∈Ico 2 N} 1/((i+1)log(i+1))`. -/
theorem reindex_inv_log (N : ℕ) :
    ∑ m ∈ Finset.Icc 3 N, 1 / ((m : ℝ) * Real.log (m : ℝ))
      = ∑ i ∈ Finset.Ico 2 N, 1 / (((i : ℝ) + 1) * Real.log ((i : ℝ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.lt_or_ge N 2 with h | h
    · interval_cases N <;> simp
    · rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ N + 1),
          Finset.sum_Ico_succ_top (by omega : 2 ≤ N), ih]
      push_cast; ring_nf

/-- leading sum: `∑_{n∈Icc 2 M} 1/(n log n) ≤ 1/(2 log2) + (loglog M − loglog 2)`, `M ≥ 2`.
Folds `sum_one_div_n_log_n_le` (the `∫ dt/(t log t)` comparison) through `reindex_inv_log`,
peeling the `n = 2` term. -/
theorem leading_sum_bound (M : ℕ) (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, 1 / ((n : ℝ) * Real.log (n : ℝ))
      ≤ 1 / ((2 : ℝ) * Real.log 2) + (Real.log (Real.log M) - Real.log (Real.log 2)) := by
  have hset : Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnotmem : (2 : ℕ) ∉ Finset.Icc 3 M := by simp [Finset.mem_Icc]
  rw [hset, Finset.sum_insert hnotmem, reindex_inv_log M]
  have hmain := sum_one_div_n_log_n_le (N := M) hM
  push_cast; linarith [hmain]

/-- **Second Abel-summation identity** (weight `1/log n`) for the prime-reciprocal sum:
`∑_{p≤N} 1/p = (∑_{p≤N}(log p)/p)/log N + ∑_{1≤n≤N-1}(∑_{p≤n}(log p)/p)·(1/log n − 1/log(n+1))`.
Pure rearrangement of `abel_summation_identity` with `aₙ = [n prime](log n)/n`,
`wₙ = 1/log n` (the `n=1` weight `1/log 1 = 0` is harmless since `A₁ = 0`). -/
theorem mertens2_abel (N : ℕ) :
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) / Real.log (N : ℝ)
        + ∑ n ∈ Finset.Icc 1 (N - 1),
            (∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
              * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
  have key : ∀ m : ℕ, (if m.Prime then Real.log (m : ℝ) / (m : ℝ) else 0) * (1 / Real.log (m : ℝ))
      = if m.Prime then (1 : ℝ) / (m : ℝ) else 0 := by
    intro m
    by_cases hp : m.Prime
    · simp only [hp, if_true]
      have hm1 : (1 : ℝ) < m := by exact_mod_cast hp.one_lt
      have hlog : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hm1)
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
    · simp [hp]
  have hfilter : ∀ M : ℕ, ∑ k ∈ Finset.Icc 1 M, (if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0)
      = ∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
    intro M; rw [Finset.sum_filter]
  have habel := abel_summation_identity N
      (fun n => if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0)
      (fun n => 1 / Real.log (n : ℝ))
  simp only [] at habel
  push_cast at habel
  have hLHS : ∑ n ∈ Finset.Icc 1 N,
        (if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0) * (1 / Real.log (n : ℝ))
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_filter]
  rw [hLHS] at habel
  rw [habel, hfilter N, mul_one_div]
  have hsum : ∑ n ∈ Finset.Icc 1 (N - 1),
        (∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
          * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      = - ∑ n ∈ Finset.Icc 1 (N - 1),
        (∑ k ∈ Finset.Icc 1 n, if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0)
          * (1 / Real.log ((n : ℝ) + 1) - 1 / Real.log (n : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hfilter n]; ring
  rw [hsum]; ring

/-- **Sharp Mertens' second theorem (upper bound, coefficient 1), conditional on the sharp
prime-log upper half.** Given `A n := ∑_{p≤n}(log p)/p ≤ log n + C` for all `n ≥ 1`
(supplied by `mertens_prime_log_two_sided_of` with `C = log 4 + 5` once the prime-power
tail bound lands), the second Abel step yields `∑_{p≤N} 1/p ≤ log log N + O(1)` with the
*correct* leading coefficient `1` on `log log N`. -/
theorem mertens2_upper_of (N : ℕ) (hN : 3 ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hAupper : ∀ n, 1 ≤ n →
        (∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log n + C) :
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log N)
        + (1 + 2 * (C / Real.log 2) + 1 / ((2 : ℝ) * Real.log 2) - Real.log (Real.log 2)) := by
  rw [mertens2_abel N]
  set A : ℕ → ℝ := fun n => ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
    with hAdef
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n; apply Finset.sum_nonneg; intro p hp
    rw [Finset.mem_filter] at hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)) (Nat.cast_nonneg _)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : (2 : ℕ) ≤ N))
  have hterm1 : A N / Real.log N ≤ 1 + C / Real.log 2 := by
    have h1 : A N / Real.log N ≤ (Real.log N + C) / Real.log N := by
      gcongr; exact hAupper N (by omega)
    rw [add_div, div_self (ne_of_gt hlogN)] at h1
    have h3 : C / Real.log N ≤ C / Real.log 2 := div_le_div_of_nonneg_left hC hlog2 hlogN2
    linarith
  have hA1 : A 1 = 0 := by
    rw [hAdef]; simp only
    rw [show (Finset.Icc 1 1).filter Nat.Prime = ∅ from by decide, Finset.sum_empty]
  have hsplit2 : ∑ n ∈ Finset.Icc 1 (N - 1),
        A n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      = ∑ n ∈ Finset.Icc 2 (N - 1),
        A n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hxni
      rw [Finset.mem_Icc] at hx hxni
      have hx1 : x = 1 := by omega
      subst hx1; rw [hA1]; ring
  rw [hsplit2]
  have hterm2 : ∑ n ∈ Finset.Icc 2 (N - 1),
        A n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.Icc 2 (N - 1),
        (1 / ((n : ℝ) * Real.log (n : ℝ))
          + C * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := hn.1
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hln1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hbn : 0 ≤ 1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hln hle
    have hAn := hAupper n (by omega)
    calc A n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
        ≤ (Real.log n + C) * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hAn hbn
      _ = Real.log n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
            + C * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ 1 / ((n : ℝ) * Real.log (n : ℝ))
            + C * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
          linarith [leading_term_bound n hn2]
  have hbig : ∑ n ∈ Finset.Icc 2 (N - 1),
        A n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1))
      ≤ (∑ n ∈ Finset.Icc 2 (N - 1), 1 / ((n : ℝ) * Real.log (n : ℝ)))
        + C * ∑ n ∈ Finset.Icc 2 (N - 1), (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
    refine le_trans hterm2 (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlead := leading_sum_bound (N - 1) (by omega)
  have htel := log_telescope_le (N - 1)
  have hCtel : C * ∑ n ∈ Finset.Icc 2 (N - 1),
      (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) ≤ C / Real.log 2 := by
    rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left htel hC
  have hloglogmono : Real.log (Real.log ((N - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log N) := by
    have h2 : (2 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ N - 1 := by omega
      exact_mod_cast this
    have hle1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : (N - 1 : ℕ) ≤ N := by omega
      exact_mod_cast this
    have hloglt : 0 < Real.log ((N - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    exact Real.log_le_log hloglt (Real.log_le_log (by linarith) hle1)
  linarith [hbig, hlead, hCtel, hloglogmono, hterm1]

end BoundedGaps.Mertens
