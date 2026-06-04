/-
# Singular-series building blocks (GPY/Maynard sub-step (c) corner).

Multiplicative-function identities feeding the singular series `𝔖` and the
Mertens-type summations of the sieve main term. The keystone here is the
exact divisor identity

  `n / φ(n) = ∑_{d ∣ n} μ(d)² / φ(d)`,

the finite (per-`n`) shadow of the Euler product `n/φ(n) = ∏_{p∣n} p/(p-1)`.
It is proved as the Dirichlet convolution `ζ ⋆ (μ²/φ) = id/φ` of two real
arithmetic functions, checked on prime powers via
`IsMultiplicative.eq_iff_eq_on_prime_powers`.

This is companion infrastructure to `BoundedGaps.Mertens` (the `∑ μ²/φ = Θ(log N)`
core) and to `ANALYTIC_AXIOM_BURNDOWN.md` sub-step (c). Kept in a separate module
so the heavy `Mertens.lean` need not recompile while it grows.
-/
import Mathlib
import BoundedGaps.Mertens

open scoped BigOperators
open ArithmeticFunction Filter Asymptotics
open scoped ArithmeticFunction.zeta

namespace BoundedGaps.SingularSeries

/-- `g(d) = μ(d)²/φ(d)` as a real arithmetic function (the Selberg/singular-series
summand). -/
noncomputable def gMoebiusSqTotient : ArithmeticFunction ℝ :=
  ⟨fun d => (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ), by simp⟩

/-- `h(d) = d/φ(d)` as a real arithmetic function. -/
noncomputable def hSelfTotient : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ) / (Nat.totient d : ℝ), by simp⟩

@[simp] lemma gMoebiusSqTotient_apply (d : ℕ) :
    gMoebiusSqTotient d = (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) := rfl
@[simp] lemma hSelfTotient_apply (d : ℕ) :
    hSelfTotient d = (d : ℝ) / (Nat.totient d : ℝ) := rfl

lemma gMoebiusSqTotient_isMultiplicative : gMoebiusSqTotient.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  simp only [gMoebiusSqTotient_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.2 hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_pow, div_mul_div_comm]

lemma hSelfTotient_isMultiplicative : hSelfTotient.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  simp only [hSelfTotient_apply]
  rw [Nat.totient_mul hmn]
  push_cast
  rw [div_mul_div_comm]

/-- `g(p^j)` is `1` at `j=0`, `1/(p-1)` at `j=1`, and `0` for `j ≥ 2`. -/
lemma gMoebiusSqTotient_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    gMoebiusSqTotient (p ^ j) = if j = 0 then 1 else if j = 1 then 1 / ((p : ℝ) - 1) else 0 := by
  have hple : (1 : ℕ) ≤ p := hp.one_le
  rcases j with _ | _ | j
  · simp
  · rw [if_neg (by norm_num), if_pos rfl, pow_one, gMoebiusSqTotient_apply,
      ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hple, Nat.cast_one]
    norm_num
  · rw [if_neg (by omega), if_neg (by omega), gMoebiusSqTotient_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp

/-- The Dirichlet convolution `ζ ⋆ (μ²/φ) = id/φ`. -/
lemma zeta_mul_gMoebiusSqTotient :
    ((ζ : ArithmeticFunction ℝ) * gMoebiusSqTotient) = hSelfTotient := by
  have hmul : ((ζ : ArithmeticFunction ℝ) * gMoebiusSqTotient).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul gMoebiusSqTotient_isMultiplicative
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
      hSelfTotient_isMultiplicative]
  intro p i hp
  have hple : (1 : ℕ) ≤ p := hp.one_le
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rcases i with _ | i
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    rw [Finset.sum_eq_zero (fun j _ => by
      rw [gMoebiusSqTotient_prime_pow hp, if_neg (by omega), if_neg (by omega)])]
    rw [gMoebiusSqTotient_prime_pow hp, gMoebiusSqTotient_prime_pow hp]
    simp only [if_neg (by norm_num : (0 + 1 : ℕ) ≠ 0)]
    rw [hSelfTotient_apply, Nat.totient_prime_pow hp (Nat.succ_pos i)]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hpne : (p : ℝ) ≠ 0 := by positivity
    push_cast [Nat.cast_sub hple]
    field_simp
    ring

/-- **Singular-series building block.** For every `n`,
`n / φ(n) = ∑_{d ∣ n} μ(d)² / φ(d)`. (The finite shadow of the Euler product
`n/φ(n) = ∏_{p∣n} p/(p-1)`.) Holds for `n = 0` too, both sides being `0`. -/
theorem self_div_totient_eq_sum_moebiusSq_div_totient (n : ℕ) :
    (n : ℝ) / (Nat.totient n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) := by
  have h : ((ζ : ArithmeticFunction ℝ) * gMoebiusSqTotient) n = hSelfTotient n := by
    rw [zeta_mul_gMoebiusSqTotient]
  rw [ArithmeticFunction.coe_zeta_mul_apply, hSelfTotient_apply] at h
  simp only [gMoebiusSqTotient_apply] at h
  exact h.symm

/-- **General Dirichlet hyperbola interchange.** Summing any `g : ℕ → ℝ` over the
divisors of each `n ∈ [1, N]` and then over `n` equals summing `g d` weighted by
the count `⌊N/d⌋` of multiples of `d` in `[1, N]`:
`∑_{n=1}^N ∑_{d∣n} g d = ∑_{d=1}^N g d · ⌊N/d⌋`. (Proved on Aristotle job
`627d10e3`; verified kernel-clean under v4.29.1.) -/
theorem dirichlet_hyperbola (N : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, g d)
      = ∑ d ∈ Finset.Icc 1 N, g d * ((N / d : ℕ) : ℝ) := by
  have lhs_def : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, g d
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ n then g d else 0 := by
    rw [Finset.sum_congr rfl]
    intro x hx; rw [← Finset.sum_filter]; congr; ext; simp +decide [Nat.mem_divisors]
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
    exact ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hx1,
        Nat.le_trans (Nat.le_of_dvd hx1 h.1) hx2⟩, h.1⟩,
      fun h => ⟨h.2, by linarith⟩⟩
  rw [lhs_def, Finset.sum_comm, Finset.sum_congr rfl]
  simp +contextual [Finset.sum_ite, mul_comm]
  exact fun x _ _ => Or.inl <| Nat.Ioc_filter_dvd_card_eq_div N x

/-- **Hyperbola form of the `∑ n/φ(n)` summatory function.** Combining the
singular-series keystone `n/φ(n) = ∑_{d∣n} μ²(d)/φ(d)` with the Dirichlet
hyperbola: the average of `n/φ(n)` is a weighted divisor sum,
`∑_{n=1}^N n/φ(n) = ∑_{d=1}^N (μ²(d)/φ(d)) · ⌊N/d⌋`. This is the entry point to
the singular-series constant (the main term of `∑ n/φ(n) ∼ A·N`). -/
theorem sum_self_div_totient_eq_weighted (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ)) * ((N / d : ℕ) : ℝ) := by
  rw [← dirichlet_hyperbola N
    (fun d => (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ))]
  exact Finset.sum_congr rfl (fun n _ => self_div_totient_eq_sum_moebiusSq_div_totient n)

/-- `|⌊N/d⌋ − N/d| ≤ 1` for `d ≥ 1` (the boundary error). -/
lemma abs_floorDiv_sub_div_le_one (N d : ℕ) (hd : 1 ≤ d) :
    |(((N / d : ℕ) : ℝ)) - (N : ℝ) / d| ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdm : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N d
  have hmod : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N (by omega)
  have hkey : (N : ℝ) / d - ((N / d : ℕ) : ℝ) = ((N % d : ℕ) : ℝ) / d := by
    field_simp; linarith [hdm]
  have hfrac0 : (0 : ℝ) ≤ ((N % d : ℕ) : ℝ) / d := by positivity
  have hfrac1 : ((N % d : ℕ) : ℝ) / d < 1 := (div_lt_one hd0).mpr hmod
  rw [abs_le]; constructor <;> linarith

/-- **Main-term split for `∑ n/φ(n)`.** Replacing `⌊N/d⌋` by `N/d` in the
hyperbola form costs at most `∑_{d≤N} μ²(d)/φ(d)`:
`|∑_{n≤N} n/φ(n) − N·∑_{d≤N} μ²(d)/(φ(d)·d)| ≤ ∑_{d≤N} μ²(d)/φ(d)`.
With `mertens_theta_log` (`∑μ²/φ = O(log N)`, `BoundedGaps.Mertens`) this gives the
`O(log N)` error of `∑ n/φ(n) = (singular sum)·N + O(log N)`. -/
theorem sum_self_div_totient_main_split (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)
        - (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) * (d : ℝ))|
      ≤ ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) := by
  rw [sum_self_div_totient_eq_weighted, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hreg : ∀ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) * ((N / d : ℕ) : ℝ)
        - (N : ℝ) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) * (d : ℝ)))
      = (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ)
          * (((N / d : ℕ) : ℝ) - (N : ℝ) / d) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  rw [Finset.sum_congr rfl hreg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hnn : (0 : ℝ) ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hnn]
  calc (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ)
          * |((N / d : ℕ) : ℝ) - (N : ℝ) / d|
      ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (abs_floorDiv_sub_div_le_one N d hd1) hnn
    _ = (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) := by ring

/-- Partial sums of the singular sum `∑_{d≤N} μ²(d)/(φ(d)·d)` (the main-term
coefficient of `∑ n/φ(n)`). -/
noncomputable def singularSumPartial (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) * (d : ℝ))

/-- **Uniform bound on the singular sum**: `∑_{d≤N} μ²(d)/(φ(d)·d) ≤ 3` for all `N`.
Euler-product route: only squarefree `d` contribute, the term factors as
`∏_{p∣d} 1/(p(p−1))`, the squarefree-divisor sum is sub-dominated by
`∏_{p≤N}(1+1/(p(p−1))) ≤ exp(∑_p 1/(p(p−1))) ≤ exp 1 < 3` (telescoping `1/(k(k−1))`).
Proved on Aristotle job `36bb3493` (`singular_sum_bounded`); verified `#print axioms`
clean `[propext, Classical.choice, Quot.sound]` in our v4.29.1 kernel before porting. -/
theorem singular_sum_bounded (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) ^ 2 / ((Nat.totient d : ℝ) * (d : ℝ)) ≤ 3 := by
  suffices h2 : (∑ d ∈ Finset.Icc 1 N,
      (if Squarefree d then (1 : ℝ) / (d.totient * d) else 0)) ≤ Real.exp 1 by
    refine le_trans ?_ ( h2.trans ?_ );
    · gcongr;
      split_ifs <;> simp_all +decide [ ArithmeticFunction.moebius ];
      norm_num [ ← pow_mul, mul_comm ];
    · exact Real.exp_one_lt_d9.le.trans <| by norm_num;
  have h_prod : (∑ d ∈ Finset.Icc 1 N, if Squarefree d then (1 : ℝ) / (d.totient * d) else 0) ≤ (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (1 + 1 / ((p : ℝ) * (p - 1)))) := by
    have h_squarefree_prod : ∑ d ∈ Finset.Icc 1 N, (if Squarefree d then (1 : ℝ) / ((d.totient) * d) else 0) ≤ ∑ d ∈ Finset.filter Squarefree (Finset.Icc 1 N), (∏ p ∈ Nat.primeFactors d, (1 : ℝ) / ((p * (p - 1)) : ℝ)) := by
      have h_squarefree_prod : ∀ d ∈ Finset.filter Squarefree (Finset.Icc 1 N), (1 : ℝ) / ((d.totient) * d) = ∏ p ∈ Nat.primeFactors d, (1 : ℝ) / ((p * (p - 1)) : ℝ) := by
        intro d hd; rw [ Nat.totient_eq_div_primeFactors_mul ] ; simp +decide [ Finset.prod_mul_distrib, mul_comm ] ;
        rw [ Nat.prod_primeFactors_of_squarefree ( Finset.mem_filter.mp hd |>.2 ) ] ; ring;
        rw [ Nat.div_self ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hd |>.1 ) |>.1 ) ] ; norm_num [ neg_add_eq_sub, Finset.prod_congr rfl fun x hx => Nat.cast_pred <| Nat.pos_of_mem_primeFactors hx ] ; ring;
        exact Or.inl <| by rw [ ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree <| Finset.mem_filter.mp hd |>.2 ] ;
      rw [ Finset.sum_filter ] ; exact Finset.sum_le_sum fun x hx => by aesop;
    have h_subset_prod : ∑ d ∈ Finset.filter Squarefree (Finset.Icc 1 N), (∏ p ∈ Nat.primeFactors d, (1 : ℝ) / ((p * (p - 1)) : ℝ)) ≤ ∑ s ∈ Finset.powerset (Finset.filter Nat.Prime (Finset.Icc 2 N)), (∏ p ∈ s, (1 : ℝ) / ((p * (p - 1)) : ℝ)) := by
      have h_subset_prod : Finset.image (fun d => Nat.primeFactors d) (Finset.filter Squarefree (Finset.Icc 1 N)) ⊆ Finset.powerset (Finset.filter Nat.Prime (Finset.Icc 2 N)) := by
        simp +decide [ Finset.subset_iff ];
        rintro _ x hx₁ hx₂ hx₃ rfl y hy; exact ⟨ ⟨ Nat.Prime.two_le ( Nat.prime_of_mem_primeFactors hy ), Nat.le_trans ( Nat.le_of_mem_primeFactors hy ) hx₂ ⟩, Nat.prime_of_mem_primeFactors hy ⟩ ;
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg h_subset_prod _ );
      · rw [ Finset.sum_image ];
        intro x hx y hy; simp_all +decide [ Nat.primeFactors_mul ] ;
        intro h; have := Nat.prod_primeFactors_of_squarefree hx.2; have := Nat.prod_primeFactors_of_squarefree hy.2; aesop;
      · exact fun _ _ _ => Finset.prod_nonneg fun p hp => one_div_nonneg.2 <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.2 <| Nat.one_le_cast.2 <| Nat.Prime.pos <| Finset.mem_filter.1 ( Finset.mem_powerset.1 ‹_› hp ) |>.2;
    convert h_squarefree_prod.trans h_subset_prod using 1;
    simp +decide [ add_comm ( 1 : ℝ ), Finset.prod_add ];
  have h_exp : (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (1 + 1 / ((p : ℝ) * (p - 1)))) ≤ Real.exp (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (1 / ((p : ℝ) * (p - 1)))) := by
    rw [ Real.exp_sum ] ; exact Finset.prod_le_prod ( fun _ _ => by exact add_nonneg zero_le_one <| one_div_nonneg.mpr <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by aesop ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
  have h_sum : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (1 / ((p : ℝ) * (p - 1)))) ≤ 1 := by
    have h_sum_le : (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 N), (1 / ((p : ℝ) * (p - 1)))) ≤ (∑ k ∈ Finset.Icc 2 N, (1 / ((k : ℝ) * (k - 1)))) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => one_div_nonneg.2 <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.2 <| Nat.one_le_cast.2 <| by linarith [ Finset.mem_Icc.1 ‹_› ] ;
    have h_telescope : ∀ N : ℕ, N ≥ 2 → (∑ k ∈ Finset.Icc 2 N, (1 / ((k : ℝ) * (k - 1)))) = 1 - 1 / (N : ℝ) := by
      intro N hN; induction hN <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
      rw [ Finset.sum_Ioc_succ_top ( by linarith ), ‹∑ x ∈ Finset.Ioc 1 _, _ = _› ] ; norm_num;
      field_simp
      ring;
    exact h_sum_le.trans ( if hN : N ≥ 2 then h_telescope N hN ▸ sub_le_self _ ( by positivity ) else by interval_cases N <;> norm_num );
  exact (h_prod.trans h_exp).trans (Real.exp_le_exp.mpr h_sum)


/-- **The singular sum converges.** Being monotone (nonnegative terms) and bounded
above, the partial sums `∑_{d≤N} μ²(d)/(φ(d)·d)` converge to their supremum `A`
(which then dominates every partial sum). The boundedness hypothesis is supplied by
the Euler-product comparison `∑_{d≤N} μ²(d)/(φ(d)·d) ≤ 3` (Aristotle `36bb3493`);
the limit `A` is the singular-series constant `ζ(2)ζ(3)/ζ(6)` of `∑ n/φ(n) ∼ A·N`. -/
theorem singularSum_tendsto_of_bounded {C : ℝ} (hC : ∀ N, singularSumPartial N ≤ C) :
    ∃ A : ℝ, Filter.Tendsto singularSumPartial Filter.atTop (nhds A)
        ∧ ∀ N, singularSumPartial N ≤ A := by
  have hmono : Monotone singularSumPartial := by
    intro a b hab
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hab)
    intro d _ _; positivity
  have hbdd : BddAbove (Set.range singularSumPartial) := ⟨C, by rintro x ⟨N, rfl⟩; exact hC N⟩
  refine ⟨⨆ N, singularSumPartial N, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  intro N; exact le_ciSup hbdd N

/-- **Average order of `n/φ(n)` (`∑_{n≤N} n/φ(n) ∼ A·N`).** Conditional on the
uniform bound on the singular sum (Aristotle `36bb3493`, `≤ 3`), the Cesàro average
`(∑_{n≤N} n/φ(n))/N` converges to the singular-series constant
`A = ∑_d μ²(d)/(φ(d)·d) = ζ(2)ζ(3)/ζ(6)`. Proof: the main-term split gives
`(∑n/φ(n))/N = T(N) + O((∑μ²/φ)/N)`, and `∑μ²/φ = O(log N) = o(N)`
(`BoundedGaps.Mertens.mertens_isTheta_log` ∘ `log =o id`), so the error vanishes and
`T(N) → A`. The classical average order of Euler's totient, fully machine-checked. -/
theorem sum_self_div_totient_asymptotic {C : ℝ} (hbound : ∀ N, singularSumPartial N ≤ C) :
    ∃ A : ℝ, Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)) / (N : ℝ))
      Filter.atTop (nhds A) := by
  obtain ⟨A, hA, _⟩ := singularSum_tendsto_of_bounded hbound
  refine ⟨A, ?_⟩
  set avg : ℕ → ℝ :=
    fun N => (∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)) / (N : ℝ) with havg
  have hlogo : (fun N : ℕ => Real.log (N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hmo : (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N, BoundedGaps.Mertens.mertensSummand d)
      =o[atTop] (fun N : ℕ => (N : ℝ)) :=
    (BoundedGaps.Mertens.mertens_isTheta_log.isBigO).trans_isLittleO hlogo
  have hgtend : Tendsto
      (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, BoundedGaps.Mertens.mertensSummand d) / (N : ℝ))
      atTop (nhds 0) := hmo.tendsto_div_nhds_zero
  have herr : Tendsto (fun N => avg N - singularSumPartial N) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgtend
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hsplit := sum_self_div_totient_main_split N
    have hbridge :
        (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ))
          = ∑ d ∈ Finset.Icc 1 N, BoundedGaps.Mertens.mertensSummand d := rfl
    have heq : avg N - singularSumPartial N
        = (∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)
            - N * singularSumPartial N) / N := by
      rw [havg]; field_simp
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hN0, div_le_div_iff_of_pos_right hN0]
    calc |∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ) - N * singularSumPartial N|
        ≤ ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) :=
          hsplit
      _ = ∑ d ∈ Finset.Icc 1 N, BoundedGaps.Mertens.mertensSummand d := hbridge
  have hsum : Tendsto (fun N => singularSumPartial N + (avg N - singularSumPartial N))
      atTop (nhds (A + 0)) := hA.add herr
  have hcongr : (fun N => singularSumPartial N + (avg N - singularSumPartial N)) = avg := by
    funext N; ring
  rw [hcongr, add_zero] at hsum
  exact hsum

/-- **The singular sum converges (unconditional).** Instantiating
`singularSum_tendsto_of_bounded` with the now-proven uniform bound
`singular_sum_bounded` (`≤ 3`): the partial sums `∑_{d≤N} μ²(d)/(φ(d)·d)` converge to
their supremum `A = ζ(2)ζ(3)/ζ(6)`. -/
theorem singularSum_converges :
    ∃ A : ℝ, Filter.Tendsto singularSumPartial Filter.atTop (nhds A)
        ∧ ∀ N, singularSumPartial N ≤ A :=
  singularSum_tendsto_of_bounded (fun N => singular_sum_bounded N)

/-- **Average order of `n/φ(n)` (unconditional): `∑_{n≤N} n/φ(n) ∼ A·N`.**
The classical average order of Euler's totient, now fully machine-checked with no
remaining hypotheses (the `≤ 3` singular-sum bound is `singular_sum_bounded`).
`A = ∑_d μ²(d)/(φ(d)·d) = ζ(2)ζ(3)/ζ(6)`. -/
theorem sum_self_div_totient_asymptotic_uncond :
    ∃ A : ℝ, Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (Nat.totient n : ℝ)) / (N : ℝ))
      Filter.atTop (nhds A) :=
  sum_self_div_totient_asymptotic (fun N => singular_sum_bounded N)

end BoundedGaps.SingularSeries
