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

open scoped BigOperators
open ArithmeticFunction
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

end BoundedGaps.SingularSeries
