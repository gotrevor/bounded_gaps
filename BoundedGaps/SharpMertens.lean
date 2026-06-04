/-
# Sharp Mertens `∑_{n≤x} μ²(n)/φ(n) = log x + O(1)` — algebraic core.

GPY/Maynard sub-step (c) needs the sieve sum `∑μ²/φ ∼ log x` with **leading
coefficient exactly 1** (so `α = I(F)`). The crude two-sided `Θ(log N)` bound in
`BoundedGaps.Mertens` (`mertens_theta_log`, coefficient `≈ e^γ ≠ 1`) is not enough.

The sharp result comes from factoring out `ζ(s+1)` (NOT `ζ(s)`): with
`g(n) = μ²(n)/φ(n)`, the Dirichlet series `∑ g(n) n^{-s} = ζ(s+1)·G(s)` with `G`
convergent near `s=0` and `G(0)=1`. At the arithmetic-function level this is the
factorization `g = u ⋆ B` (`u(n)=1/n`), equivalently — defining `B := μ ⋆ (id·g)` —
the **keystone divisor identity**

  `∑_{e ∣ n} B(e) = n · μ²(n)/φ(n)`.            (★)

This module establishes (★) (pure Dirichlet algebra: `ζ⋆B = (ζ⋆μ)⋆(id·g) = id·g`),
together with `B`'s multiplicativity and explicit prime-power values
`B(1)=1, B(p)=1/(p−1), B(p²)=−p/(p−1), B(p^k)=0 (k≥3)`. The analytic assembly
(reindex `S(x)=∑_{e≤x}(B(e)/e)H(⌊x/e⌋)`, three tail estimates, harmonic bound)
builds on this. See `SHARP_MERTENS_RECONSTRUCTION.md`.
-/
import Mathlib
import BoundedGaps.SingularSeries

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace BoundedGaps.SharpMertens

open BoundedGaps.SingularSeries

/-- The identity arithmetic function over `ℝ`, `idR n = n`. -/
noncomputable def idR : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ), by simp⟩

@[simp] lemma idR_apply (n : ℕ) : idR n = (n : ℝ) := rfl

lemma idR_isMultiplicative : idR.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [idR_apply]
  push_cast; ring

/-- `idG n = n · g(n) = n · μ²(n)/φ(n)`, the pointwise product `id · g`. -/
noncomputable def idG : ArithmeticFunction ℝ := idR.pmul gMoebiusSqTotient

@[simp] lemma idG_apply (n : ℕ) :
    idG n = (n : ℝ) * ((ArithmeticFunction.moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ)) := by
  rw [idG, ArithmeticFunction.pmul_apply, idR_apply, gMoebiusSqTotient_apply]

lemma idG_isMultiplicative : idG.IsMultiplicative :=
  idR_isMultiplicative.pmul gMoebiusSqTotient_isMultiplicative

/-- `B := μ ⋆ (id·g)`, the Möbius inverse of `n ↦ n·μ²(n)/φ(n)`. -/
noncomputable def BSharp : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * idG

lemma BSharp_isMultiplicative : BSharp.IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_moebius.intCast).mul idG_isMultiplicative

/-- **The clean Dirichlet algebra**: `ζ ⋆ B = (ζ ⋆ μ) ⋆ (id·g) = id·g`. -/
lemma zeta_mul_BSharp : ((ζ : ArithmeticFunction ℝ) * BSharp) = idG := by
  rw [BSharp, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

/-- **Keystone divisor identity (★).** For every `n`,
`∑_{e ∣ n} B(e) = n · μ²(n)/φ(n)`. Holds at `n=0` too (both sides `0`). -/
theorem sum_divisors_BSharp (n : ℕ) :
    ∑ e ∈ n.divisors, BSharp e
      = (n : ℝ) * ((ArithmeticFunction.moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ)) := by
  have h : ((ζ : ArithmeticFunction ℝ) * BSharp) n = idG n := by rw [zeta_mul_BSharp]
  rwa [ArithmeticFunction.coe_zeta_mul_apply, idG_apply] at h

/-- The divisor sum of `B` over `p^i` is the partial sum `∑_{j≤i} B(p^j) = idG(p^i)`. -/
lemma sum_range_BSharp_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), BSharp (p ^ j) = idG (p ^ i) := by
  have h := sum_divisors_BSharp (p ^ i)
  rw [Nat.divisors_prime_pow hp, Finset.sum_map] at h
  simp only [Function.Embedding.coeFn_mk] at h
  rw [idG_apply]; exact h

/-- `idG` at prime powers: `idG(p^0)=1`, `idG(p^1)=p/(p−1)`, `idG(p^i)=0 (i≥2)`. -/
lemma idG_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    idG (p ^ i) = if i = 0 then 1 else if i = 1 then (p : ℝ) / ((p : ℝ) - 1) else 0 := by
  have hg : idG (p ^ i) = ((p ^ i : ℕ) : ℝ) * gMoebiusSqTotient (p ^ i) := by
    rw [idG, ArithmeticFunction.pmul_apply, idR_apply]
  rw [hg, gMoebiusSqTotient_prime_pow hp]
  rcases i with _ | _ | i
  · simp
  · rw [if_neg (by norm_num), if_pos rfl, if_neg (by norm_num), if_pos rfl, pow_one, mul_one_div]
  · simp

/-- Reduced value `idG(p^0)=1`. -/
lemma idG_pp0 {p : ℕ} (hp : p.Prime) : idG (p ^ 0) = 1 := by rw [idG_prime_pow hp]; norm_num
/-- Reduced value `idG(p^1)=p/(p−1)`. -/
lemma idG_pp1 {p : ℕ} (hp : p.Prime) : idG (p ^ 1) = (p : ℝ) / ((p : ℝ) - 1) := by
  rw [idG_prime_pow hp]; norm_num
/-- Reduced value `idG(p^i)=0` for `i ≥ 2`. -/
lemma idG_pp_ge2 {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 2 ≤ i) : idG (p ^ i) = 0 := by
  rw [idG_prime_pow hp, if_neg (by omega), if_neg (by omega)]

/-- **Recurrence for `B` on prime powers**: `B(p^{i+1}) = idG(p^{i+1}) − idG(p^i)`. -/
lemma BSharp_prime_pow_succ {p : ℕ} (hp : p.Prime) (i : ℕ) :
    BSharp (p ^ (i + 1)) = idG (p ^ (i + 1)) - idG (p ^ i) := by
  have h1 := sum_range_BSharp_prime_pow hp (i + 1)
  have h2 := sum_range_BSharp_prime_pow hp i
  rw [Finset.sum_range_succ] at h1
  linarith

/-- `B(1) = 1`. -/
@[simp] lemma BSharp_one : BSharp 1 = 1 := BSharp_isMultiplicative.1

/-- `B(p^1) = 1/(p−1)` for a prime `p`. -/
lemma BSharp_prime {p : ℕ} (hp : p.Prime) : BSharp (p ^ 1) = 1 / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [BSharp_prime_pow_succ hp 0, idG_pp1 hp, idG_pp0 hp]
  field_simp
  ring

/-- `B(p²) = −p/(p−1)` for a prime `p`. -/
lemma BSharp_prime_sq {p : ℕ} (hp : p.Prime) : BSharp (p ^ 2) = -(p : ℝ) / ((p : ℝ) - 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, BSharp_prime_pow_succ hp 1,
      idG_pp_ge2 (i := 1 + 1) hp (by norm_num), idG_pp1 hp]
  ring

/-- `B(p^k) = 0` for `k ≥ 3` and `p` prime. -/
lemma BSharp_prime_pow_high {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k) : BSharp (p ^ k) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rw [BSharp_prime_pow_succ hp, idG_pp_ge2 (i := i + 1) hp (by omega),
      idG_pp_ge2 (i := i) hp (by omega), sub_zero]
