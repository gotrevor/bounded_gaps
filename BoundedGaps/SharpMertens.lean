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

/-! ## Reindexing the summatory function

`S(N) := ∑_{n≤N} g(n)`. From the keystone `∑_{e∣n} B(e) = n·g(n)` (so
`g(n) = (1/n)∑_{e∣n} B(e)`) and a divisor-pair swap, `S(N) = ∑_{e≤N}(B(e)/e)·H(⌊N/e⌋)`
with `H(M) = ∑_{m≤M} 1/m` the harmonic sum. This is the form on which the harmonic
bound + tail estimates assemble the sharp `log x + O(1)`. -/

/-- **Multiples reindex.** Summing `f` over `{n ∈ [1,N] : e ∣ n}` equals summing
`f(e·m)` over `m ∈ [1, ⌊N/e⌋]` (the bijection `n = e·m`). -/
lemma sum_filter_dvd_eq_sum_Icc_div {e N : ℕ} (he : 1 ≤ e) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), f n
      = ∑ m ∈ Finset.Icc 1 (N / e), f (e * m) := by
  refine Finset.sum_nbij' (fun n => n / e) (fun m => e * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd hn1 hdvd), Nat.div_le_div_right hnN⟩
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmN⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos he hm1, ?_⟩, dvd_mul_right e m⟩
    calc e * m = m * e := mul_comm e m
      _ ≤ N := (Nat.le_div_iff_mul_le he).mp hmN
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m he
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- **Generalized Dirichlet divisor-pair swap.** `∑_{n≤N} ∑_{d∣n} φ(d,n) =
∑_{d≤N} ∑_{m≤⌊N/d⌋} φ(d, d·m)` (reindex divisor pairs `n = d·m`). Generalizes
`SingularSeries.dirichlet_hyperbola` to weights depending on the outer index. -/
theorem sum_divisorpairs (N : ℕ) (φ : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, φ d n
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), φ d (d * m) := by
  have lhs_def : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, φ d n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ n then φ d n else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn1, le_trans (Nat.le_of_dvd hn1 hdvd) hnN⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [lhs_def, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  rw [← Finset.sum_filter]
  exact sum_filter_dvd_eq_sum_Icc_div hd1 (φ d)

/-- **Weighted-harmonic form of the summatory function.**
`∑_{n≤N} μ²(n)/φ(n) = ∑_{e≤N} (B(e)/e)·∑_{m≤⌊N/e⌋} 1/m`. The entry point to the
sharp `log x + O(1)` (harmonic bound on the inner sum + tail estimates on `B(e)/e`). -/
theorem sum_g_eq_weighted_harmonic (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n
      = ∑ e ∈ Finset.Icc 1 N,
          (BSharp e / (e : ℝ)) * (∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) := by
  have step1 : ∀ n ∈ Finset.Icc 1 N,
      gMoebiusSqTotient n = ∑ d ∈ n.divisors, BSharp d / (n : ℝ) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1; positivity
    rw [gMoebiusSqTotient_apply, ← Finset.sum_div, sum_divisors_BSharp n]
    exact (mul_div_cancel_left₀ _ hn0).symm
  calc ∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, BSharp d / (n : ℝ) :=
        Finset.sum_congr rfl step1
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), BSharp d / ((d * m : ℕ) : ℝ) :=
        sum_divisorpairs N (fun d n => BSharp d / (n : ℝ))
    _ = ∑ e ∈ Finset.Icc 1 N,
          (BSharp e / (e : ℝ)) * (∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : (d : ℝ) ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; positivity
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : (m : ℝ) ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; positivity
        push_cast
        rw [div_mul_div_comm, mul_one]
