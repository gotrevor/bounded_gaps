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

/-! ## The harmonic remainder

In the weighted-harmonic form `S(N) = ∑_{e≤N}(B(e)/e)·H(⌊N/e⌋)`, replace the inner
harmonic sum `H(⌊N/e⌋)` by `log(N/e)`. The remainder lies in `[0,1]` uniformly
(mathlib's two-sided floor-harmonic bound), so `∑_e b(e)·remainder_e = O(∑|b(e)|) = O(1)`
once the b-series is shown absolutely bounded (Aristotle job `830e5129`). -/

/-- **Harmonic remainder bound.** For `1 ≤ e ≤ N`,
`log(N/e) ≤ ∑_{m≤⌊N/e⌋} 1/m ≤ 1 + log(N/e)` (so the remainder is in `[0,1]`). -/
lemma harmonic_remainder_mem {N e : ℕ} (he : 1 ≤ e) (heN : e ≤ N) :
    Real.log ((N : ℝ) / (e : ℝ)) ≤ (∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m)
      ∧ (∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) ≤ 1 + Real.log ((N : ℝ) / (e : ℝ)) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hy1 : (1 : ℝ) ≤ (N : ℝ) / (e : ℝ) := by
    rw [le_div_iff₀ he0, one_mul]; exact_mod_cast heN
  have hfloor : ⌊(N : ℝ) / (e : ℝ)⌋₊ = N / e := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hH : (harmonic (N / e) : ℝ) = ∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m :=
    BoundedGaps.Mertens.harmonic_eq_icc_sum (N / e)
  refine ⟨?_, ?_⟩
  · have h := log_le_harmonic_floor ((N : ℝ) / (e : ℝ)) (by positivity)
    rwa [hfloor, hH] at h
  · have h := harmonic_floor_le_one_add_log ((N : ℝ) / (e : ℝ)) hy1
    rwa [hfloor, hH] at h

/-- **Decomposition of the summatory function.** Writing `H(⌊N/e⌋) = log(N/e) + r_e`
and `log(N/e) = log N − log e`,
`∑_{n≤N} μ²(n)/φ(n) = P(N)·log N − Q(N) + R(N)` with
`P(N) = ∑_{e≤N} B(e)/e`, `Q(N) = ∑_{e≤N} (B(e)/e)·log e`,
`R(N) = ∑_{e≤N} (B(e)/e)·r_e` (`r_e = H(⌊N/e⌋) − log(N/e) ∈ [0,1]`).
**This reduces the sharp Mertens `= log x + O(1)` to three facts**: `P(N) → 1`
(signed b-series sum, telescoping Euler product), `Q(N) = O(1)` and `R(N) = O(1)`
(both from `∑|b(e)| < ∞`, Aristotle `830e5129`). -/
theorem sum_g_decomp (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n
      = (∑ e ∈ Finset.Icc 1 N, BSharp e / (e : ℝ)) * Real.log N
        - (∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) * Real.log e)
        + ∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) *
            ((∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) - Real.log ((N : ℝ) / (e : ℝ))) := by
  rw [sum_g_eq_weighted_harmonic N, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.log_div hN0 he0]
  ring

/-- **The remainder term `R(N)` is `O(1)`.** `|R(N)| ≤ ∑_{e≤N} |B(e)/e|`, since each
`r_e ∈ [0,1]`. Combined with the absolute b-series bound (`∑|b(e)| ≤ 8`, Aristotle
`830e5129`) this gives `|R(N)| ≤ 8`, one of the two `O(1)` error terms of `sum_g_decomp`. -/
theorem abs_remainder_term_le (N : ℕ) :
    |∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) *
        ((∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) - Real.log ((N : ℝ) / (e : ℝ)))|
      ≤ ∑ e ∈ Finset.Icc 1 N, |BSharp e / (e : ℝ)| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
  rw [abs_mul]
  have hr := harmonic_remainder_mem he1 heN
  have hr01 : |(∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) - Real.log ((N : ℝ) / (e : ℝ))| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  calc |BSharp e / (e : ℝ)|
          * |(∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) - Real.log ((N : ℝ) / (e : ℝ))|
        ≤ |BSharp e / (e : ℝ)| * 1 := mul_le_mul_of_nonneg_left hr01 (abs_nonneg _)
    _ = |BSharp e / (e : ℝ)| := mul_one _

/-- **The `log`-weighted term `Q(N)` is controlled by the `log`-weighted b-series.**
`|Q(N)| ≤ ∑_{e≤N} |B(e)/e|·|log e|`. The RHS is bounded (`∑ |b(e) log e| < ∞`, terms
`≪ p^{-2} log p`) — a future Euler-product estimate — giving the second `O(1)` error
term of `sum_g_decomp`. -/
theorem abs_logweighted_term_le (N : ℕ) :
    |∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) * Real.log e|
      ≤ ∑ e ∈ Finset.Icc 1 N, |BSharp e / (e : ℝ)| * |Real.log e| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum (fun e _ => le_of_eq (abs_mul _ _))

/-! ## The main coefficient `P(N) = ∑_{e≤N} b(e) → 1` (signed Euler product)

`b(e) = B(e)/e` as an `ArithmeticFunction ℝ` (`bAF`). It is multiplicative, and
`∑'_e b(p^e) = 1 + b(p) + b(p²) = 1` at every prime (the local Euler factor is exactly
`1`). So mathlib's Euler product `∏'_p (∑'_e b(p^e)) = ∑'_n b(n)` gives
`∑'_n b(n) = ∏'_p 1 = 1`, hence the partial sums `P(N) → 1`. (Conditional on
`Summable ‖b‖`, supplied by the absolute bound `∑|b(e)| ≤ 8`, Aristotle `830e5129`.) -/

/-- `invR n = 1/n` as a (multiplicative) real arithmetic function. -/
noncomputable def invR : ArithmeticFunction ℝ := ⟨fun n => 1 / (n : ℝ), by simp⟩

@[simp] lemma invR_apply (n : ℕ) : invR n = 1 / (n : ℝ) := rfl

lemma invR_isMultiplicative : invR.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [invR_apply]
  push_cast
  rw [one_div_mul_one_div]

/-- `b(e) = B(e)/e` as a real arithmetic function. -/
noncomputable def bAF : ArithmeticFunction ℝ := BSharp.pmul invR

@[simp] lemma bAF_apply (n : ℕ) : bAF n = BSharp n / (n : ℝ) := by
  rw [bAF, ArithmeticFunction.pmul_apply, invR_apply, mul_one_div]

lemma bAF_isMultiplicative : bAF.IsMultiplicative :=
  BSharp_isMultiplicative.pmul invR_isMultiplicative

/-- `B(p) = 1/(p−1)` at the prime `p` itself (not as `p^1`). -/
lemma BSharp_prime' {p : ℕ} (hp : p.Prime) : BSharp p = 1 / ((p : ℝ) - 1) := by
  conv_lhs => rw [← pow_one p]
  exact BSharp_prime hp

/-- `b(p) = 1/(p(p−1))` at a prime (value used by the absolute-bound port). -/
lemma bAF_prime {p : ℕ} (hp : p.Prime) : bAF p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpne : (p : ℝ) ≠ 0 := by linarith
  rw [bAF_apply, BSharp_prime' hp]
  field_simp

/-- `b(p²) = −1/(p(p−1))` at a prime square. -/
lemma bAF_prime_sq {p : ℕ} (hp : p.Prime) : bAF (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpne : (p : ℝ) ≠ 0 := by linarith
  rw [bAF_apply, BSharp_prime_sq hp]
  push_cast; field_simp

/-- `b(p^k) = 0` for `k ≥ 3`. -/
lemma bAF_prime_pow_high {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k) : bAF (p ^ k) = 0 := by
  rw [bAF_apply, BSharp_prime_pow_high hp hk, zero_div]

/-- **The local Euler factor is `1`.** For a prime `p`, `∑'_e b(p^e) = 1`
(`= 1 + b(p) + b(p²) = 1 + 1/(p(p−1)) − 1/(p(p−1))`). -/
lemma tsum_bAF_primePow {p : ℕ} (hp : p.Prime) : ∑' e : ℕ, bAF (p ^ e) = 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have hsupp : ∀ e ∉ Finset.range 3, bAF (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_range, not_lt] at he
    rw [bAF_apply, BSharp_prime_pow_high hp he, zero_div]
  rw [tsum_eq_sum hsupp]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [bAF_apply, bAF_apply, bAF_apply, pow_zero, BSharp_one, BSharp_prime hp, BSharp_prime_sq hp]
  push_cast
  field_simp
  ring

/-- **The b-series sums to `1`** (given absolute summability). Euler product:
`∑'_n b(n) = ∏'_p (∑'_e b(p^e)) = ∏'_p 1 = 1`. -/
theorem tsum_bAF_eq_one (hsum : Summable (fun n => ‖bAF n‖)) : ∑' n, bAF n = 1 := by
  have hep := bAF_isMultiplicative.eulerProduct_tprod hsum
  rw [← hep]
  have hone : (fun p : Nat.Primes => ∑' e : ℕ, bAF ((p : ℕ) ^ e)) = fun _ => (1 : ℝ) := by
    funext p
    exact tsum_bAF_primePow p.2
  rw [hone, tprod_one]

/-- **The main coefficient tends to `1`: `P(N) = ∑_{e≤N} B(e)/e → 1`.**
The signed-b-series partial sums converge to `∑'_n b(n) = 1` (Euler product), the last
piece of `sum_g_decomp`'s reduction. (Conditional on `Summable ‖b‖`, from `∑|b(e)| ≤ 8`,
Aristotle `830e5129`.) -/
theorem P_tendsto_one (hsum : Summable (fun n => ‖bAF n‖)) :
    Filter.Tendsto (fun N : ℕ => ∑ e ∈ Finset.Icc 1 N, BSharp e / (e : ℝ))
      Filter.atTop (nhds 1) := by
  have hHS : HasSum bAF 1 := by
    have h := hsum.of_norm.hasSum
    rwa [tsum_bAF_eq_one hsum] at h
  have htnat : Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, bAF n)
      Filter.atTop (nhds 1) := hHS.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), bAF n)
      Filter.atTop (nhds 1) := by
    have := htnat.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp] using this
  have hbridge : ∀ N : ℕ, ∑ e ∈ Finset.Icc 1 N, BSharp e / (e : ℝ)
      = ∑ n ∈ Finset.range (N + 1), bAF n := by
    intro N
    rw [Finset.sum_range_succ', ArithmeticFunction.map_zero, add_zero]
    refine Finset.sum_nbij' (fun e => e - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro e he; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro e he; simp only [Finset.mem_Icc] at he; show e - 1 + 1 = e; omega
    · intro i _; show i + 1 - 1 = i; omega
    · intro e he; simp only [Finset.mem_Icc] at he
      have hee : e - 1 + 1 = e := by omega
      show BSharp e / (e : ℝ) = bAF (e - 1 + 1)
      rw [bAF_apply, hee]
  simpa only [hbridge] using hshift

/-! ## The capstone: sharp Mertens `∑_{n≤N} μ²(n)/φ(n) ∼ log N`

Combining `sum_g_decomp` (`S = P·log − Q + R`) with `P → 1` and `Q, R = O(1)`
(both `Q/log, R/log → 0`), the Cesàro ratio `S(N)/log N → 1`, i.e. leading
coefficient exactly `1` — precisely GPY/Maynard sub-step (c). Conditional on two
absolute-summability facts (the b-series and its `log`-weighted version), both
Euler-product estimates: `∑|b(e)| ≤ 8` is Aristotle `830e5129`, and
`∑|b(e)||log e| < ∞` is the near-identical companion. -/

/-- **Sharp Mertens (`∑μ²/φ ∼ log x`).** Given absolute summability of the b-series
and its `log`-weighted version, `(∑_{n≤N} μ²(n)/φ(n)) / log N → 1`. -/
theorem sharp_mertens_tendsto
    (hsum : Summable (fun n => ‖bAF n‖))
    (hsumlog : Summable (fun n => ‖bAF n‖ * |Real.log (n : ℝ)|)) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n) / Real.log N)
      Filter.atTop (nhds 1) := by
  have hlogtop : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- The `Q/log → 0` error term.
  have hQ0 : Filter.Tendsto
      (fun N : ℕ => (∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) * Real.log e) / Real.log N)
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto
        (fun N : ℕ => (∑' n, ‖bAF n‖ * |Real.log (n : ℝ)|) / Real.log N) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlogtop
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hlogtop.eventually_ge_atTop 1] with N hlogN
    have hpos : 0 < Real.log N := lt_of_lt_of_le one_pos hlogN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    gcongr
    refine (abs_logweighted_term_le N).trans ?_
    rw [show (∑ e ∈ Finset.Icc 1 N, |BSharp e / (e : ℝ)| * |Real.log e|)
          = ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ * |Real.log (e : ℝ)| from
        Finset.sum_congr rfl (fun e _ => by rw [bAF_apply, Real.norm_eq_abs])]
    exact hsumlog.sum_le_tsum _ (fun i _ => by positivity)
  -- The `R/log → 0` error term.
  have hR0 : Filter.Tendsto
      (fun N : ℕ => (∑ e ∈ Finset.Icc 1 N, (BSharp e / (e : ℝ)) *
        ((∑ m ∈ Finset.Icc 1 (N / e), (1 : ℝ) / m) - Real.log ((N : ℝ) / (e : ℝ)))) / Real.log N)
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto
        (fun N : ℕ => (∑' n, ‖bAF n‖) / Real.log N) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlogtop
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hlogtop.eventually_ge_atTop 1] with N hlogN
    have hpos : 0 < Real.log N := lt_of_lt_of_le one_pos hlogN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    gcongr
    refine (abs_remainder_term_le N).trans ?_
    rw [show (∑ e ∈ Finset.Icc 1 N, |BSharp e / (e : ℝ)|)
          = ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ from
        Finset.sum_congr rfl (fun e _ => by rw [bAF_apply, Real.norm_eq_abs])]
    exact hsum.sum_le_tsum _ (fun i _ => by positivity)
  -- Assemble: S/log = P − Q/log + R/log → 1 − 0 + 0.
  have htarget := ((P_tendsto_one hsum).sub hQ0).add hR0
  rw [sub_zero, add_zero] at htarget
  refine htarget.congr' ?_
  filter_upwards [hlogtop.eventually_ge_atTop 1, Filter.eventually_ge_atTop 1] with N hlogN hN1
  have hlog0 : Real.log N ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hlogN)
  rw [sum_g_decomp N hN1]
  field_simp

/-! ## Discharging summability from a uniform bound

The two summability hypotheses of `sharp_mertens_tendsto` reduce to *uniform
partial-sum bounds* (Euler-product estimates of the kind Aristotle handles). Once
the bound `∑_{e≤N}|b(e)| ≤ C` (Aristotle `830e5129`) ports, `summable_norm_bAF_of_bound`
turns it into `Summable ‖b‖`, discharging the first hypothesis; the `log`-weighted
companion is identical. -/

/-- General Icc→range bridge for a function vanishing at `0`:
`∑_{e=1}^N g(e) = ∑_{n<N+1} g(n)`. -/
lemma sum_Icc_eq_sum_range_succ {g : ℕ → ℝ} (hg0 : g 0 = 0) (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, g e = ∑ n ∈ Finset.range (N + 1), g n := by
  rw [Finset.sum_range_succ', hg0, add_zero]
  refine Finset.sum_nbij' (fun e => e - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
  · intro e he; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
  · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
  · intro e he; simp only [Finset.mem_Icc] at he; show e - 1 + 1 = e; omega
  · intro i _; show i + 1 - 1 = i; omega
  · intro e he; simp only [Finset.mem_Icc] at he
    show g e = g (e - 1 + 1)
    rw [show e - 1 + 1 = e from by omega]

/-- `‖b(0)‖ = 0`. -/
lemma norm_bAF_zero : ‖bAF 0‖ = 0 := by
  rw [show bAF 0 = (0 : ℝ) from ArithmeticFunction.map_zero, norm_zero]

/-- **Summability of `‖b‖` from a uniform partial-sum bound.** If `∑_{e≤N}‖b(e)‖ ≤ C`
for all `N`, then `‖b‖` is summable. -/
theorem summable_norm_bAF_of_bound {C : ℝ}
    (hC : ∀ N, ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ ≤ C) : Summable (fun n => ‖bAF n‖) := by
  apply summable_of_sum_range_le (fun n => norm_nonneg _)
  intro n
  cases n with
  | zero => simpa using hC 0
  | succ m =>
    rw [← sum_Icc_eq_sum_range_succ (g := fun i => ‖bAF i‖) norm_bAF_zero m]
    exact hC m

/-- **Companion: summability of the `log`-weighted series from its bound.** -/
theorem summable_norm_bAF_log_of_bound {C : ℝ}
    (hC : ∀ N, ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ * |Real.log (e : ℝ)| ≤ C) :
    Summable (fun n => ‖bAF n‖ * |Real.log (n : ℝ)|) := by
  apply summable_of_sum_range_le (fun n => by positivity)
  intro n
  cases n with
  | zero => simpa using hC 0
  | succ m =>
    calc ∑ i ∈ Finset.range (m + 1), ‖bAF i‖ * |Real.log (i : ℝ)|
        = ∑ e ∈ Finset.Icc 1 m, ‖bAF e‖ * |Real.log (e : ℝ)| :=
          (sum_Icc_eq_sum_range_succ (g := fun i => ‖bAF i‖ * |Real.log (i : ℝ)|)
            (by simp [norm_bAF_zero]) m).symm
      _ ≤ C := hC m

/-! ## Unconditional bound `∑_{e≤N} ‖b(e)‖ ≤ exp 2` — discharges hypothesis #1

Rather than the abstract Euler product on `babs` (Aristotle), we bound the partial sum
directly on the concrete `bAF`. The structural fact: `bAF e ≠ 0` forces every prime
exponent of `e` to be `≤ 2` (since `bAF (p^k) = 0` for `k ≥ 3`), so any `e ≤ N` in the
support divides the **primorial squared** `(N#)²`. Hence
  `∑_{e≤N} |bAF e| ≤ ∑_{d ∣ (N#)²} |bAF d| = ∏_{p ≤ N} (1 + 2/(p(p-1))) ≤ exp 2`,
the middle equality by multiplicativity of `ζ ⋆ |bAF|`, the last by `1+x ≤ eˣ` and the
convergent telescoping `∑_p 2/(p(p-1)) ≤ ∑_{2≤n≤N} 2/(n(n-1)) = 2 - 2/N ≤ 2`. -/

/-- `|bAF|` packaged as a (multiplicative) real arithmetic function. -/
noncomputable def gabs : ArithmeticFunction ℝ := ⟨fun n => |bAF n|, by simp⟩

@[simp] lemma gabs_apply (n : ℕ) : gabs n = |bAF n| := rfl

lemma gabs_isMultiplicative : gabs.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · show |bAF 1| = 1
    rw [bAF_isMultiplicative.1, abs_one]
  · intro m n hmn
    show |bAF (m * n)| = |bAF m| * |bAF n|
    rw [bAF_isMultiplicative.2 hmn, abs_mul]

/-- Telescoping value `∑_{2≤n≤N} 2/(n(n-1)) = 2 - 2/N` (for `N ≥ 1`). -/
lemma sum_Icc_two_div_eq : ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 2 N, (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 2 - 2 / (N : ℝ) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ M ih =>
    intro _
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1), ih hM]
      have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
      have hMc : (M : ℝ) + 1 - 1 = (M : ℝ) := by ring
      push_cast
      rw [hMc]
      field_simp
      ring

/-- Uniform telescoping bound `∑_{2≤n≤N} 2/(n(n-1)) ≤ 2`. -/
lemma sum_Icc_two_div_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]; norm_num
  · rw [sum_Icc_two_div_eq N hN]
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
    linarith

/-- `bAF e ≠ 0` forces every prime exponent of `e` to be `≤ 2`
(because `bAF (p^k) = 0` for `k ≥ 3`, and `bAF` is multiplicative). -/
lemma factorization_le_two_of_bAF_ne_zero {e : ℕ} (h : bAF e ≠ 0) (p : ℕ) :
    e.factorization p ≤ 2 := by
  by_contra hlt
  push_neg at hlt
  have he : e ≠ 0 := by
    rintro rfl; exact h (by rw [ArithmeticFunction.map_zero])
  have hp : p.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime e hnp] at hlt; omega
  apply h
  rw [bAF_isMultiplicative.multiplicative_factorization _ he]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr (by omega))
    (bAF_prime_pow_high hp (by omega))

/-- Any `e ∈ [1,N]` in the support of `bAF` divides the primorial squared `(N#)²`. -/
lemma dvd_primorial_sq_of_bAF_ne_zero {e N : ℕ} (h1 : 1 ≤ e) (hN : e ≤ N)
    (h : bAF e ≠ 0) : e ∣ (primorial N) ^ 2 := by
  have he : e ≠ 0 := by omega
  have hM : (primorial N) ^ 2 ≠ 0 := pow_ne_zero _ (primorial_pos N).ne'
  rw [← Nat.factorization_prime_le_iff_dvd he hM]
  intro p hp
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (e.factorization p) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hpe : p ∣ e := Nat.dvd_of_factorization_pos (by omega)
    have hpN : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hpe) hN
    have hmem : p ∈ (Finset.range (N + 1)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hdvd : p ∣ primorial N := Finset.dvd_prod_of_mem _ hmem
    have hpp : 0 < (primorial N).factorization p :=
      hp.factorization_pos_of_dvd (primorial_pos N).ne' hdvd
    have h2 := factorization_le_two_of_bAF_ne_zero h p
    omega

/-- **The full divisor sum `∑_{d∣(N#)²} |bAF d| ≤ exp 2`** — the Euler-product estimate,
`= ∏_{p≤N}(1+2/(p(p-1))) ≤ exp(∑ 2/(p(p-1))) ≤ exp 2`. Reusable: the unweighted bound #1
and the restricted (multiples-of-`p`) sums for the log-weighted bound #2 both rest on it. -/
theorem sum_gabs_divisors_primorial_sq_le (N : ℕ) :
    ∑ d ∈ ((primorial N) ^ 2).divisors, gabs d ≤ Real.exp 2 := by
  set M := (primorial N) ^ 2 with hMdef
  set S := (Finset.range (N + 1)).filter Nat.Prime with hSdef
  have hMfact : M = ∏ p ∈ S, p ^ 2 := by
    rw [hMdef, show primorial N = ∏ p ∈ S, p from rfl, ← Finset.prod_pow]
  have hGmult : ((ζ : ArithmeticFunction ℝ) * gabs).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul gabs_isMultiplicative
  have hcop : (↑S : Set ℕ).Pairwise (fun a b => Nat.Coprime (a ^ 2) (b ^ 2)) := by
    intro p hp q hq hpq
    rw [hSdef] at hp hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp.2 hq.2).mpr hpq)
  have hlocal : ∀ p ∈ S, ((ζ : ArithmeticFunction ℝ) * gabs) (p ^ 2)
      = 1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpp : p.Prime := by rw [hSdef] at hp; exact (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by apply mul_pos <;> linarith
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        gabs_apply, gabs_apply, gabs_apply, pow_zero, pow_one,
        show bAF 1 = 1 from bAF_isMultiplicative.1, bAF_prime hpp, bAF_prime_sq hpp,
        abs_one, abs_of_pos (by positivity : (0:ℝ) < 1 / ((p:ℝ) * ((p:ℝ) - 1))),
        abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / ((p:ℝ) * ((p:ℝ) - 1)))]
    ring
  have hpos_term : ∀ p ∈ S, (0 : ℝ) ≤ 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpp : p.Prime := by rw [hSdef] at hp; exact (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    apply div_nonneg (by norm_num); nlinarith
  calc ∑ d ∈ M.divisors, gabs d
      = ((ζ : ArithmeticFunction ℝ) * gabs) M := coe_zeta_mul_apply.symm
    _ = ∏ p ∈ S, ((ζ : ArithmeticFunction ℝ) * gabs) (p ^ 2) := by
        rw [hMfact]; exact hGmult.map_prod (fun p => p ^ 2) S hcop
    _ = ∏ p ∈ S, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := Finset.prod_congr rfl hlocal
    _ ≤ ∏ p ∈ S, Real.exp (2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        apply Finset.prod_le_prod
        · exact fun p hp => by linarith [hpos_term p hp]
        · exact fun p _ => by rw [add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        (Real.exp_sum S _).symm
    _ ≤ Real.exp 2 := by
        apply Real.exp_le_exp.mpr
        calc ∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 1))
            ≤ ∑ n ∈ Finset.Icc 2 N, 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rw [hSdef, Finset.mem_filter, Finset.mem_range] at hp
                rw [Finset.mem_Icc]
                exact ⟨hp.2.two_le, by omega⟩
              · intro n hn _
                rw [Finset.mem_Icc] at hn
                have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
                apply div_nonneg (by norm_num); nlinarith
          _ ≤ 2 := sum_Icc_two_div_le N

/-- **Unconditional bound** `∑_{e≤N} ‖b(e)‖ ≤ exp 2`. The support of `bAF` restricted to
`[1,N]` injects into the divisors of `(N#)²`, so this follows from
`sum_gabs_divisors_primorial_sq_le`. -/
theorem sum_norm_bAF_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ ≤ Real.exp 2 := by
  have hMne : (primorial N) ^ 2 ≠ 0 := pow_ne_zero _ (primorial_pos N).ne'
  calc ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => bAF e ≠ 0), gabs e := by
        rw [show (∑ e ∈ Finset.Icc 1 N, ‖bAF e‖)
              = ∑ e ∈ Finset.Icc 1 N, gabs e from
            Finset.sum_congr rfl (fun e _ => by rw [gabs_apply, Real.norm_eq_abs])]
        symm
        apply Finset.sum_filter_of_ne
        intro e _ hge h0
        rw [gabs_apply, h0, abs_zero] at hge
        exact hge rfl
    _ ≤ ∑ d ∈ ((primorial N) ^ 2).divisors, gabs d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_filter, Finset.mem_Icc] at he
          obtain ⟨⟨ha, hb⟩, hne⟩ := he
          rw [Nat.mem_divisors]
          exact ⟨dvd_primorial_sq_of_bAF_ne_zero ha hb hne, hMne⟩
        · exact fun d _ _ => by rw [gabs_apply]; exact abs_nonneg _
    _ ≤ Real.exp 2 := sum_gabs_divisors_primorial_sq_le N

/-- **Summability of `‖b‖`, unconditionally** (from `sum_norm_bAF_le`). Discharges the
first hypothesis of `sharp_mertens_tendsto` with no axioms. -/
theorem summable_norm_bAF : Summable (fun n => ‖bAF n‖) :=
  summable_norm_bAF_of_bound (C := Real.exp 2) sum_norm_bAF_le

/-! ## Structural divisor lemmas toward the log-weighted bound #2

These build the reduction `∑_{d∣(N#)²} |bAF d|·log d ≤ (const)·∑_p (log p)/(p(p-1))`.
The divisor sum of the (multiplicative) `|bAF|` factors over coprime products, which lets
us isolate, for each prime `p`, the contribution of the multiples of `p`. -/

/-- The divisor sum of `gabs = |bAF|` is multiplicative over coprime products. -/
lemma gabs_sum_divisors_mul {m n : ℕ} (hmn : Nat.Coprime m n) :
    ∑ d ∈ (m * n).divisors, gabs d
      = (∑ d ∈ m.divisors, gabs d) * (∑ d ∈ n.divisors, gabs d) := by
  have h := (isMultiplicative_zeta.natCast.mul gabs_isMultiplicative).map_mul_of_coprime hmn
  simpa only [coe_zeta_mul_apply] using h

/-- `∑_{d∣n} gabs d ≥ 0`. -/
lemma sum_gabs_divisors_nonneg (n : ℕ) : 0 ≤ ∑ d ∈ n.divisors, gabs d :=
  Finset.sum_nonneg (fun d _ => by rw [gabs_apply]; exact abs_nonneg _)

/-- **(C) The multiples-of-`p` contribution.** For a prime `p ≤ N`, the divisors of `(N#)²`
divisible by `p` contribute at most `(|bAF p| + |bAF p²|)·exp 2`. Proof: split off the `p`-part,
`(N#)² = p²·Q²` with `p ⟂ Q`; the divisors not divisible by `p` are exactly the divisors of
`Q²` (summing to `B`), and the full sum is `(1+|bAF p|+|bAF p²|)·B`, so the multiples sum to
`(|bAF p|+|bAF p²|)·B ≤ (|bAF p|+|bAF p²|)·exp 2` (since `B ≤ (1+…)·B = full ≤ exp 2`). -/
theorem sum_gabs_divisors_multiples_le {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    ∑ d ∈ (((primorial N) ^ 2).divisors.filter (fun d => p ∣ d)), gabs d
      ≤ (gabs p + gabs (p ^ 2)) * Real.exp 2 := by
  classical
  set S := (Finset.range (N + 1)).filter Nat.Prime with hSdef
  have hpS : p ∈ S := by rw [hSdef, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩
  set Q := ∏ q ∈ S.erase p, q with hQdef
  have hprim : primorial N = p * Q := by
    rw [hQdef]; exact (Finset.mul_prod_erase S (fun q => q) hpS).symm
  have hcopQ : Nat.Coprime p Q := by
    rw [hQdef]
    apply Nat.Coprime.prod_right
    intro q hq
    rw [Finset.mem_erase, hSdef, Finset.mem_filter] at hq
    exact (Nat.coprime_primes hp hq.2.2).mpr (Ne.symm hq.1)
  have hnpQ : ¬ p ∣ Q := by
    intro h
    have hg : Nat.gcd p Q = 1 := hcopQ
    have hg2 : Nat.gcd p Q = p := Nat.gcd_eq_left h
    have := hp.two_le
    omega
  have hcopM : Nat.Coprime (p ^ 2) (Q ^ 2) := Nat.Coprime.pow 2 2 hcopQ
  have hMeq : (primorial N) ^ 2 = p ^ 2 * Q ^ 2 := by rw [hprim]; ring
  have hMne : (primorial N) ^ 2 ≠ 0 := pow_ne_zero _ (primorial_pos N).ne'
  set B := ∑ d ∈ (Q ^ 2).divisors, gabs d with hBdef
  have hBnn : 0 ≤ B := sum_gabs_divisors_nonneg _
  have hA : ∑ d ∈ (p ^ 2).divisors, gabs d = 1 + gabs p + gabs (p ^ 2) := by
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, pow_zero, pow_one, show gabs 1 = 1 from gabs_isMultiplicative.1]
  have hfull : ∑ d ∈ ((primorial N) ^ 2).divisors, gabs d
      = (1 + gabs p + gabs (p ^ 2)) * B := by
    rw [hMeq, gabs_sum_divisors_mul hcopM, hA, hBdef]
  have hQ2M : Q ^ 2 ∣ (primorial N) ^ 2 := by rw [hMeq]; exact dvd_mul_left _ _
  have hcompl : ∑ d ∈ (((primorial N) ^ 2).divisors.filter (fun d => ¬ p ∣ d)), gabs d = B := by
    have hfilter_eq : ((primorial N) ^ 2).divisors.filter (fun d => ¬ p ∣ d)
        = ((primorial N) ^ 2).divisors.filter (fun d => d ∣ Q ^ 2) := by
      apply Finset.filter_congr
      intro d hd
      rw [Nat.mem_divisors] at hd
      constructor
      · intro hnpd
        have hcopdp : Nat.Coprime d (p ^ 2) :=
          Nat.Coprime.pow_right 2 (((Nat.coprime_or_dvd_of_prime hp d).resolve_right hnpd).symm)
        exact hcopdp.dvd_of_dvd_mul_left (hMeq ▸ hd.1)
      · intro hdQ2 hpd
        exact hnpQ (hp.prime.dvd_of_dvd_pow (hpd.trans hdQ2))
    rw [hfilter_eq, Nat.divisors_filter_dvd_of_dvd hMne hQ2M, hBdef]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (((primorial N) ^ 2).divisors) (fun d => p ∣ d) gabs
  have hApos : 0 ≤ gabs p + gabs (p ^ 2) := by rw [gabs_apply, gabs_apply]; positivity
  have hrestricted : ∑ d ∈ (((primorial N) ^ 2).divisors.filter (fun d => p ∣ d)), gabs d
      = (gabs p + gabs (p ^ 2)) * B := by
    have heq : ∑ d ∈ (((primorial N) ^ 2).divisors.filter (fun d => p ∣ d)), gabs d
        = (∑ d ∈ ((primorial N) ^ 2).divisors, gabs d)
          - ∑ d ∈ (((primorial N) ^ 2).divisors.filter (fun d => ¬ p ∣ d)), gabs d := by
      rw [← hsplit]; ring
    rw [heq, hfull, hcompl]; ring
  rw [hrestricted]
  have hBle : B ≤ Real.exp 2 :=
    calc B ≤ (1 + gabs p + gabs (p ^ 2)) * B := by nlinarith [hBnn, hApos]
      _ = ∑ d ∈ ((primorial N) ^ 2).divisors, gabs d := hfull.symm
      _ ≤ Real.exp 2 := sum_gabs_divisors_primorial_sq_le N
  exact mul_le_mul_of_nonneg_left hBle hApos

/-! ## Analytic crux of the log-weighted bound #2: `∑_p (log p)/(p(p-1)) < ∞`

The log-weighted summability hypothesis of `sharp_mertens_tendsto` reduces (after the
von-Mangoldt / divisor-sum split) to the convergent prime sum `∑_p (log p)/(p(p-1))`.
Its convergence is the genuine analytic content; we bound it via the pointwise estimate
`(log n)/(n(n-1)) ≤ 4·n^{-3/2}` (from `log n ≤ 2√n` and `n(n-1) ≥ n^{3/2}·√n`... i.e.
`log n · n^{3/2} ≤ 2n² ≤ 4n(n-1)`) and the `p`-series `∑ n^{-3/2} < ∞`. This is the
brick that ports onto the concrete prime sum when discharging bound #2. -/

/-- Pointwise: `(log n)/(n(n-1)) ≤ 4·n^{-3/2}` for `n ≥ 2`. -/
lemma term_log_div_le (n : ℕ) (hn : 2 ≤ n) :
    Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 4 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hr1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hs : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hr0 _
  have hlog : Real.log n ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have h := Real.log_le_rpow_div (le_of_lt hr0) (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)
    have h2 : (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [div_eq_mul_inv, show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num]; ring
    rw [h2] at h; exact h
  have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
    rw [← Real.rpow_add hr0, show (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) := by
    rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hr0, Real.rpow_one]
  rw [h32, div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.log n * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ))
      ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hlog; positivity
    _ = 2 * (n : ℝ) * (n : ℝ) := by
        rw [show (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ))
              = 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2)) * (n : ℝ) by ring, hsq]
    _ ≤ 4 * ((n : ℝ) * ((n : ℝ) - 1)) := by nlinarith [hr, hr0]

/-- The majorant `∑ 4·n^{-3/2}` is summable (`p`-series with `p = 3/2 > 1`). -/
lemma summable_four_div_rpow : Summable (fun n : ℕ => (4 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  have := (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 4
  simpa [mul_one_div] using this

/-- **Analytic crux**: the partial sums `∑_{2≤n≤N} (log n)/(n(n-1))` are uniformly bounded
by the convergent `∑' 4·n^{-3/2}`. -/
theorem sum_log_div_consecutive_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑' n : ℕ, (4 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  calc ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 N, (4 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro n hn
        exact term_log_div_le n (Finset.mem_Icc.mp hn).1
    _ ≤ ∑' n : ℕ, (4 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) :=
        summable_four_div_rpow.sum_le_tsum _ (fun i _ => by positivity)

/-- **The convergent prime sum** `∑_{p≤N} (log p)/(p(p-1)) ≤ ∑' 4·n^{-3/2}` — the brick the
log-weighted bound #2 needs once its von-Mangoldt/divisor reduction lands. -/
theorem sum_log_div_primes_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑' n : ℕ, (4 : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  refine le_trans ?_ (sum_log_div_consecutive_le N)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, by omega⟩
  · intro n hn _
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)

/-- **Sharp Mertens from the two partial-sum bounds (one-shot).** Packages the full
reduction: given the unweighted and `log`-weighted Euler-product bounds (the two
Aristotle leaves), `(∑_{n≤N} μ²/φ)/log N → 1`. Porting `830e5129` (and its
`log`-weighted sister) into `h1`/`h2` makes the sharp Mertens fully unconditional. -/
theorem sharp_mertens_of_bounds {C₁ C₂ : ℝ}
    (h1 : ∀ N, ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ ≤ C₁)
    (h2 : ∀ N, ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ * |Real.log (e : ℝ)| ≤ C₂) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n) / Real.log N)
      Filter.atTop (nhds 1) :=
  sharp_mertens_tendsto (summable_norm_bAF_of_bound h1) (summable_norm_bAF_log_of_bound h2)

/-- **Sharp Mertens from the log-weighted bound ALONE** (the unweighted bound #1 is now
discharged unconditionally via `summable_norm_bAF`). So `(∑_{n≤N} μ²/φ)/log N → 1` rests on
the single remaining ingredient: the `log`-weighted partial-sum bound `h2` (the von-Mangoldt
/ divisor-sum reduction to the convergent `∑_p (log p)/(p(p-1))`, see `sum_log_div_primes_le`;
on Aristotle `blog 4b5e45de`). -/
theorem sharp_mertens_of_log_bound {C₂ : ℝ}
    (h2 : ∀ N, ∑ e ∈ Finset.Icc 1 N, ‖bAF e‖ * |Real.log (e : ℝ)| ≤ C₂) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n) / Real.log N)
      Filter.atTop (nhds 1) :=
  sharp_mertens_tendsto summable_norm_bAF (summable_norm_bAF_log_of_bound h2)

end BoundedGaps.SharpMertens
