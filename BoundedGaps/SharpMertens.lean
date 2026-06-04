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
