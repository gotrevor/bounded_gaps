/-
# The single-prime coprime Mertens recursion (the structural crux of `hBaseW`)

`hBaseW` (the W-coprime sharp Mertens `(∑_{n≤N,(n,W)=1}μ²/φ)/log N → φ(W)/W`) is the sole remaining
analytic input threaded through the contour-free y-space `s1` chain. The repo already proves the
**unrestricted** sharp Mertens `(∑_{n≤N}μ²/φ)/log N → 1` (`SharpMertens.sharp_mertens_unconditional`),
so `hBaseW` is NOT a from-scratch analytic theorem — it follows by an **elementary geometric Möbius
inversion**, one prime at a time, with NO Euler products and NO new analytic number theory.

This file proves the structural crux: the single-prime recursion
  `∑_{n≤N} μ²/φ  =  ∑_{n≤N,(n,p)=1} μ²/φ  +  (1/(p-1))·∑_{n≤N/p,(n,p)=1} μ²/φ`
(`coprime_mertens_recursion`), obtained by splitting `∑μ²/φ` by `p ∣ n` and reindexing the `p∣n` part
`n = p·m` (squarefreeness forces `p ∤ m`, and `μ²(pm)/φ(pm) = μ²(m)/((p-1)φ(m))`).

Inverting this two-term recursion gives the finite geometric series
`∑_{n≤N,(n,p)=1}μ²/φ = ∑_{k≥0}(-1/(p-1))^k ∑_{n≤N/p^k}μ²/φ` (terminating, as the inner sum is `0` once
`p^k > N`); taking `/log N → 1` per term yields `∑_{n≤N,(n,p)=1}μ²/φ / log N → (p-1)/p = φ(p)/p`.
Iterating over the primes of (squarefree) `W` gives `hBaseW`. The single-prime limit is also on
Aristotle (`dd98b9c1`, with `sharp_mertens` inlined); this file de-risks it by machine-checking the
recursion in-kernel.
-/
import BoundedGaps.WeightedMertens

open scoped BigOperators
open ArithmeticFunction (moebius)
open BoundedGaps.SingularSeries Filter Topology
open BoundedGaps.WeightedMertens (gMuSqTotientCoprime)

namespace BoundedGaps.CoprimeMertens

/-- **Per-term identity.** For a prime `p` and any `m`, `μ²(pm)/φ(pm) = (1/(p-1))·[(m,p)=1]·μ²(m)/φ(m)`.
If `(m,p)=1` use multiplicativity (`μ(pm)=μ(p)μ(m)`, `φ(pm)=(p-1)φ(m)`); if `p∣m` then `p²∣pm` so
`μ(pm)=0` and both sides vanish. -/
theorem per_term (p m : ℕ) (hp : p.Prime) :
    ((moebius (p * m) : ℝ)) ^ 2 / (Nat.totient (p * m) : ℝ)
      = (1 / ((p : ℝ) - 1))
        * (if Nat.Coprime m p then (moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ) else 0) := by
  by_cases hc : Nat.Coprime m p
  · rw [if_pos hc]
    have hcpm : Nat.Coprime p m := hc.symm
    have hmu : (moebius (p * m) : ℝ) = (moebius p : ℝ) * (moebius m : ℝ) := by
      have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcpm
      exact_mod_cast this
    have hphi : Nat.totient (p * m) = (p - 1) * Nat.totient m := by
      rw [Nat.totient_mul hcpm, Nat.totient_prime hp]
    have hp1 : (moebius p : ℝ) = -1 := by rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
    have hp1ne : ((p : ℝ) - 1) ≠ 0 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
      linarith
    rw [hmu, hp1, hphi, Nat.cast_mul, Nat.cast_pred hp.pos]
    field_simp
  · rw [if_neg hc]
    have hpdvdm : p ∣ m := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd] at hc; exact not_not.mp hc
    have hnsf : ¬ Squarefree (p * m) := by
      obtain ⟨t, rfl⟩ := hpdvdm
      intro hsf
      exact absurd (Nat.isUnit_iff.mp (hsf p ⟨t, by ring⟩)) hp.ne_one
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    simp

/-- **The single-prime coprime Mertens recursion** (stated on the repo sums `gMoebiusSqTotient` /
`gMuSqTotientCoprime`). Splits `∑_{n≤N} μ²/φ` by `p ∣ n`: the `p∤n` part is the `p`-coprime sum at `N`,
the `p∣n` part reindexes (`n = p·m`) to `(1/(p-1))·` the `p`-coprime sum at `N/p` (`per_term`). The
structural crux of `hBaseW` (its geometric-inversion route); UNCONDITIONAL, no BV, no Euler product. -/
theorem coprime_mertens_recursion (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n)
      = (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime p n)
        + (1 / ((p : ℝ) - 1))
          * ∑ n ∈ Finset.Icc 1 (N / p), BoundedGaps.WeightedMertens.gMuSqTotientCoprime p n := by
  show (∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ))
      = (∑ n ∈ Finset.Icc 1 N,
            (if Nat.Coprime n p then (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ) else 0))
        + (1 / ((p : ℝ) - 1))
          * ∑ n ∈ Finset.Icc 1 (N / p),
              (if Nat.Coprime n p then (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ) else 0)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)
    (fun n => (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ))
  have hA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
        (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N,
          (if Nat.Coprime n p then (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ) else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun n _ => rfl)
    apply Finset.filter_congr
    intro n _
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  have hB : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
        (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ)
      = (1 / ((p : ℝ) - 1))
        * ∑ n ∈ Finset.Icc 1 (N / p),
            (if Nat.Coprime n p then (moebius n : ℝ) ^ 2 / (Nat.totient n : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun a _ => a / p) (fun b _ => p * b) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      obtain ⟨⟨ha1, ha2⟩, hpa⟩ := ha
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpa),
        Nat.div_le_div_right ha2⟩
    · intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hb2⟩ := hb
      show p * b ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n)
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p b⟩
      · calc 1 ≤ p := hp.one_le
          _ ≤ p * b := Nat.le_mul_of_pos_right p hb1
      · rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).mp hb2
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact Nat.mul_div_cancel' ha.2
    · intro b _
      exact Nat.mul_div_cancel_left b hp.pos
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [← per_term p (a / p) hp, Nat.mul_div_cancel' ha.2]
  rw [← hsplit, hA, hB, add_comm]

/-- The unrestricted `μ²/φ` partial sum vanishes at `N = 0` (empty range). -/
theorem U_zero : (∑ n ∈ Finset.Icc 1 0, gMoebiusSqTotient n) = 0 := by simp

/-- The `μ²/φ` weight is nonnegative. -/
theorem gMoebiusSqTotient_nonneg (n : ℕ) : 0 ≤ gMoebiusSqTotient n := by
  rw [gMoebiusSqTotient_apply]; positivity

/-- The unrestricted `μ²/φ` partial sum is monotone in the cutoff (nonnegative terms). Feeds the
dominated-convergence bound for the single-prime limit (`U(N/p^k) ≤ U(N)`). -/
theorem U_mono {M M' : ℕ} (h : M ≤ M') :
    (∑ n ∈ Finset.Icc 1 M, gMoebiusSqTotient n)
      ≤ ∑ n ∈ Finset.Icc 1 M', gMoebiusSqTotient n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun i _ _ => gMoebiusSqTotient_nonneg i)

/-- **Summability of the geometric-inversion series.** For each `N`, only finitely many terms
`(-1/(p-1))^k·(∑_{n≤N/p^k}μ²/φ)` are nonzero (`N/p^k = 0` once `p^k > N`), so the series is summable. -/
theorem inversion_summable (p : ℕ) (hp : p.Prime) (N : ℕ) :
    Summable (fun k : ℕ =>
      (- (1 / ((p:ℝ)-1)))^k * (∑ n ∈ Finset.Icc 1 (N / p^k), gMoebiusSqTotient n)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (N+1)) ?_
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have hpk : N < p ^ k := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
    (Nat.pow_le_pow_right hp.pos (by omega))
  rw [Nat.div_eq_of_lt hpk, U_zero, mul_zero]

/-- **The geometric inversion of the single-prime recursion.** Inverting the two-term recursion
`coprime_mertens_recursion` gives the `p`-coprime `μ²/φ` partial sum as the (finite, convergent)
geometric series of the *unrestricted* partial sums:
  `∑_{n≤N,(n,p)=1} μ²/φ  =  ∑_{k≥0} (-1/(p-1))^k · ∑_{n≤N/p^k} μ²/φ`.
Proved by strong induction on `N` (split off `k=0`, reindex `k↦k+1` to `N/p`, apply the IH and the
recursion). This is the second pillar of the geometric route to `hBaseW`: with the unrestricted sum's
limit (`SharpMertens.sharp_mertens_unconditional`, `∑/log N → 1`), taking `/log N → 1` term-by-term in
this series yields `∑_{n≤N,(n,p)=1}μ²/φ / log N → ∑_k(-1/(p-1))^k = (p-1)/p` (the remaining step is the
limit/sum interchange). UNCONDITIONAL; no BV, no Euler product. -/
theorem coprime_geometric_inversion (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime p n)
      = ∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^k
          * (∑ n ∈ Finset.Icc 1 (N / p^k), gMoebiusSqTotient n) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hz : ∀ k : ℕ, (- (1 / ((p:ℝ)-1)))^k
          * (∑ n ∈ Finset.Icc 1 (0 / p^k), gMoebiusSqTotient n) = 0 := by
        intro k; rw [Nat.zero_div, U_zero, mul_zero]
      rw [tsum_congr hz, tsum_zero]
      simp
    · rw [(inversion_summable p hp N).tsum_eq_zero_add]
      have hterm0 : (- (1 / ((p:ℝ)-1)))^0
          * (∑ n ∈ Finset.Icc 1 (N / p^0), gMoebiusSqTotient n)
          = ∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n := by
        rw [pow_zero, one_mul, pow_zero, Nat.div_one]
      have htail : (∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^(k+1)
            * (∑ n ∈ Finset.Icc 1 (N / p^(k+1)), gMoebiusSqTotient n))
          = (- (1 / ((p:ℝ)-1)))
            * (∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^k
                * (∑ n ∈ Finset.Icc 1 ((N / p) / p^k), gMoebiusSqTotient n)) := by
        rw [← tsum_mul_left]
        apply tsum_congr; intro k
        have hdiv : N / p^(k+1) = (N / p) / p^k := by
          rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
        rw [hdiv, pow_succ]; ring
      rw [hterm0, htail, ← ih (N / p) (Nat.div_lt_self hN hp.one_lt)]
      have hrec := coprime_mertens_recursion p hp N
      linarith [hrec]

/-- **The geometric target value** (`p ≥ 3`). The limit of the inverted series' coefficients:
`∑_k (-1/(p-1))^k = (p-1)/p = φ(p)/p`. For `p ≥ 3` the ratio `1/(p-1) < 1`, so this is a convergent
signed geometric series with sum `1/(1+1/(p-1)) = (p-1)/p`. This is the target constant of the
single-prime `hBaseW` for odd primes: combined with `coprime_geometric_inversion` and a dominated-
convergence interchange (`U(N/p^k)/log N → 1` per `k`, dominated by `(1/(p-1))^k·C` — summable since
`1/(p-1) < 1`), `∑_{n≤N,(n,p)=1}μ²/φ / log N → (p-1)/p`. [The interchange for `p = 2` is genuinely
different: `1/(p-1) = 1`, the limit series `∑(-1)^k` diverges, so DCT fails and the cancellation in the
finite inverted sum must be used directly (Abel/telescoping) — the remaining nut.] -/
theorem geom_value (p : ℕ) (hp : 3 ≤ p) :
    ∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^k = ((p:ℝ)-1)/p := by
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hc : ‖(- (1 / ((p:ℝ)-1)))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (div_pos one_pos hpos))]
    rw [div_lt_one hpos]; linarith
  rw [tsum_geometric_of_norm_lt_one hc, sub_neg_eq_add]
  rw [show (1:ℝ) + 1/((p:ℝ)-1) = (p:ℝ)/((p:ℝ)-1) by field_simp; ring]
  rw [inv_div]

/-- The unrestricted sharp Mertens, as the `gMoebiusSqTotient` partial-sum limit (= the repo's
`SharpMertens.sharp_mertens_unconditional`). The base case of the single-prime limit. -/
theorem U_div_log_tendsto_one :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n) / Real.log N) atTop (𝓝 1) :=
  BoundedGaps.SharpMertens.sharp_mertens_unconditional

/-- `a / log N → 0` (a constant over a diverging `log`). -/
theorem const_div_log_tendsto_zero (a : ℝ) :
    Tendsto (fun N : ℕ => a / Real.log N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Tendsto.div_atTop tendsto_const_nhds h1

/-- `log(⌊N/c⌋) / log N → 1` (nat division by a fixed `c ≥ 1`). Squeeze:
`1 - log(2c)/log N ≤ ratio ≤ 1`, using `⌊N/c⌋ ≥ N/(2c)` for `N ≥ 2c`. -/
theorem log_div_ratio_tendsto_one (c : ℕ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (↑(N / c)) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hlow : Tendsto (fun N : ℕ => 1 - Real.log (2 * c) / Real.log (N:ℝ)) atTop (𝓝 1) := by
    have := const_div_log_tendsto_zero (Real.log (2 * c))
    simpa using (tendsto_const_nhds.sub this)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 * c), eventually_ge_atTop 2] with N hN hN2
    have hlogN : (0:ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have key : N ≤ 2 * (c * (N / c)) := by
      have h1 := Nat.div_add_mod N c
      have h2 := Nat.mod_lt N hc
      have hq1 : 1 ≤ N / c := (Nat.one_le_div_iff hc).mpr (by omega)
      have hcq : c ≤ c * (N / c) := Nat.le_mul_of_pos_right c hq1
      set m := c * (N / c) with hm
      omega
    have hfloor : (N:ℝ) / (2 * c) ≤ (↑(N / c) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have hcast : (N:ℝ) ≤ 2 * ((c:ℝ) * (↑(N/c):ℝ)) := by exact_mod_cast key
      nlinarith [hcast]
    have hpos2 : (0:ℝ) < (N:ℝ) / (2 * c) := by positivity
    have hloglow : Real.log ((N:ℝ) / (2 * c)) ≤ Real.log (↑(N / c) : ℝ) :=
      Real.log_le_log hpos2 hfloor
    rw [Real.log_div (by positivity) (by positivity)] at hloglow
    have hLHS : (1:ℝ) - Real.log (2 * c) / Real.log N
        = (Real.log N - Real.log (2 * c)) / Real.log N := by field_simp
    rw [hLHS]; gcongr
  · filter_upwards [eventually_ge_atTop c, eventually_ge_atTop 2] with N hN hN2
    have hlogN : (0:ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hle : (↑(N / c) : ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_le_self N c
    have h1 : (1:ℝ) ≤ (↑(N / c) : ℝ) := by
      have : 1 ≤ N / c := (Nat.one_le_div_iff hc).mpr hN
      exact_mod_cast this
    rw [div_le_one hlogN]
    exact Real.log_le_log (by linarith) hle

/-- **The shifted unrestricted sum, `/log N → 1`.** For fixed `k`, `(∑_{n≤N/p^k}μ²/φ) / log N → 1`,
via `U(M)/log M → 1` composed with `M = N/p^k → ∞`, times `log(N/p^k)/log N → 1`. The per-`k`
ingredient of the dominated-convergence interchange. -/
theorem U_shift_div_log_tendsto_one (p k : ℕ) (hp : p.Prime) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 (N / p^k), gMoebiusSqTotient n) / Real.log (N:ℝ))
      atTop (𝓝 1) := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  have hdiv : Tendsto (fun N : ℕ => N / p ^ k) atTop atTop := by
    apply tendsto_atTop_atTop_of_monotone
    · intro a b hab; exact Nat.div_le_div_right hab
    · intro b; exact ⟨b * p ^ k, by rw [Nat.mul_div_cancel _ hpk]⟩
  have h1 := U_div_log_tendsto_one.comp hdiv
  have h2 := log_div_ratio_tendsto_one (p^k) hpk
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (2 * p^k), eventually_ge_atTop 2] with N hN hN2
  have hge2 : 2 ≤ N / p^k := by rw [Nat.le_div_iff_mul_le hpk]; omega
  have hlogpos : (0:ℝ) < Real.log (↑(N / p^k)) := Real.log_pos (by exact_mod_cast hge2)
  simp only [Function.comp]
  field_simp

/-- **Single-prime coprime sharp Mertens (`p ≥ 3`), UNCONDITIONAL.** For an odd prime `p`,
`(∑_{n≤N,(n,p)=1}μ²/φ) / log N → (p-1)/p = φ(p)/p`. The complete geometric route: the inverted series
(`coprime_geometric_inversion`) `S(N)/log N = ∑'_k (-1/(p-1))^k·(U(N/p^k)/log N)` converges term-by-term
(`U_shift_div_log_tendsto_one`) to `∑'_k(-1/(p-1))^k = (p-1)/p` (`geom_value`), the interchange
justified by dominated convergence (`tendsto_tsum_of_dominated_convergence`, bound `(1/(p-1))^k·2`,
summable since `1/(p-1) < 1` for `p ≥ 3`). No BV, no Euler product — only the repo's unrestricted sharp
Mertens. [The `p = 2` case `1/(p-1) = 1` defeats this DCT (the limit series `∑(-1)^k` diverges) and is
the remaining nut — it needs the bounded-difference form `U(M) = log M + O(1)` or a signed Abel
argument. The general `W = ∏_{p≤D₀}p` then follows by induction over its prime factors, but since `W`
includes `2`, the induction's `2`-step requires the `p = 2` single-prime result.] -/
theorem single_prime_coprime_mertens (p : ℕ) (hpp : p.Prime) (hp3 : 3 ≤ p) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime p n) / Real.log (N:ℝ))
      atTop (𝓝 (((p:ℝ)-1)/p)) := by
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
  set c : ℝ := 1/((p:ℝ)-1) with hcdef
  set f : ℕ → ℕ → ℝ := fun N k =>
    (-c)^k * ((∑ n ∈ Finset.Icc 1 (N / p^k), gMoebiusSqTotient n) / Real.log (N:ℝ)) with hf
  have heq : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime p n) / Real.log (N:ℝ)
      = ∑' k : ℕ, f N k := by
    intro N
    rw [coprime_geometric_inversion p hpp N, div_eq_mul_inv, ← tsum_mul_right]
    apply tsum_congr; intro k
    simp only [hf, div_eq_mul_inv]; ring
  have hclt : c < 1 := by rw [hcdef, div_lt_one hpos]; linarith
  have hcnn : 0 ≤ c := by rw [hcdef]; exact le_of_lt (div_pos one_pos hpos)
  have hsum : Summable (fun k : ℕ => c^k * 2) :=
    (summable_geometric_of_lt_one hcnn hclt).mul_right 2
  have hab : ∀ k : ℕ, Tendsto (fun N => f N k) atTop (𝓝 ((-c)^k)) := by
    intro k
    have h := (tendsto_const_nhds (x := (-c)^k)).mul (U_shift_div_log_tendsto_one p k hpp)
    rw [mul_one] at h
    exact h
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖f N k‖ ≤ c^k * 2 := by
    have hUbdd : ∀ᶠ N in atTop, (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n)/Real.log N ≤ 2 :=
      (U_div_log_tendsto_one.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))).mono
        (fun N hN => le_of_lt hN)
    filter_upwards [hUbdd, eventually_ge_atTop 2] with N hUN hN2
    intro k
    have hlogN : (0:ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hUnn : 0 ≤ (∑ n ∈ Finset.Icc 1 (N/p^k), gMoebiusSqTotient n)/Real.log N :=
      div_nonneg (Finset.sum_nonneg (fun n _ => gMoebiusSqTotient_nonneg n)) (le_of_lt hlogN)
    have hmono : (∑ n ∈ Finset.Icc 1 (N/p^k), gMoebiusSqTotient n)/Real.log N
        ≤ (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n)/Real.log N :=
      (div_le_div_iff_of_pos_right hlogN).mpr (U_mono (Nat.div_le_self N (p^k)))
    have hnf : ‖f N k‖ = c^k * ((∑ n ∈ Finset.Icc 1 (N/p^k), gMoebiusSqTotient n)/Real.log N) := by
      rw [hf, norm_mul]
      congr 1
      · rw [norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hcnn]
      · rw [Real.norm_eq_abs, abs_of_nonneg hUnn]
    rw [hnf]
    exact mul_le_mul_of_nonneg_left (le_trans hmono hUN) (by positivity)
  have hfinal := tendsto_tsum_of_dominated_convergence hsum hab hbound
  have hgv : (∑' k : ℕ, (-c)^k) = ((p:ℝ)-1)/p := by rw [hcdef]; exact geom_value p hp3
  rw [hgv] at hfinal
  exact hfinal.congr (fun N => (heq N).symm)

end BoundedGaps.CoprimeMertens
