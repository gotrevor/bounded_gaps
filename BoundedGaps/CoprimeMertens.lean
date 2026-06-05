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

end BoundedGaps.CoprimeMertens
