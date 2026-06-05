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
open BoundedGaps.SingularSeries

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

end BoundedGaps.CoprimeMertens
