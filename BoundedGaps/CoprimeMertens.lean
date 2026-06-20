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

/-- **General per-term identity** (coprimality base `V`). For `p` prime with `p ∤ V`,
`g_V(p·m) = (1/(p-1))·g_{pV}(m)` where `g_W(n) = (μ²/φ)(n)·[(n,W)=1]`. Generalises `per_term`
(the `V = 1` case). -/
theorem per_term_general (p m V : ℕ) (hp : p.Prime) (hpV : Nat.Coprime p V) :
    gMuSqTotientCoprime V (p * m)
      = (1 / ((p : ℝ) - 1)) * gMuSqTotientCoprime (p * V) m := by
  unfold gMuSqTotientCoprime
  by_cases hcm : Nat.Coprime m V
  · have hpmV : Nat.Coprime (p * m) V := Nat.coprime_mul_iff_left.mpr ⟨hpV, hcm⟩
    rw [if_pos hpmV]
    have hpt := per_term p m hp
    rw [gMoebiusSqTotient_apply, hpt]
    by_cases hcp : Nat.Coprime m p
    · have hmpV : Nat.Coprime m (p * V) := Nat.coprime_mul_iff_right.mpr ⟨hcp, hcm⟩
      rw [if_pos hmpV, if_pos hcp, gMoebiusSqTotient_apply]
    · have hnmpV : ¬ Nat.Coprime m (p * V) := fun h => hcp (Nat.coprime_mul_iff_right.mp h).1
      rw [if_neg hnmpV, if_neg hcp, mul_zero]
  · have hnpmV : ¬ Nat.Coprime (p * m) V := fun h => hcm (Nat.coprime_mul_iff_left.mp h).2
    rw [if_neg hnpmV]
    have hnmpV : ¬ Nat.Coprime m (p * V) := fun h => hcm (Nat.coprime_mul_iff_right.mp h).2
    rw [if_neg hnmpV, mul_zero]

/-- **General single-prime coprime recursion** (the inductive step toward `hBaseW`). For `p`
prime with `p ∤ V`,
  `∑_{n≤N,(n,V)=1} μ²/φ = ∑_{n≤N,(n,pV)=1} μ²/φ + (1/(p-1))·∑_{n≤N/p,(n,pV)=1} μ²/φ`,
i.e. `S_V(N) = S_{pV}(N) + (1/(p-1))·S_{pV}(N/p)`. Generalises `coprime_mertens_recursion`
(`V = 1`, `S_1 = U`). Inverts geometrically to express `S_{pV}` via `S_V`, the engine of the
prime-by-prime induction `S_1 = U → S_2 → S_{2·3} → ⋯ → S_W` giving `hBaseW`. -/
theorem coprime_mertens_recursion_general (p V : ℕ) (hp : p.Prime)
    (hpV : Nat.Coprime p V) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime V n)
      = (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (p * V) n)
        + (1 / ((p : ℝ) - 1))
          * ∑ n ∈ Finset.Icc 1 (N / p), gMuSqTotientCoprime (p * V) n := by
  have hcoe : ∀ n, ¬ p ∣ n → gMuSqTotientCoprime (p * V) n = gMuSqTotientCoprime V n := by
    intro n hn
    unfold gMuSqTotientCoprime
    have hcp : Nat.Coprime n p := (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hn))
    by_cases hcv : Nat.Coprime n V
    · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hcp, hcv⟩), if_pos hcv]
    · rw [if_neg (fun h => hcv (Nat.coprime_mul_iff_right.mp h).2), if_neg hcv]
  have hzero : ∀ n, p ∣ n → gMuSqTotientCoprime (p * V) n = 0 := by
    intro n hn
    unfold gMuSqTotientCoprime
    rw [if_neg]
    intro h
    have hcp : Nat.Coprime n p := (Nat.coprime_mul_iff_right.mp h).1
    exact absurd hn ((hp.coprime_iff_not_dvd).mp hcp.symm)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)
    (fun n => gMuSqTotientCoprime V n)
  -- hA : ∑_{¬p∣n} gV = ∑ g_{pV}
  have hA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n), gMuSqTotientCoprime V n
      = ∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (p * V) n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hpd : p ∣ n
    · rw [if_neg (not_not.mpr hpd), hzero n hpd]
    · rw [if_pos hpd, hcoe n hpd]
  -- hB : ∑_{p∣n} gV = (1/(p-1)) ∑_{n≤N/p} g_{pV}
  have hB : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), gMuSqTotientCoprime V n
      = (1 / ((p : ℝ) - 1)) * ∑ n ∈ Finset.Icc 1 (N / p), gMuSqTotientCoprime (p * V) n := by
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
      rw [← per_term_general p (a / p) V hp hpV, Nat.mul_div_cancel' ha.2]
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

/-- **Summability of the general inverted series** (coprimality base `V`). Mirror of
`inversion_summable`. -/
theorem inversion_summable_general (p V : ℕ) (hp : p.Prime) (N : ℕ) :
    Summable (fun k : ℕ =>
      (- (1 / ((p:ℝ)-1)))^k * (∑ n ∈ Finset.Icc 1 (N / p^k), gMuSqTotientCoprime V n)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (N+1)) ?_
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have hpk : N < p ^ k := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
    (Nat.pow_le_pow_right hp.pos (by omega))
  rw [Nat.div_eq_of_lt hpk]; simp

/-- **General geometric inversion** (the inductive step for `hBaseW`). Inverting
`coprime_mertens_recursion_general` expresses the finer `pV`-coprime sum via the coarser
`V`-coprime sums:
  `∑_{n≤N,(n,pV)=1} μ²/φ = ∑_{k≥0} (-1/(p-1))^k · ∑_{n≤N/p^k,(n,V)=1} μ²/φ`,
i.e. `S_{pV}(N) = ∑_k (-1/(p-1))^k S_V(N/p^k)`. Generalises `coprime_geometric_inversion`
(`V = 1`, `S_1 = U`). With the base limit `S_V/log N → φ(V)/V`, taking `/log N` term-by-term
(DCT for odd `p`; recursion + second-order for `p = 2`, only needed at `V = 1`) yields
`S_{pV}/log N → (φ(V)/V)·(p-1)/p = φ(pV)/(pV)`. UNCONDITIONAL. -/
theorem coprime_geometric_inversion_general (p V : ℕ) (hp : p.Prime) (hpV : Nat.Coprime p V)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (p * V) n)
      = ∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^k
          * (∑ n ∈ Finset.Icc 1 (N / p^k), gMuSqTotientCoprime V n) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hz : ∀ k : ℕ, (- (1 / ((p:ℝ)-1)))^k
          * (∑ n ∈ Finset.Icc 1 (0 / p^k), gMuSqTotientCoprime V n) = 0 := by
        intro k; rw [Nat.zero_div]; simp
      rw [tsum_congr hz, tsum_zero]; simp
    · rw [(inversion_summable_general p V hp N).tsum_eq_zero_add]
      have hterm0 : (- (1 / ((p:ℝ)-1)))^0
          * (∑ n ∈ Finset.Icc 1 (N / p^0), gMuSqTotientCoprime V n)
          = ∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime V n := by
        rw [pow_zero, one_mul, pow_zero, Nat.div_one]
      have htail : (∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^(k+1)
            * (∑ n ∈ Finset.Icc 1 (N / p^(k+1)), gMuSqTotientCoprime V n))
          = (- (1 / ((p:ℝ)-1)))
            * (∑' k : ℕ, (- (1 / ((p:ℝ)-1)))^k
                * (∑ n ∈ Finset.Icc 1 ((N / p) / p^k), gMuSqTotientCoprime V n)) := by
        rw [← tsum_mul_left]
        apply tsum_congr; intro k
        have hdiv : N / p^(k+1) = (N / p) / p^k := by
          rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
        rw [hdiv, pow_succ]; ring
      rw [hterm0, htail, ← ih (N / p) (Nat.div_lt_self hN hp.one_lt)]
      have hrec := coprime_mertens_recursion_general p V hp hpV N
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

/-! ## Toward general `W`: nonneg / domination helpers and the abstract inductive step -/

theorem gMuSqTotientCoprime_nonneg (V n : ℕ) : 0 ≤ gMuSqTotientCoprime V n := by
  unfold gMuSqTotientCoprime
  split_ifs with h
  · exact gMoebiusSqTotient_nonneg n
  · exact le_refl 0

theorem SV_le_U (V M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, gMuSqTotientCoprime V n)
      ≤ ∑ n ∈ Finset.Icc 1 M, gMoebiusSqTotient n := by
  apply Finset.sum_le_sum
  intro n _
  unfold gMuSqTotientCoprime
  split_ifs with h
  · exact le_refl _
  · exact gMoebiusSqTotient_nonneg n

theorem SV_mono (V : ℕ) {M M' : ℕ} (h : M ≤ M') :
    (∑ n ∈ Finset.Icc 1 M, gMuSqTotientCoprime V n)
      ≤ ∑ n ∈ Finset.Icc 1 M', gMuSqTotientCoprime V n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun i _ _ => gMuSqTotientCoprime_nonneg V i)

theorem SV_shift_div_log_tendsto (p k V : ℕ) (hp : p.Prime) (c : ℝ)
    (hbase : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime V n) / Real.log N)
      atTop (𝓝 c)) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 (N / p^k), gMuSqTotientCoprime V n) / Real.log (N:ℝ)) atTop (𝓝 c) := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  have hdiv : Tendsto (fun N : ℕ => N / p ^ k) atTop atTop := by
    apply tendsto_atTop_atTop_of_monotone
    · intro a b hab; exact Nat.div_le_div_right hab
    · intro b; exact ⟨b * p ^ k, by rw [Nat.mul_div_cancel _ hpk]⟩
  have h1 := hbase.comp hdiv
  have h2 := log_div_ratio_tendsto_one (p^k) hpk
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (2 * p^k), eventually_ge_atTop 2] with N hN hN2
  have hge2 : 2 ≤ N / p^k := by rw [Nat.le_div_iff_mul_le hpk]; omega
  have hlogpos : (0:ℝ) < Real.log (↑(N / p^k)) := Real.log_pos (by exact_mod_cast hge2)
  simp only [Function.comp]
  field_simp

/-- **Abstract single-prime step** (`p ≥ 3`): from a base limit `S_V(N)/log N → c` derive
`S_{pV}(N)/log N → c·(p-1)/p`. General inversion + DCT (bound `(1/(p-1))^k·2` via `S_V ≤ U` and
`U/log → 1`), interchange via `geom_value`. The inductive step of `hBaseW` for odd primes: starting
from `S_2/log → 1/2` (`single_prime_coprime_mertens_two`), repeatedly apply this for the odd primes
of `W` to reach `S_W/log → φ(W)/W`. (The `p = 2` step needs the second-order route and is only used
once, at the base `V = 1`.) -/
theorem coprime_step (p V : ℕ) (hp : p.Prime) (hpV : Nat.Coprime p V) (hp3 : 3 ≤ p) (c : ℝ)
    (hbase : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime V n) / Real.log N)
      atTop (𝓝 c)) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (p * V) n) / Real.log (N:ℝ))
      atTop (𝓝 (c * (((p:ℝ)-1)/p))) := by
  have hpR : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have hpos : (0:ℝ) < (p:ℝ) - 1 := by linarith
  set cp : ℝ := 1/((p:ℝ)-1) with hcpdef
  set f : ℕ → ℕ → ℝ := fun N k =>
    (-cp)^k * ((∑ n ∈ Finset.Icc 1 (N / p^k), gMuSqTotientCoprime V n) / Real.log (N:ℝ)) with hf
  have heq : ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (p * V) n) / Real.log (N:ℝ) = ∑' k : ℕ, f N k := by
    intro N
    rw [coprime_geometric_inversion_general p V hp hpV N, div_eq_mul_inv, ← tsum_mul_right]
    apply tsum_congr; intro k
    simp only [hf, div_eq_mul_inv]; ring
  have hclt : cp < 1 := by rw [hcpdef, div_lt_one hpos]; linarith
  have hcnn : 0 ≤ cp := by rw [hcpdef]; exact le_of_lt (div_pos one_pos hpos)
  have hsum : Summable (fun k : ℕ => cp^k * 2) :=
    (summable_geometric_of_lt_one hcnn hclt).mul_right 2
  have hab : ∀ k : ℕ, Tendsto (fun N => f N k) atTop (𝓝 ((-cp)^k * c)) := by
    intro k
    exact (tendsto_const_nhds (x := (-cp)^k)).mul (SV_shift_div_log_tendsto p k V hp c hbase)
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖f N k‖ ≤ cp^k * 2 := by
    have hUbdd : ∀ᶠ N in atTop, (∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n)/Real.log N ≤ 2 :=
      (U_div_log_tendsto_one.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))).mono
        (fun N hN => le_of_lt hN)
    filter_upwards [hUbdd, eventually_ge_atTop 2] with N hUN hN2
    intro k
    have hlogN : (0:ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hSVnn : 0 ≤ (∑ n ∈ Finset.Icc 1 (N/p^k), gMuSqTotientCoprime V n)/Real.log N :=
      div_nonneg (Finset.sum_nonneg (fun n _ => gMuSqTotientCoprime_nonneg V n)) (le_of_lt hlogN)
    have hle2 : (∑ n ∈ Finset.Icc 1 (N/p^k), gMuSqTotientCoprime V n)/Real.log N ≤ 2 := by
      refine le_trans ?_ hUN
      exact (div_le_div_iff_of_pos_right hlogN).mpr
        (le_trans (SV_le_U V (N/p^k)) (U_mono (Nat.div_le_self N (p^k))))
    have hnf : ‖f N k‖
        = cp^k * ((∑ n ∈ Finset.Icc 1 (N/p^k), gMuSqTotientCoprime V n)/Real.log N) := by
      rw [hf, norm_mul]
      congr 1
      · rw [norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hcnn]
      · rw [Real.norm_eq_abs, abs_of_nonneg hSVnn]
    rw [hnf]
    exact mul_le_mul_of_nonneg_left hle2 (by positivity)
  have hfinal := tendsto_tsum_of_dominated_convergence hsum hab hbound
  have hgv : (∑' k : ℕ, (-cp)^k * c) = c * (((p:ℝ)-1)/p) := by
    rw [tsum_mul_right, hcpdef]
    rw [show ∑' k : ℕ, (-(1/((p:ℝ)-1)))^k = ((p:ℝ)-1)/p from geom_value p hp3]
    ring
  rw [hgv] at hfinal
  exact hfinal.congr (fun N => (heq N).symm)

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

/-! ## The `p = 2` single-prime case (the DCT-defeating nut)

For `p = 2` the geometric inversion coefficient `−1/(p−1) = −1` makes the inverted series
`∑_k (−1)^k U(N/2^k)` an alternating series of a *diverging* sequence, so the `p ≥ 3` DCT
route fails. The correct route uses the recursion `U N = T N + T⌊N/2⌋` directly, together with
the **second-order** Mertens `SharpMertens.sum_g_second_order` (`U(N) − log N → β`, which the
first-order `sharp_mertens_unconditional` cannot supply). Everything reduces to a single
abstract analytic crux: a *halving recursion with bounded RHS-limit forces `o(log N)`*. -/

/-! ## Discharging the crux `halving_recursion_o_log` (UNCONDITIONAL)

A halving recursion with bounded RHS-limit forces `o(log N)`. Proved in-kernel via the
`L = 0` reduction (the constant `L/2` solves `g + g∘half = L`, killing the alternation): then
`V = d + d∘half → 0` and the naive triangle bound on the exact unrolling already gives `o(log N)`,
the only content being `∑_{k<K}|V⌊N/2^k⌋| ≤ ε·K + C` (good terms `≤ ε`; bad-argument terms inject
into `{1,…,M₀}`). This replaces the lap-7 disclosed `axiom`. -/

theorem halving_unroll (d : ℕ → ℝ) (N m : ℕ) :
    d N = (∑ k ∈ Finset.range m, (-1 : ℝ) ^ k * (d (N / 2 ^ k) + d (N / 2 ^ k / 2)))
      + (-1) ^ m * d (N / 2 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hdiv : N / 2 ^ m / 2 = N / 2 ^ (m + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [Finset.sum_range_succ, hdiv]; linear_combination ih

theorem natlog_mul_log_two_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h2N : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    have : (2 : ℕ) ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
    exact_mod_cast this
  have := Real.log_le_log (by positivity) h2N
  rwa [Real.log_pow] at this

theorem halving_o_log_zero (d : ℕ → ℝ)
    (hd0 : Tendsto (fun N : ℕ => d N + d (N / 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => d N / Real.log N) atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun M => |d M + d (M / 2)| with hadef
  have ha0 : Tendsto a atTop (𝓝 0) := by have := hd0.abs; simpa [hadef] using this
  have hanneg : ∀ M, 0 ≤ a M := fun M => abs_nonneg _
  have hdbound : ∀ N : ℕ, 1 ≤ N →
      |d N| ≤ (∑ k ∈ Finset.range (Nat.log 2 N + 1), a (N / 2 ^ k)) + |d 0| := by
    intro N hN
    have hzero : N / 2 ^ (Nat.log 2 N + 1) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) N)
    have hun := halving_unroll d N (Nat.log 2 N + 1)
    rw [hzero] at hun
    rw [hun]
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hadef]
    · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hsumbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      (∑ k ∈ Finset.range (Nat.log 2 N + 1), a (N / 2 ^ k))
        ≤ ε * ((Nat.log 2 N : ℝ) + 1) + C := by
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp ha0 ε hε)
    refine ⟨∑ M ∈ Finset.Ico 1 M₀, a M, fun N hN => ?_⟩
    have hargpos : ∀ k ∈ Finset.range (Nat.log 2 N + 1), 1 ≤ N / 2 ^ k := by
      intro k hk
      rw [Finset.mem_range] at hk
      have : 2 ^ k ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.pow_log_le_self 2 (by omega))
      exact (Nat.one_le_div_iff (by positivity)).mpr this
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Nat.log 2 N + 1))
      (fun k => M₀ ≤ N / 2 ^ k)]
    gcongr ?_ + ?_
    · -- good ≤ ε*(↑(Nat.log2N)+1)
      refine le_trans (Finset.sum_le_sum (g := fun _ => ε) ?_) ?_
      · intro k hk
        rw [Finset.mem_filter] at hk
        have := hM₀ (N / 2 ^ k) hk.2
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hanneg _)] at this
        exact this.le
      · rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (((Finset.range (Nat.log 2 N + 1)).filter
            (fun k => M₀ ≤ N / 2 ^ k)).card : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
          have : ((Finset.range (Nat.log 2 N + 1)).filter (fun k => M₀ ≤ N / 2 ^ k)).card
              ≤ Nat.log 2 N + 1 :=
            le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
          calc (((Finset.range (Nat.log 2 N + 1)).filter (fun k => M₀ ≤ N / 2 ^ k)).card : ℝ)
                ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by exact_mod_cast this
            _ = (Nat.log 2 N : ℝ) + 1 := by push_cast; ring
        calc (((Finset.range (Nat.log 2 N + 1)).filter (fun k => M₀ ≤ N / 2 ^ k)).card : ℝ) * ε
              ≤ ((Nat.log 2 N : ℝ) + 1) * ε := by gcongr
          _ = ε * ((Nat.log 2 N : ℝ) + 1) := by ring
    · -- bad ≤ ∑_{Ico 1 M₀} a M
      have hstrict : ∀ x y : ℕ, x < y → 1 ≤ N / 2 ^ x → N / 2 ^ y < N / 2 ^ x := by
        intro x y hlt hpos
        have he : x + (y - x) = y := by omega
        rw [show N / 2 ^ y = N / 2 ^ x / 2 ^ (y - x) by rw [Nat.div_div_eq_div_mul, ← pow_add, he]]
        apply Nat.div_lt_self (by omega)
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (y - x) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hinj : Set.InjOn (fun k => N / 2 ^ k)
          ((Finset.range (Nat.log 2 N + 1)).filter (fun k => ¬ M₀ ≤ N / 2 ^ k) : Finset ℕ) := by
        intro k₁ hk₁ k₂ hk₂ heq
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk₁ hk₂
        simp only at heq
        by_contra hne
        rcases Nat.lt_or_ge k₁ k₂ with h | h
        · exact absurd heq.symm (hstrict k₁ k₂ h (hargpos k₁ (Finset.mem_range.mpr hk₁.1))).ne
        · exact absurd heq (hstrict k₂ k₁ (by omega) (hargpos k₂ (Finset.mem_range.mpr hk₂.1))).ne
      rw [← Finset.sum_image hinj]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro M hM
        rw [Finset.mem_image] at hM
        obtain ⟨k, hk, rfl⟩ := hM
        rw [Finset.mem_filter, not_le] at hk
        rw [Finset.mem_Ico]
        exact ⟨hargpos k hk.1, hk.2⟩
      · intro M _ _; exact hanneg M
  -- assemble
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ * Real.log 2 / 2 with hεdef
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨C, hC⟩ := hsumbound ε hε
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop, (ε + C + |d 0|) / Real.log N < δ / 2 := by
    have h := (tendsto_const_nhds (x := ε + C + |d 0|)).div_atTop hlogtop
    exact h.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 2))
  obtain ⟨N₀, hN₀⟩ := (hsmall.and ((hlogtop.eventually_gt_atTop 0).and
    (eventually_ge_atTop 1))).exists_forall_of_atTop
  refine ⟨N₀, fun N hNN₀ => ?_⟩
  obtain ⟨hsm, hlog0, hN1⟩ := hN₀ N hNN₀
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog0]
  have hb := hdbound N hN1
  have hsb := hC N hN1
  have hexp : ε * ((Nat.log 2 N : ℝ) + 1) = ε * (Nat.log 2 N : ℝ) + ε := by ring
  have hdb' : |d N| ≤ ε * (Nat.log 2 N : ℝ) + (ε + C + |d 0|) := by
    rw [hexp] at hsb; linarith [hb]
  have hstep : ε * (Nat.log 2 N : ℝ) / Real.log N ≤ δ / 2 := by
    rw [div_le_iff₀ hlog0]
    have heq : ε * (Nat.log 2 N : ℝ) = (δ / 2) * ((Nat.log 2 N : ℝ) * Real.log 2) := by
      rw [hεdef]; ring
    rw [heq]
    calc (δ / 2) * ((Nat.log 2 N : ℝ) * Real.log 2)
          ≤ (δ / 2) * Real.log N :=
          mul_le_mul_of_nonneg_left (natlog_mul_log_two_le N hN1) (by positivity)
      _ = δ / 2 * Real.log N := rfl
  have h1 : |d N| / Real.log N
      ≤ ε * (Nat.log 2 N : ℝ) / Real.log N + (ε + C + |d 0|) / Real.log N := by
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hlog0).mpr hdb'
  linarith [hstep, hsm, h1]

theorem halving_recursion_o_log (d : ℕ → ℝ) (L : ℝ)
    (hd : Tendsto (fun N : ℕ => d N + d (N / 2)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => d N / Real.log N) atTop (𝓝 0) := by
  have hd0 : Tendsto (fun N : ℕ => (d N - L / 2) + ((fun M => d M - L / 2) (N / 2))) atTop (𝓝 0) := by
    have h := hd.sub (tendsto_const_nhds (x := L))
    rw [sub_self] at h
    refine h.congr (fun N => ?_)
    simp only; ring
  have hcore := halving_o_log_zero (fun M => d M - L / 2) hd0
  have hconst : Tendsto (fun N : ℕ => (L / 2) / Real.log N) atTop (𝓝 0) := by
    have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hsum := hcore.add hconst
  rw [add_zero] at hsum
  refine hsum.congr (fun N => ?_)
  try simp only
  rw [← add_div]
  ring_nf


/-- `log N − log⌊N/2⌋ → log 2`. Squeeze between `log 2` (from `⌊N/2⌋ ≤ N/2`) and
`log(N/(N−1)) + log 2` (from `2⌊N/2⌋ ≥ N−1`). -/
theorem log_sub_log_half_tendsto :
    Tendsto (fun N : ℕ => Real.log N - Real.log (↑(N / 2))) atTop (𝓝 (Real.log 2)) := by
  have hupp : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / ((N : ℝ) - 1)) + Real.log 2) atTop
      (𝓝 (Real.log 2)) := by
    have hr : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) - 1)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (1 - 1 / (N : ℝ))) atTop (𝓝 (1 / (1 - 0))) := by
        apply Tendsto.div tendsto_const_nhds
        · exact (tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat))
        · norm_num
      simp only [sub_zero, div_one] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hN1 : (N : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      field_simp
    have : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / ((N : ℝ) - 1))) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp hr
    rw [Real.log_one] at this
    simpa using this.add (tendsto_const_nhds (x := Real.log 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hhalf_pos : 1 ≤ N / 2 := (Nat.one_le_div_iff (by norm_num)).mpr hN
    have hle : (↑(N / 2) : ℝ) ≤ (N : ℝ) / 2 := by exact_mod_cast Nat.cast_div_le
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hhpos : (0 : ℝ) < (↑(N / 2) : ℝ) := by exact_mod_cast hhalf_pos
    have hlog : Real.log (↑(N / 2) : ℝ) ≤ Real.log ((N : ℝ) / 2) :=
      Real.log_le_log hhpos hle
    rw [Real.log_div (by positivity) (by norm_num)] at hlog
    linarith
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hN3 : 3 ≤ N := hN
    have hhalf_pos : 1 ≤ N / 2 := (Nat.one_le_div_iff (by norm_num)).mpr (by omega)
    have hge : N - 1 ≤ 2 * (N / 2) := by omega
    have hcast : ((N : ℝ) - 1) / 2 ≤ (↑(N / 2) : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]
      have : ((N : ℝ) - 1) ≤ 2 * (↑(N / 2) : ℝ) := by
        have : (N : ℝ) - 1 ≤ ((2 * (N / 2) : ℕ) : ℝ) := by
          calc (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
                rw [Nat.cast_sub (by omega)]; norm_num
            _ ≤ ((2 * (N / 2) : ℕ) : ℝ) := by exact_mod_cast hge
        push_cast at this ⊢; linarith
      linarith
    have hNm1pos : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      linarith
    have hhpos : (0 : ℝ) < (↑(N / 2) : ℝ) := by exact_mod_cast hhalf_pos
    have hlog : Real.log (((N : ℝ) - 1) / 2) ≤ Real.log (↑(N / 2) : ℝ) :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_div (by positivity) (by norm_num)] at hlog
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    rw [Real.log_div (by positivity) (by positivity)]
    linarith

/-- Halving `N ↦ ⌊N/2⌋` tends to infinity. -/
theorem tendsto_half_atTop : Tendsto (fun N : ℕ => N / 2) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · intro a b hab; exact Nat.div_le_div_right hab
  · intro K; exact ⟨2 * K, by rw [Nat.mul_div_cancel_left _ (by norm_num)]⟩

/-- **Single-prime coprime sharp Mertens at `p = 2`** (modulo the isolated crux
`halving_recursion_o_log`). `(∑_{n≤N,(n,2)=1} μ²/φ)/log N → 1/2 = (2−1)/2`, matching the
`p ≥ 3` formula at `p = 2`.

Reduction: with `T N = ∑_{(n,2)=1} μ²/φ`, `U N = ∑ μ²/φ`, the recursion
`coprime_mertens_recursion 2` reads `U N = T N + T⌊N/2⌋`. Set `D N = T N − T⌊N/2⌋`; then
`D N + D⌊N/2⌋ = U N − U⌊N/2⌋ → log 2` (via the **second-order** Mertens
`SharpMertens.sum_g_second_order` and `log_sub_log_half_tendsto`). The crux gives
`D N/log N → 0`, and since `T N = (U N + D N)/2`,
`T N/log N = (U N/log N + D N/log N)/2 → (1+0)/2 = 1/2`. -/
theorem single_prime_coprime_mertens_two :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime 2 n) / Real.log (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  set T : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime 2 n with hT
  set U : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N, gMoebiusSqTotient n with hU
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hrec : ∀ N : ℕ, U N = T N + T (N / 2) := by
    intro N
    have h := coprime_mertens_recursion 2 hp2 N
    rw [hT, hU]
    simp only
    norm_num at h
    exact h
  set D : ℕ → ℝ := fun N => T N - T (N / 2) with hD
  have hDrec : ∀ N : ℕ, D N + D (N / 2) = U N - U (N / 2) := by
    intro N
    rw [hD]
    simp only
    rw [hrec N, hrec (N / 2)]
    ring
  have hsoU : Tendsto (fun N : ℕ => U N - Real.log N) atTop (𝓝
      (Real.eulerMascheroniConstant - ∑' e : ℕ, BoundedGaps.SharpMertens.bAF e * Real.log e)) :=
    BoundedGaps.SharpMertens.sum_g_second_order
  have hsoUhalf : Tendsto (fun N : ℕ => U (N / 2) - Real.log (↑(N / 2))) atTop (𝓝
      (Real.eulerMascheroniConstant - ∑' e : ℕ, BoundedGaps.SharpMertens.bAF e * Real.log e)) :=
    hsoU.comp tendsto_half_atTop
  have hV : Tendsto (fun N : ℕ => U N - U (N / 2)) atTop (𝓝 (Real.log 2)) := by
    have hcomb := (hsoU.sub hsoUhalf).add log_sub_log_half_tendsto
    have hval : (Real.eulerMascheroniConstant
          - ∑' e : ℕ, BoundedGaps.SharpMertens.bAF e * Real.log e)
        - (Real.eulerMascheroniConstant - ∑' e : ℕ, BoundedGaps.SharpMertens.bAF e * Real.log e)
        + Real.log 2 = Real.log 2 := by ring
    rw [hval] at hcomb
    refine hcomb.congr (fun N => ?_)
    ring
  have hDsum : Tendsto (fun N : ℕ => D N + D (N / 2)) atTop (𝓝 (Real.log 2)) :=
    hV.congr (fun N => (hDrec N).symm)
  have hD0 : Tendsto (fun N : ℕ => D N / Real.log N) atTop (𝓝 0) :=
    halving_recursion_o_log D (Real.log 2) hDsum
  have hU1 : Tendsto (fun N : ℕ => U N / Real.log N) atTop (𝓝 1) := U_div_log_tendsto_one
  have hcomb := (hU1.add hD0).div_const 2
  rw [show ((1 : ℝ) + 0) / 2 = 1 / 2 by norm_num] at hcomb
  refine hcomb.congr (fun N => ?_)
  rw [hD]
  simp only
  rw [hrec N, ← add_div, show T N + T (N / 2) + (T N - T (N / 2)) = 2 * T N from by ring, div_div,
    mul_comm (Real.log (N : ℝ)) 2]
  exact mul_div_mul_left (T N) (Real.log N) two_ne_zero

/-! ## The general-`W` induction over primes -/

/-- **Prime-by-prime product limit** (odd primes). From a base limit `S_{V₀}(N)/log N → c₀`,
multiplying the modulus by a finite set `T` of *odd* primes (each coprime to `V₀`) scales the limit
by `∏_{p∈T}(p-1)/p`:
  `S_{V₀·∏T}(N)/log N → c₀·∏_{p∈T}((p-1)/p)`.
Finset-induction applying `coprime_step` once per prime. The engine of `hBaseW`: start from
`S_2/log → 1/2` (`single_prime_coprime_mertens_two`) or `S_1 = U/log → 1`, then sweep the odd
primes of `W`. UNCONDITIONAL. -/
theorem coprime_prod_limit (V₀ : ℕ) (c₀ : ℝ)
    (hbase : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime V₀ n) / Real.log N)
      atTop (𝓝 c₀)) :
    ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (∀ p ∈ T, 3 ≤ p) → (∀ p ∈ T, Nat.Coprime p V₀) →
      Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (V₀ * ∏ p ∈ T, p) n) / Real.log N)
        atTop (𝓝 (c₀ * ∏ p ∈ T, (((p:ℝ) - 1) / p))) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ _
    simpa using hbase
  | insert p T' hpT' ih =>
    intro hprime h3 hcop
    have hp_prime : p.Prime := hprime p (Finset.mem_insert_self p T')
    have hp3 : 3 ≤ p := h3 p (Finset.mem_insert_self p T')
    have ihT' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      (fun q hq => h3 q (Finset.mem_insert_of_mem hq))
      (fun q hq => hcop q (Finset.mem_insert_of_mem hq))
    -- coprimality of p with V₀ * ∏T'
    have hcopV₀ : Nat.Coprime p V₀ := hcop p (Finset.mem_insert_self p T')
    have hcopProd : Nat.Coprime p (∏ q ∈ T', q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hq_prime : q.Prime := hprime q (Finset.mem_insert_of_mem hq)
      have hpq : p ≠ q := fun h => hpT' (h ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hpq
    have hcopAll : Nat.Coprime p (V₀ * ∏ q ∈ T', q) := hcopV₀.mul_right hcopProd
    have hstep := coprime_step p (V₀ * ∏ q ∈ T', q) hp_prime hcopAll hp3
      (c₀ * ∏ q ∈ T', (((q:ℝ) - 1) / q)) ihT'
    -- rewrite the modulus and the constant via prod_insert
    rw [Finset.prod_insert hpT', Finset.prod_insert hpT']
    have hmod : V₀ * (p * ∏ q ∈ T', q) = p * (V₀ * ∏ q ∈ T', q) := by ring
    rw [hmod]
    have hconst : (c₀ * ∏ q ∈ T', (((q:ℝ) - 1) / q)) * (((p:ℝ) - 1) / p)
        = c₀ * ((((p:ℝ) - 1) / p) * ∏ q ∈ T', (((q:ℝ) - 1) / q)) := by ring
    rw [hconst] at hstep
    exact hstep

/-! ## `hBaseW` DISCHARGED for primorial moduli (`W = ∏` over a prime set containing 2)

Assembling the prime-by-prime induction with the squarefree-product totient identity yields the
W-coprime sharp Mertens `(∑_{n≤N,(n,W)=1} μ²/φ)/log N → φ(W)/W` for any `W = ∏_{p∈T} p` over a
finite set `T` of primes with `2 ∈ T` — in particular the sieve's primorial `∏_{p≤D₀} p`. This is
the sole remaining analytic input `hBaseW` of `WeightedMertens.weighted_mertens_coprime(_sq)`, now
**fully machine-checked and unconditional** (no BV, no PNT, no Euler products). -/

/-- `φ(∏_{p∈T} p) = ∏_{p∈T}(p-1)` for a finite set `T` of primes (squarefree product). -/
theorem prod_primes_totient (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    Nat.totient (∏ p ∈ T, p) = ∏ p ∈ T, (p - 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T' hp ih =>
    have hpp : p.Prime := hT p (Finset.mem_insert_self p T')
    have ihT' := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime p (∏ q ∈ T', q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqp : q.Prime := hT q (Finset.mem_insert_of_mem hq)
      exact (Nat.coprime_primes hpp hqp).mpr (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop, ihT',
      Nat.totient_prime hpp]

/-- `φ(∏T)/∏T = ∏_{p∈T}((p-1)/p)` for a finite set `T` of primes. -/
theorem totient_div_eq_prod (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (Nat.totient (∏ p ∈ T, p) : ℝ) / (∏ p ∈ T, p) = ∏ p ∈ T, (((p:ℝ) - 1) / p) := by
  rw [prod_primes_totient T hT, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have h1 : 1 ≤ p := (hT p hp).one_lt.le
  rw [Nat.cast_sub h1, Nat.cast_one]

/-- **W-coprime sharp Mertens** for `W = ∏_{p∈T} p` (prime set `T` with `2 ∈ T`), in the
`∏(p-1)/p` form: `(∑_{n≤N,(n,W)=1} μ²/φ)/log N → ∏_{p∈T}((p-1)/p)`. Base `S_2/log → 1/2`
(`single_prime_coprime_mertens_two`) swept over the odd primes via `coprime_prod_limit`. -/
theorem hBaseW_of_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (h2 : 2 ∈ T) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (∏ p ∈ T, p) n) / Real.log N)
      atTop (𝓝 (∏ p ∈ T, (((p:ℝ) - 1) / p))) := by
  have hTodd := coprime_prod_limit 2 (1/2) single_prime_coprime_mertens_two (T.erase 2)
    (fun p hp => hT p (Finset.mem_of_mem_erase hp))
    (fun p hp => by
      have hpp : p.Prime := hT p (Finset.mem_of_mem_erase hp)
      have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      have := hpp.two_le; omega)
    (fun p hp => by
      have hpp : p.Prime := hT p (Finset.mem_of_mem_erase hp)
      have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      exact (Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
  have hmod : 2 * ∏ p ∈ T.erase 2, p = ∏ p ∈ T, p :=
    Finset.mul_prod_erase T (fun p => p) h2
  have hconst : (1 / 2 : ℝ) * ∏ p ∈ T.erase 2, (((p:ℝ) - 1) / p)
      = ∏ p ∈ T, (((p:ℝ) - 1) / p) := by
    rw [← Finset.mul_prod_erase T (fun p => (((p:ℝ) - 1) / p)) h2]
    norm_num
  rw [hmod, hconst] at hTodd
  exact hTodd

/-- **`hBaseW`, discharged.** `(∑_{n≤N,(n,W)=1} μ²/φ)/log N → φ(W)/W` for `W = ∏_{p∈T} p`
(`T` a finite set of primes, `2 ∈ T`) — exactly the hypothesis of
`WeightedMertens.weighted_mertens_coprime`. UNCONDITIONAL. -/
theorem hBaseW_of_primes_totient (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (h2 : 2 ∈ T) :
    Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, gMuSqTotientCoprime (∏ p ∈ T, p) n) / Real.log N)
      atTop (𝓝 ((Nat.totient (∏ p ∈ T, p) : ℝ) / (∏ p ∈ T, p))) := by
  rw [totient_div_eq_prod T hT]
  exact hBaseW_of_primes T hT h2

end BoundedGaps.CoprimeMertens
