/-
# The y-space S1 off-diagonal size bound — the `∑_{p>D₀} 1/p²` tail (UNCONDITIONAL)

The off-diagonal leg of the y-space S1 correction bound (`S1Correction.yspace_correction_abs_bound`)
is `∑_{¬diag P} |∏λλ| · M/∏[dᵢ,eᵢ]`. Classically (Maynard/GPY) this is `o(M·(log R)^k)` because each
off-diagonal `P` carries a *shared prime* `p > D₀` between two coordinates, contributing a `1/p²`
weight to the singular-series discrepancy; summed over all shared primes this is
`∑_{i<j} ∑_{p>D₀} 1/p² → 0` as `D₀ → ∞` — purely a **convergent-series tail**, NO BV/EH.

This file isolates that analytic engine: the `1/n²` (Basel-type) `p`-series tail tends to `0`, and any
finite reciprocal-square sum over a set of naturals all exceeding `D₀` (e.g. the shared primes) is
bounded by that tail. Combined with the off-diagonal vanishing of `S1Correction`, this is the
elementary (unconditional) core of the off-diagonal size estimate.
-/
import BoundedGaps.SieveExpansion

open Filter Topology
open scoped BigOperators

namespace BoundedGaps.S1OffDiagSize

/-- Summability of `1/(k+D₀)²` (the shifted Basel `p`-series). -/
theorem summable_recip_sq_shift (D₀ : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((k + D₀ : ℕ):ℝ)^2) := by
  have hf : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff D₀).mpr hf

/-- **The `1/n²` tail tends to 0.** As `D₀ → ∞`, `∑_{k} 1/(k+D₀)² → 0`. The convergent-series tail
of the Basel-type `p`-series (`tendsto_sum_nat_add`). The analytic engine behind the off-diagonal
S1 correction: a shared prime `p > D₀` contributes a `1/p²` weight, and these sum to `o(1)`. -/
theorem recip_sq_tail_tendsto_zero :
    Tendsto (fun D₀ : ℕ => ∑' k : ℕ, (1:ℝ)/((k + D₀ : ℕ):ℝ)^2) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n => (1:ℝ)/(n:ℝ)^2)

/-- **Finite reciprocal-square sum over a tail set ≤ the infinite tail.** Any finite set `s` of
naturals all exceeding `D₀` (e.g. the shared primes `> D₀` of an off-diagonal tuple) satisfies
`∑_{n∈s}1/n² ≤ ∑'_k 1/(k+(D₀+1))²`. Combined with `recip_sq_tail_tendsto_zero` this gives a
**uniform** `o(1)` bound (in `D₀`) on the off-diagonal singular-series weight — the `∑_{p>D₀}1/p²`
factor of the S1 correction off-diagonal leg, with NO BV/EH. -/
theorem sum_finset_recip_sq_le_tail (D₀ : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, D₀ < n) :
    ∑ n ∈ s, (1:ℝ)/(n:ℝ)^2 ≤ ∑' k : ℕ, (1:ℝ)/((k + (D₀ + 1) : ℕ):ℝ)^2 := by
  classical
  set g : ℕ → ℝ := fun k => (1:ℝ)/((k + (D₀ + 1) : ℕ):ℝ)^2 with hg
  have hginj : Set.InjOn (fun n => n - (D₀ + 1)) s := by
    intro a ha b hb hab
    have ha' : D₀ + 1 ≤ a := hs a ha
    have hb' : D₀ + 1 ≤ b := hs b hb
    simp only at hab
    omega
  have hstep : ∑ n ∈ s, (1:ℝ)/(n:ℝ)^2 = ∑ j ∈ s.image (fun n => n - (D₀ + 1)), g j := by
    rw [Finset.sum_image hginj]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' : D₀ + 1 ≤ n := hs n hn
    rw [hg]
    simp only
    rw [show n - (D₀ + 1) + (D₀ + 1) = n from by omega]
  rw [hstep]
  refine (summable_recip_sq_shift (D₀ + 1)).sum_le_tsum _ (fun j _ => ?_)
  rw [hg]; positivity

/-- **Off-diagonal union-bound reduction.** With nonnegative weights `w`, the sum over the
non-diagonal tuples (whose coordinate moduli `q i P` are NOT pairwise coprime) is bounded by the
double sum over ordered pairs of distinct coordinates `(i,j)` of the pair-non-coprime restricted
sums. The first step of the y-space S1 off-diagonal size estimate: a `¬diag` tuple has some pair
`i ≠ j` sharing a prime (`> D₀` by the W-trick), and we union-bound over those pairs; each pair then
carries the singular-series `1/p²` factor (the next step). Proved by Aristotle (`c459c135`), verified
in-kernel + axiom-clean. -/
theorem offdiag_le_sum_pairs {k : ℕ} (T : Finset (Fin k → ℕ × ℕ))
    (q : Fin k → (Fin k → ℕ × ℕ) → ℕ) (w : (Fin k → ℕ × ℕ) → ℝ)
    (hw : ∀ P ∈ T, 0 ≤ w P) :
    ∑ P ∈ T.filter (fun P => ¬ ∀ i j : Fin k, i ≠ j → Nat.Coprime (q i P) (q j P)), w P
      ≤ ∑ i : Fin k, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
          ∑ P ∈ T.filter (fun P => ¬ Nat.Coprime (q i P) (q j P)), w P := by
  have h_lhs : ∑ P ∈ T with ¬∀ i j, i ≠ j → Nat.Coprime (q i P) (q j P), w P
      ≤ ∑ P ∈ T, ∑ i, ∑ j with j ≠ i,
          (if ¬Nat.Coprime (q i P) (q j P) then w P else 0) := by
    have h_lhs : ∀ P ∈ T, (¬∀ i j, i ≠ j → Nat.Coprime (q i P) (q j P)) →
        w P ≤ ∑ i, ∑ j with j ≠ i, (if ¬Nat.Coprime (q i P) (q j P) then w P else 0) := by
      intro P hP hP'; simp_all +decide [Finset.sum_ite]
      obtain ⟨i, j, hij, h⟩ := hP'
      refine' le_trans _ (Finset.single_le_sum
        (fun x _ => mul_nonneg (Nat.cast_nonneg _) (hw P hP)) (Finset.mem_univ i))
      simp +decide [*, Finset.filter_ne']
      exact le_mul_of_one_le_left (hw P hP) (mod_cast Finset.card_pos.mpr ⟨j, by aesop⟩)
    exact le_trans (Finset.sum_le_sum fun P hP =>
        h_lhs P (Finset.mem_filter.mp hP |>.1) (Finset.mem_filter.mp hP |>.2))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
          split_ifs <;> linarith [hw _ ‹_›])
  convert h_lhs using 1
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro i hi; rw [Finset.sum_comm]; simp +decide [Finset.sum_ite]

/-- **Shared-prime union bound for one coordinate pair.** Given a finite prime cover `Ps` such that
every `¬coprime` tuple of the pair `(i,j)` has a shared prime in `Ps` (`hcover`), the pair-restricted
nonnegative-weight sum is bounded by the sum over `p ∈ Ps` of the "both `i,j` moduli divisible by `p`"
restricted sums. The second reduction of the y-space S1 off-diagonal estimate (after
`offdiag_le_sum_pairs`): each shared prime `p > D₀` (W-trick) then carries a `1/p²` singular-series
weight, and `∑_{p>D₀}1/p² → 0`. Pure `Finset` union bound. -/
theorem pair_offdiag_le_sum_primes {k : ℕ} (T : Finset (Fin k → ℕ × ℕ)) (i j : Fin k)
    (w : (Fin k → ℕ × ℕ) → ℝ) (hw : ∀ P ∈ T, 0 ≤ w P) (Ps : Finset ℕ)
    (hcover : ∀ P ∈ T, ¬ Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2) →
      ∃ p ∈ Ps, p ∣ Nat.lcm (P i).1 (P i).2 ∧ p ∣ Nat.lcm (P j).1 (P j).2) :
    ∑ P ∈ T.filter (fun P => ¬ Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)), w P
      ≤ ∑ p ∈ Ps, ∑ P ∈ T.filter
          (fun P => p ∣ Nat.lcm (P i).1 (P i).2 ∧ p ∣ Nat.lcm (P j).1 (P j).2), w P := by
  classical
  have key : ∑ P ∈ T.filter
        (fun P => ¬ Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)), w P
      ≤ ∑ P ∈ T, ∑ p ∈ Ps,
          (if p ∣ Nat.lcm (P i).1 (P i).2 ∧ p ∣ Nat.lcm (P j).1 (P j).2 then w P else 0) := by
    have hterm : ∀ P ∈ T,
        (¬ Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)) →
        w P ≤ ∑ p ∈ Ps,
          (if p ∣ Nat.lcm (P i).1 (P i).2 ∧ p ∣ Nat.lcm (P j).1 (P j).2 then w P else 0) := by
      intro P hP hnc
      obtain ⟨p, hpPs, hpa, hpb⟩ := hcover P hP hnc
      have hnn : ∀ q ∈ Ps, (0 : ℝ) ≤
          (if q ∣ Nat.lcm (P i).1 (P i).2 ∧ q ∣ Nat.lcm (P j).1 (P j).2 then w P else 0) := by
        intro q _
        by_cases hc : q ∣ Nat.lcm (P i).1 (P i).2 ∧ q ∣ Nat.lcm (P j).1 (P j).2
        · rw [if_pos hc]; exact hw P hP
        · rw [if_neg hc]
      have hsingle := Finset.single_le_sum hnn hpPs
      beta_reduce at hsingle
      rwa [if_pos ⟨hpa, hpb⟩] at hsingle
    refine le_trans (Finset.sum_le_sum fun P hP =>
        hterm P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro P _ _
    refine Finset.sum_nonneg (fun q _ => ?_)
    by_cases hc : q ∣ Nat.lcm (P i).1 (P i).2 ∧ q ∣ Nat.lcm (P j).1 (P j).2
    · rw [if_pos hc]; exact hw P ‹_›
    · rw [if_neg hc]
  refine le_trans key (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_filter]

/-- **Per-coordinate factorization of a filtered `piFinset` product-sum.** A sum of coordinate-product
weights `∏ l, g l (P l)` over the `piFinset`, restricted by a per-coordinate predicate
`∀ l, pred l (P l)`, factorizes as the product over coordinates of the per-coordinate restricted sums.
The multiplicative core of the y-space S1 off-diagonal estimate: after fixing a shared prime `p` at
the pair `(i,j)`, the restriction `p ∣ lcm(P i) ∧ p ∣ lcm(P j)` is per-coordinate, so the Selberg
mass factors into `(∑_{P_i : p|lcm} g_i)·(∑_{P_j : p|lcm} g_j)·∏_{l≠i,j} Q_l`. Proved by Aristotle
(`3de9feb2`), verified in-kernel + axiom-clean (`Finset.prod_sum` + `Finset.sum_bij`). -/
theorem piFinset_filter_prod_factor {k : ℕ} {α : Type*} [DecidableEq α] (s : Fin k → Finset α)
    (g : Fin k → α → ℝ) (pred : Fin k → α → Prop) [∀ l, DecidablePred (pred l)] :
    ∑ P ∈ (Fintype.piFinset s).filter (fun P => ∀ l, pred l (P l)), ∏ l : Fin k, g l (P l)
      = ∏ l : Fin k, ∑ d ∈ (s l).filter (pred l), g l d := by
  rw [Finset.prod_sum]
  refine Finset.sum_bij (fun P hP => fun l _ => P l) ?_ ?_ ?_ ?_ <;> simp +decide
  · exact fun a ha₁ ha₂ l => ⟨ha₁ l, ha₂ l⟩
  · simp +contextual [funext_iff]
  · exact fun b hb => ⟨fun l => b l (Finset.mem_univ l), ⟨fun l => hb l |>.1, fun l => hb l |>.2⟩, rfl⟩

end BoundedGaps.S1OffDiagSize
