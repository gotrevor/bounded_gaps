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

/-- **The per-prime local factor of the singular-series majorant — the `1/(p-1)` reindex identity.**
For a prime `p` not dividing `d` nor `e` (with `d,e ≥ 1`), the deterministic Selberg majorant
`G(a,e) := (a/φ(a))·(e/φ(e))/lcm(a,e)` satisfies `G(p·d, e) = (1/(p-1))·G(d,e)`. This is the
arithmetic core that makes the off-diagonal `p`-restricted mass a `1/(p-1)` fraction: under the
reindex `a = p·d` on `{a : p ∣ a}`, every term picks up exactly the factor `1/(p-1)`, because
`φ(p·d) = (p-1)·φ(d)` (Euler, `p` coprime to `d`) and `lcm(p·d, e) = p·lcm(d,e)` (`p` coprime to `e`),
and the `p` in the numerator `p·d/φ(p·d) = p·d/((p-1)φ(d))` cancels the `p` in `lcm(p·d,e)`.
**Fully elementary (PNT-free).** NB this controls the *majorant* `G`, not the actual weight
`|yLambda_d·yLambda_e|/lcm`: the per-prime *mass-fraction* bound for the genuine off-diagonal
correction additionally needs the smoothing estimate `|yLambda_d| ≲ (d/φ(d))/log R` (the Möbius-mean
cancellation, PNT-strength) — the `abs_yLambda_le_sharp` majorant alone is lossy by `(log)²` per
coordinate (it carries `∑μ²/φ ≈ log N` in place of the cancelling `∑μ(t)F/φ(t) ≈ 1/log R`). See
`PENDING_WORK.md` (lap-11 head). -/
theorem selberg_local_factor (p d e : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    ((p * d : ℕ) : ℝ) / ((p * d).totient : ℝ) * ((e : ℝ) / (e.totient : ℝ))
        / ((Nat.lcm (p * d) e : ℕ) : ℝ)
      = (1 / ((p : ℝ) - 1))
          * (((d : ℝ) / (d.totient : ℝ)) * ((e : ℝ) / (e.totient : ℝ))
              / ((Nat.lcm d e : ℕ) : ℝ)) := by
  have hcpd : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
  have hcpe : Nat.Coprime p e := (hp.coprime_iff_not_dvd).mpr hpe
  have htot : (p * d).totient = (p - 1) * d.totient := by
    rw [Nat.totient_mul hcpd, Nat.totient_prime hp]
  have hlcm : Nat.lcm (p * d) e = p * Nat.lcm d e := by
    have hg : Nat.gcd (p * d) e = Nat.gcd d e := hcpe.gcd_mul_left_cancel d
    unfold Nat.lcm
    rw [hg, Nat.mul_assoc, Nat.mul_div_assoc _ (Nat.gcd_dvd_left d e |>.mul_right e)]
  have hp2 : 2 ≤ p := hp.two_le
  have hφd : (0:ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφe : (0:ℝ) < (e.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr he
  have hlcmde : (0:ℝ) < ((Nat.lcm d e : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hpm1 : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  rw [htot, hlcm]
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  field_simp

/-- The deterministic Selberg singular-series majorant `G(a,e) = (a/φa)·(e/φe)/lcm(a,e)`. The sharp
coefficient bound `S1Correction.abs_yLambda_le_sharp` gives `|yLambda_a · yLambda_e|/lcm(a,e) ≤
(C·∑μ²/φ)²·G(a,e)`, so `G` is the deterministic upper envelope of the off-diagonal Selberg weight.
**NB (lap-11):** this majorant alone is lossy by `(log)²` per coordinate (it carries `∑μ²/φ ≈ log N`
where the truth is `1/log R`); the off-diagonal closure needs the smoothing bound — see the
`PENDING_WORK.md` lap-11 head. `G` + `reindex_bound` are the PNT-free combinatorial scaffold. -/
noncomputable def Gmaj (a e : ℕ) : ℝ :=
  (a : ℝ) / (a.totient : ℝ) * ((e : ℝ) / (e.totient : ℝ)) / ((Nat.lcm a e : ℕ) : ℝ)

theorem Gmaj_nonneg (a e : ℕ) : 0 ≤ Gmaj a e := by unfold Gmaj; positivity

/-- `selberg_local_factor` specialised to the named majorant `Gmaj`. -/
theorem Gmaj_local_factor (p d e : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    Gmaj (p * d) e = (1 / ((p : ℝ) - 1)) * Gmaj d e := by
  unfold Gmaj
  exact selberg_local_factor p d e hp hd he hpd hpe

/-- **The per-prime reindex bound for the singular-series majorant.** Over a squarefree,
divisor-closed Finset `R`, the `p∣d` part of the double majorant sum is a `1/(p-1)` fraction of the
whole:
`∑_{d∈R, p∣d} ∑_{e∈R, p∤e} G d e ≤ (1/(p-1)) · ∑_{d∈R} ∑_{e∈R, p∤e} G d e`.
Reindex the outer sum by `d ↦ d/p` on `{d∈R : p∣d}` (injective; image `⊆ R` by divisor-closure;
squarefreeness gives `p∤(d/p)`), where each term picks up the `1/(p-1)` factor via
`Gmaj_local_factor`/`selberg_local_factor`. **Fully PNT-free** (pure `Finset` combinatorics + the
elementary local factor). This is the multiplicative heart of the off-diagonal per-prime mass
fraction: combined with the symmetric `p∣e` part it gives `∑_{p∣lcm} G ≤ (κ/(p-1))·∑ G`, and the
`∑_{p>D₀}1/(p-1)²` tail (`recip_sq_tail_tendsto_zero`) then drives the off-diagonal `→ 0` for growing
`W`. (The genuine off-diagonal correction further needs the smoothing bound to control `G` vs the
actual weight — `PENDING_WORK.md` lap-11.) -/
theorem reindex_bound (R : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hRsf : ∀ a ∈ R, Squarefree a) (hR1 : ∀ a ∈ R, 1 ≤ a)
    (hRdc : ∀ a ∈ R, ∀ b, b ∣ a → 1 ≤ b → b ∈ R) :
    ∑ d ∈ R.filter (fun d => p ∣ d), ∑ e ∈ R.filter (fun e => ¬ p ∣ e), Gmaj d e
      ≤ (1 / ((p : ℝ) - 1))
          * ∑ d ∈ R, ∑ e ∈ R.filter (fun e => ¬ p ∣ e), Gmaj d e := by
  classical
  set inner : ℕ → ℝ := fun d => ∑ e ∈ R.filter (fun e => ¬ p ∣ e), Gmaj d e with hinner
  have hinner_nonneg : ∀ d, 0 ≤ inner d := fun d =>
    Finset.sum_nonneg (fun e _ => Gmaj_nonneg d e)
  have hpm1 : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hp1 : (0:ℝ) ≤ 1 / ((p:ℝ) - 1) := by positivity
  have hd'pos : ∀ d, d ∈ R → p ∣ d → 1 ≤ d / p := by
    intro d hdR hpdvd
    have hd1 : 1 ≤ d := hR1 d hdR
    rcases Nat.eq_zero_or_pos (d / p) with h | h
    · exfalso; have := Nat.mul_div_cancel' hpdvd; rw [h, Nat.mul_zero] at this; omega
    · exact h
  have hstep1 : ∑ d ∈ R.filter (fun d => p ∣ d), inner d
      = (1 / ((p:ℝ) - 1)) * ∑ d ∈ R.filter (fun d => p ∣ d), inner (d / p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_filter] at hd
    obtain ⟨hdR, hpdvd⟩ := hd
    have hdsf : Squarefree d := hRsf d hdR
    have hdeq : p * (d / p) = d := Nat.mul_div_cancel' hpdvd
    have hd'1 : 1 ≤ d / p := hd'pos d hdR hpdvd
    have hpd' : ¬ p ∣ (d / p) := by
      intro hdvd
      have hpp : p * p ∣ d := by rw [← hdeq]; exact Nat.mul_dvd_mul_left p hdvd
      exact hp.ne_one (Nat.isUnit_iff.mp (hdsf p hpp))
    simp only [hinner, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    have he1 : 1 ≤ e := hR1 e he.1
    calc Gmaj d e = Gmaj (p * (d/p)) e := by rw [hdeq]
      _ = (1/((p:ℝ)-1)) * Gmaj (d/p) e :=
          Gmaj_local_factor p (d/p) e hp hd'1 he1 hpd' he.2
  rw [hstep1]
  have himg : (R.filter (fun d => p ∣ d)).image (fun d => d / p) ⊆ R := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨d, ⟨hdR, hpdvd⟩, rfl⟩ := hy
    exact hRdc d hdR (d/p) (Nat.div_dvd_of_dvd hpdvd) (hd'pos d hdR hpdvd)
  have hinj : ∀ x ∈ R.filter (fun d => p ∣ d), ∀ y ∈ R.filter (fun d => p ∣ d),
      x / p = y / p → x = y := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    have : p * (a/p) = p * (b/p) := by rw [hab]
    rwa [Nat.mul_div_cancel' ha.2, Nat.mul_div_cancel' hb.2] at this
  have hmono : ∑ d ∈ R.filter (fun d => p ∣ d), inner (d / p) ≤ ∑ d ∈ R, inner d := by
    calc ∑ d ∈ R.filter (fun d => p ∣ d), inner (d / p)
        = ∑ y ∈ (R.filter (fun d => p ∣ d)).image (fun d => d / p), inner y :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ R, inner d :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun d _ _ => hinner_nonneg d)
  calc (1/((p:ℝ)-1)) * ∑ d ∈ R.filter (fun d => p ∣ d), inner (d / p)
      ≤ (1/((p:ℝ)-1)) * ∑ d ∈ R, inner d := mul_le_mul_of_nonneg_left hmono hp1
    _ = _ := rfl

/-- `Gmaj` is symmetric (`lcm` is commutative). -/
theorem Gmaj_symm (a e : ℕ) : Gmaj a e = Gmaj e a := by
  unfold Gmaj; rw [Nat.lcm_comm]; ring

/-- **The both-divisible per-term local factor:** `G(p·d, p·e) = (p/(p-1)²)·G(d,e)` for prime `p ∤ d,e`.
The companion to `selberg_local_factor` for the diagonal-in-`p` part (`p ∣ d ∧ p ∣ e`): both
coordinates contribute a `1/(p-1)` from `φ(p·) = (p-1)φ(·)`, while `lcm(p·d, p·e) = p·lcm(d,e)`
(`Nat.lcm_mul_left`) supplies only one `1/p`, leaving the net `p/(p-1)²`. Elementary, PNT-free. -/
theorem Gmaj_local_factor_both (p d e : ℕ) (hp : p.Prime) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    Gmaj (p * d) (p * e) = ((p:ℝ) / ((p:ℝ) - 1)^2) * Gmaj d e := by
  unfold Gmaj
  have hcpd : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
  have hcpe : Nat.Coprime p e := (hp.coprime_iff_not_dvd).mpr hpe
  have htotd : (p * d).totient = (p - 1) * d.totient := by
    rw [Nat.totient_mul hcpd, Nat.totient_prime hp]
  have htote : (p * e).totient = (p - 1) * e.totient := by
    rw [Nat.totient_mul hcpe, Nat.totient_prime hp]
  have hlcm : Nat.lcm (p * d) (p * e) = p * Nat.lcm d e := by rw [Nat.lcm_mul_left]
  have hp2 : 2 ≤ p := hp.two_le
  have hφd : (0:ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφe : (0:ℝ) < (e.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr he
  have hlcmde : (0:ℝ) < ((Nat.lcm d e : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hpm1 : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  rw [htotd, htote, hlcm]
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  field_simp

/-- **The both-divisible 2D reindex bound:** `∑_{d∈R,p∣d} ∑_{e∈R,p∣e} G d e ≤ (p/(p-1)²) ∑_R ∑_R G`.
The diagonal-in-`p` analogue of `reindex_bound`: reindex BOTH coordinates by `·/p` (the product map on
`{d:p∣d}×{e:p∣e}`, injective, image `⊆ R×R`), each term picking up the `p/(p-1)²` factor of
`Gmaj_local_factor_both`. Pure `Finset` combinatorics, PNT-free. -/
theorem reindex_bound_both (R : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hRsf : ∀ a ∈ R, Squarefree a) (hR1 : ∀ a ∈ R, 1 ≤ a)
    (hRdc : ∀ a ∈ R, ∀ b, b ∣ a → 1 ≤ b → b ∈ R) :
    ∑ d ∈ R.filter (fun d => p ∣ d), ∑ e ∈ R.filter (fun e => p ∣ e), Gmaj d e
      ≤ ((p:ℝ) / ((p:ℝ) - 1)^2) * ∑ d ∈ R, ∑ e ∈ R, Gmaj d e := by
  classical
  set Rp := R.filter (fun d => p ∣ d) with hRp
  have hpm1 : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hcoef : (0:ℝ) ≤ (p:ℝ) / ((p:ℝ) - 1)^2 := by positivity
  have hd'pos : ∀ d, d ∈ R → p ∣ d → 1 ≤ d / p := by
    intro d hdR hpdvd
    have hd1 : 1 ≤ d := hR1 d hdR
    rcases Nat.eq_zero_or_pos (d / p) with h | h
    · exfalso; have := Nat.mul_div_cancel' hpdvd; rw [h, Nat.mul_zero] at this; omega
    · exact h
  have hpd' : ∀ d, d ∈ R → p ∣ d → ¬ p ∣ (d / p) := by
    intro d hdR hpdvd hdvd
    have hdeq : p * (d / p) = d := Nat.mul_div_cancel' hpdvd
    have hpp : p * p ∣ d := by rw [← hdeq]; exact Nat.mul_dvd_mul_left p hdvd
    exact hp.ne_one (Nat.isUnit_iff.mp ((hRsf d hdR) p hpp))
  have hstep1 : ∑ d ∈ Rp, ∑ e ∈ Rp, Gmaj d e
      = ((p:ℝ)/((p:ℝ)-1)^2) * ∑ d ∈ Rp, ∑ e ∈ Rp, Gmaj (d/p) (e/p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mul_sum]
    rw [hRp, Finset.mem_filter] at hd
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [hRp, Finset.mem_filter] at he
    have hdeq : p * (d/p) = d := Nat.mul_div_cancel' hd.2
    have heeq : p * (e/p) = e := Nat.mul_div_cancel' he.2
    calc Gmaj d e = Gmaj (p*(d/p)) (p*(e/p)) := by rw [hdeq, heeq]
      _ = ((p:ℝ)/((p:ℝ)-1)^2) * Gmaj (d/p) (e/p) :=
          Gmaj_local_factor_both p (d/p) (e/p) hp (hd'pos d hd.1 hd.2) (hd'pos e he.1 he.2)
            (hpd' d hd.1 hd.2) (hpd' e he.1 he.2)
  rw [hstep1]
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  have hinj : ∀ x ∈ Rp, ∀ y ∈ Rp, x / p = y / p → x = y := by
    intro a ha b hb hab
    rw [hRp, Finset.mem_filter] at ha hb
    have : p * (a/p) = p * (b/p) := by rw [hab]
    rwa [Nat.mul_div_cancel' ha.2, Nat.mul_div_cancel' hb.2] at this
  have himg : Rp.image (fun d => d / p) ⊆ R := by
    intro y hy
    simp only [Finset.mem_image, hRp, Finset.mem_filter] at hy
    obtain ⟨d, ⟨hdR, hpdvd⟩, rfl⟩ := hy
    exact hRdc d hdR (d/p) (Nat.div_dvd_of_dvd hpdvd) (hd'pos d hdR hpdvd)
  calc ∑ d ∈ Rp, ∑ e ∈ Rp, Gmaj (d/p) (e/p)
      = ∑ d' ∈ Rp.image (fun d => d/p), ∑ e' ∈ Rp.image (fun e => e/p), Gmaj d' e' := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.sum_image hinj]
    _ ≤ ∑ d' ∈ Rp.image (fun d => d/p), ∑ e' ∈ R, Gmaj d' e' := by
        refine Finset.sum_le_sum (fun d' _ => ?_)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun e' _ _ => Gmaj_nonneg d' e')
    _ ≤ ∑ d' ∈ R, ∑ e' ∈ R, Gmaj d' e' :=
        Finset.sum_le_sum_of_subset_of_nonneg himg
          (fun d' _ _ => Finset.sum_nonneg (fun e' _ => Gmaj_nonneg d' e'))

end BoundedGaps.S1OffDiagSize
