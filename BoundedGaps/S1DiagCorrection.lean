/-
# The DIAGONAL leg of the y-space S1 correction is `o(B^{+k}·M)` — PNT-FREE (Leg 1, instantiated)

This file wires together the abstract, machine-checked pieces built across laps 7–9 into the
concrete conclusion the lap-9 handoff identified as "the satisfying milestone":

  **the diagonal half of the s1 off-diagonal correction `hcorr` tends to `0` in the `B^{+k}·M`
  normalisation — with NO PNT, NO Möbius cancellation — by decoupling the sieve scale `x` from the
  level `N`.**

## The decoupling (`PENDING_WORK.md`, memory `[[hcorr-diag-pntfree-offdiag-growing-w]]`)
The full s1 correction (`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`) splits,
after restricting to the divisor-closed candidate set `Rset`, into a **diagonal** leg (cross-coprime
moduli, count error `≤ 1`, NO `M` factor) and an **off-diagonal** leg (the W-trick vanishing density
mass that scales with `M`). The diagonal leg's weight is bounded by a **fixed polynomial in the
level `N`, independent of the sieve scale `x`** (`S1Correction.diag_weight_yLambda_le_poly`:
`∑_{diag}|∏λλ| ≤ ((C·N³)²)^k = C^{2k}·N^{6k}`), because the `F`-support cutoff kills every divisor
`> N` (`S1Correction.sum_abs_yLambda_le_level`). The main-term chain takes the scale `x` as a free
parameter, so taking `x = x(N)` polynomially large forces the lattice density
`M(N) = (⌊2x⌋−(⌈x⌉−1))/W ≥ N^{6k+1}`, and then the diagonal ratio
`C^{2k}·N^{6k} / ((φW/W)^k·(log N)^k·M(N)) → 0` (`S1DiagonalSize.diag_ratio_tendsto_zero`).

`diagCorr` packages the diagonal-restricted y-space correction sum; `abs_diagCorr_le` is its
PNT-free polynomial bound; `diag_correction_ratio_tendsto_zero` is the limit. The diagonal count
error `≤ 1` is discharged in-kernel (`S1Correction.yspace_diag_count_err`, CRT, no BV — needs only
the candidate-set coprimality, NOT the W-trick admissibility). This discharges the diagonal HALF of
`hcorr`. (The off-diagonal half — where `M` cancels against the main term so the scale trick is
useless — is the genuine remaining nut; it needs a *growing* modulus `W = W(N)`, see `S1OffDiagSize`
and the lap-9 `PENDING_WORK.md`.)
-/
import BoundedGaps.S1Correction
import BoundedGaps.S1DiagonalSize
import BoundedGaps.S1CandidateSet

open Filter Topology
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1DiagCorrection

/-- **The diagonal-restricted y-space S1 correction sum.** Over the squarefree `W`-coprime candidate
sets `Rset_i = (sieveDivisors_i).filter(sf ∧ (·,W)=1)`, restricted to the *diagonal* tuples `P`
(pairwise-coprime moduli `lcm(P i)` across coordinates), the weighted count error
`∑_{P : diag} (∏ᵢ yLambda·yLambda)·(count_P − M/∏[dᵢ,eᵢ])`. Here `x` is the sieve scale, `L` the
y-space level (`= log N`), `M` the lattice density. Packaging this as a `def` keeps the limit goal
small (the scale-trick engine sees an opaque numerator). -/
noncomputable def diagCorr {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (b W : ℕ) (x L M : ℝ) : ℝ :=
  ∑ P ∈ (Fintype.piFinset (fun i : Fin k =>
        ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W))
          ×ˢ ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)))).filter
        (fun P => ∀ i j : Fin k, i ≠ j →
          Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)),
      (∏ i : Fin k,
        S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).1
          * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) L (P i).2)
      * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
            (fun m => ∀ i : Fin k,
              (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
          - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))

/-- **The diagonal correction is bounded by a fixed polynomial in the level `N`, x-independent.**
At the exact lattice density `M = (⌊2x⌋−(⌈x⌉−1))/W`, with `|Fs i| ≤ C` and `Fs i` cut off above `1`,
`|diagCorr| ≤ ((C·N³)²)^k`. The diagonal count error `≤ 1` is discharged via
`S1Correction.yspace_diag_count_err` (CRT, unconditional — only the candidate-set coprimality is
needed); the weight by `S1Correction.diag_weight_yLambda_le_poly` (PNT-free). -/
theorem abs_diagCorr_le {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (b W : ℕ) (x : ℝ) (N : ℕ) (C : ℝ)
    (hx : 0 < x) (hW : 0 < W) (hN : 2 ≤ N) (hAB : ⌈x⌉₊ - 1 ≤ ⌊2 * x⌋₊)
    (hC : ∀ i, ∀ t, |Fs i t| ≤ C) (hFcut : ∀ i, ∀ t, 1 < t → Fs i t = 0) :
    |diagCorr Fs H b W x (Real.log (N : ℝ))
        (((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))|
      ≤ ((C * (N : ℝ) ^ 3) ^ 2) ^ k := by
  unfold diagCorr
  refine le_trans (S1Correction.abs_diag_correction_le_diag_weight
      (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W))
      (fun i => S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log (N : ℝ)))
      (fun P => ∀ i j : Fin k, i ≠ j →
        Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2))
      (fun P => ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
            (fun m => ∀ i : Fin k,
              (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
          - ((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)
              / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      ?_) ?_
  · -- `herr`: the per-diagonal count error is `≤ 1` (CRT, unconditional)
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPmem, hdiagP⟩ := hP
    have hmem := Fintype.mem_piFinset.mp hPmem
    have hpos : ∀ i, 0 < Nat.lcm (P i).1 (P i).2 := by
      intro i
      have h2 := Finset.mem_product.mp (hmem i)
      have h1a : 1 ≤ (P i).1 :=
        (BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x).1 (P i).1 h2.1
      have h1b : 1 ≤ (P i).2 :=
        (BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x).1 (P i).2 h2.2
      exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have hcopW : ∀ i, Nat.Coprime (Nat.lcm (P i).1 (P i).2) W := by
      intro i
      have h2 := Finset.mem_product.mp (hmem i)
      have hc1 := (Finset.mem_filter.mp h2.1).2.2
      have hc2 := (Finset.mem_filter.mp h2.2).2.2
      exact S1Correction.coprime_lcm_of_coprime hc1 hc2
    exact S1Correction.yspace_diag_count_err k H b W x hx hW hAB P hpos hcopW hdiagP
  · -- the diagonal weight ≤ the fixed polynomial `((C·N³)²)^k`
    exact S1Correction.diag_weight_yLambda_le_poly Fs
      (fun i => (BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) N C hN hC hFcut
      (fun i => (BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x).1)
      (fun P => ∀ i j : Fin k, i ≠ j →
        Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2))

/-- **The diagonal leg of the s1 correction is `o(B^{+k}·M)` — PNT-free (Leg 1).** With a sieve scale
`x = x(N)` decoupled from the level `N` and taken polynomially large
(`hgrow : eventually N^{6k+1} ≤ (⌊2x⌋−(⌈x⌉−1))/W`), the diagonal-restricted y-space correction
`diagCorr` (at the exact lattice density `M = (⌊2x⌋−(⌈x⌉−1))/W`), normalised by the y-space main term
`B^{+k}·M = sieveB W N ^ k · M`, tends to `0`.

The count error `|count_P − M/∏[dᵢ,eᵢ]| ≤ 1` is discharged unconditionally (CRT,
`abs_diagCorr_le`); the diagonal weight is bounded by `((C·N³)²)^k = C^{2k}·N^{6k}` (PNT-free,
x-independent); the ratio limit is `S1DiagonalSize.diag_ratio_tendsto_zero` with `K = C^{2k}`,
`p = 6k`, `c = (φW/W)^k`. **No PNT, no Möbius cancellation.** This is the PNT-free diagonal HALF of
`hcorr`. (The off-diagonal half, where `M` cancels against the main term, needs a growing modulus.) -/
theorem diag_correction_ratio_tendsto_zero {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (C : ℝ) (hW : 0 < W)
    (hC : ∀ i, ∀ t, |Fs i t| ≤ C) (hFcut : ∀ i, ∀ t, 1 < t → Fs i t = 0)
    (x : ℕ → ℝ) (hcov : ∀ N : ℕ, (W * N : ℝ) + 2 ≤ x N)
    (hgrow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (6 * k + 1)
        ≤ ((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)) :
    Tendsto (fun N : ℕ =>
        diagCorr Fs H b W (x N) (Real.log (N : ℝ))
            (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
          / (Sieve.sieveB W (N : ℝ) ^ k
              * (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))))
      atTop (nhds 0) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hφ : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW
  have hc : (0 : ℝ) < ((W.totient : ℝ) / W) ^ k := pow_pos (div_pos hφ hWr) k
  have hden : ∀ N : ℕ, Sieve.sieveB W (N : ℝ) ^ k
      = ((W.totient : ℝ) / W) ^ k * (Real.log N) ^ k := by
    intro N; rw [Sieve.sieveB, mul_pow]
  simp only [hden]
  apply S1DiagonalSize.diag_ratio_tendsto_zero ((C ^ 2) ^ k) (((W.totient : ℝ) / W) ^ k)
    (6 * k) k hc (by positivity)
  · -- `|diagCorr| ≤ C^{2k}·N^{6k}`, eventually
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hxN : 0 < x N := by
      have h0 : (0 : ℝ) ≤ (W : ℝ) * (N : ℝ) := by positivity
      have hcN := hcov N
      push_cast at hcN
      linarith
    have hAB : ⌈x N⌉₊ - 1 ≤ ⌊2 * x N⌋₊ := by
      have := (S1CandidateSet.sieve_interval_covers (x N) W N (hcov N)).1
      omega
    have hCeq : ((C * (N : ℝ) ^ 3) ^ 2) ^ k = (C ^ 2) ^ k * (N : ℝ) ^ (6 * k) := by
      have h1 : (C * (N : ℝ) ^ 3) ^ 2 = C ^ 2 * (N : ℝ) ^ 6 := by ring
      rw [h1, mul_pow]
      congr 1
      exact (pow_mul (N : ℝ) 6 k).symm
    calc |diagCorr Fs H b W (x N) (Real.log (N : ℝ))
            (((⌊2 * x N⌋₊ : ℝ) - ((⌈x N⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))|
        ≤ ((C * (N : ℝ) ^ 3) ^ 2) ^ k :=
          abs_diagCorr_le Fs H b W (x N) N C hxN hW hN hAB hC hFcut
      _ = (C ^ 2) ^ k * (N : ℝ) ^ (6 * k) := hCeq
  · -- the scale dominates `N^{6k+1}` eventually
    exact hgrow

end BoundedGaps.S1DiagCorrection
