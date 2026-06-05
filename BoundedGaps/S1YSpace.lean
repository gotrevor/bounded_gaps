/-
# Path-Y (y_r-space) `s1` main term — the contour-free assembly

The explicit y-space Selberg quadratic form, with the inversion-defined coefficient
`λ_d = d·∑_{s∈R_N, d∣s} μ(s/d)·F(log s/log N)/φ(s)` over the sieve index set
`R_N = {r ≤ N : Squarefree r ∧ (r,W)=1}`, has the **contour-free** asymptotic

    (∑_{d,e∈R_N} λ_d λ_e / [d,e]) / log N  →  (φ(W)/W)·∫₀¹ F²    (as N → ∞).

This composes `SieveExpansion.gpy_diagonalize_yform_muphi` (the algebraic diagonalisation:
`∑ λλ/[d,e] = ∑_{r∈R_N}(μ²/φ)F²`, via Möbius inversion over multiples) with
`WeightedMertens.yspace_muphi_diagonal_tendsto` (the limit of the diagonal sum). It is the
`s1` main term in Maynard's `y_r`-space — the convention under which the constant genuinely IS
`∫F²` (= `mkF_denominator` at `k=1`) and the proof uses NO PNT / contour (unlike the `d`-space
`selberg_nu`; see `PENDING_WORK.md` and memory `s1-derivative-landmine`). Conditional only on the
W-coprime sharp Mertens base `hBaseW` (Aristotle brick `65d11d89`).
-/
import BoundedGaps.SieveExpansion
import BoundedGaps.WeightedMertens

open scoped BigOperators
open Filter Topology
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1YSpace

/-- The y-space sieve coefficient `λ_d = d·∑_{s∈R, d∣s} μ(s/d)·F(log s/L)/φ(s)`. -/
noncomputable def yLambda (R : Finset ℕ) (F : ℝ → ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * ∑ s ∈ R.filter (fun s => d ∣ s),
    (moebius (s / d) : ℝ) * (F (Real.log s / L) / (Nat.totient s : ℝ))

/-- **The explicit y-space Selberg quadratic form → `(φ(W)/W)·∫F²`, contour-free.**
With `R_N = {r ≤ N : Squarefree r ∧ (r,W)=1}` and `λ` the inversion coefficient `yLambda R_N F (log N)`,
`(∑_{d,e∈R_N} λ_d λ_e / [d,e]) / log N → (φ(W)/W)·∫₀¹F²`. The 1-D Path-Y `s1` main term in the form
the sieve produces it, proved with no PNT-strength input. Conditional only on the W-coprime sharp
Mertens base `hBaseW`. -/
theorem yspace_sieve_quadform_tendsto {W : ℕ} {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N)
      atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto
      (fun N : ℕ =>
        (∑ d ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
          ∑ e ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
            yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
                F (Real.log N) d
              * yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
                F (Real.log N) e
              / (Nat.lcm d e : ℝ)) / Real.log N)
      atTop (nhds ((W.totient : ℝ) / W * ∫ u in (0 : ℝ)..1, F u ^ 2)) := by
  have hlim := BoundedGaps.WeightedMertens.yspace_muphi_diagonal_tendsto (W := W) (F := F) hF hBaseW
  refine hlim.congr (fun N => ?_)
  congr 1
  obtain ⟨h0, hsf, hdc⟩ := BoundedGaps.Sieve.sieveR_yspace_hyps N W
  rw [← BoundedGaps.Sieve.gpy_diagonalize_yform_muphi
    ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W)) h0 hsf hdc F (Real.log N)]
  rfl

/-- **The explicit y-space Selberg quadratic CROSS form → `(φ(W)/W)·∫F₁F₂`, contour-free.**
The `j≠j'` analog of `yspace_sieve_quadform_tendsto` — the cross-term `s1` block. With the two
inversion coefficients `yLambda R_N F₁ (log N)`, `yLambda R_N F₂ (log N)`,
`(∑_{d,e∈R_N} λ^{(1)}_d λ^{(2)}_e/[d,e])/log N → (φ(W)/W)·∫₀¹F₁F₂`. Composes
`SieveExpansion.gpy_diagonalize_yform_muphi_bilinear` with `WeightedMertens.yspace_muphi_bilinear_tendsto`.
With `yspace_sieve_quadform_tendsto` this covers every block of the general
`ν = (∑_j c_j ∏_i λ_{F_{j,i}})²` after opening the square. Conditional only on `hBaseW`. -/
theorem yspace_sieve_quadform_bilinear_tendsto {W : ℕ} {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ContDiff ℝ 1 F₁) (hF₂ : ContDiff ℝ 1 F₂)
    (hBaseW : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime W n)
        / Real.log N)
      atTop (nhds ((W.totient : ℝ) / W))) :
    Tendsto
      (fun N : ℕ =>
        (∑ d ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
          ∑ e ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
            yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
                F₁ (Real.log N) d
              * yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
                F₂ (Real.log N) e
              / (Nat.lcm d e : ℝ)) / Real.log N)
      atTop (nhds ((W.totient : ℝ) / W * ∫ u in (0 : ℝ)..1, F₁ u * F₂ u)) := by
  have hlim := BoundedGaps.WeightedMertens.yspace_muphi_bilinear_tendsto
    (W := W) (F₁ := F₁) (F₂ := F₂) hF₁ hF₂ hBaseW
  refine hlim.congr (fun N => ?_)
  congr 1
  obtain ⟨h0, hsf, hdc⟩ := BoundedGaps.Sieve.sieveR_yspace_hyps N W
  rw [← BoundedGaps.Sieve.gpy_diagonalize_yform_muphi_bilinear
    ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W)) h0 hsf hdc
    F₁ F₂ (Real.log N)]
  rfl

/-- The `W = 1` base density `(∑_{n≤N} g_1)/log N → 1` IS `sharp_mertens_unconditional`
(`g_1 = μ²/φ` since `(n,1)=1` always; `φ(1)/1 = 1`). So the whole y-space chain is UNCONDITIONAL
at `W = 1` (singular series `𝔖 = 1`). -/
theorem base_one :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, BoundedGaps.WeightedMertens.gMuSqTotientCoprime 1 n)
        / Real.log N) atTop (nhds (((1 : ℕ).totient : ℝ) / ((1 : ℕ) : ℝ))) := by
  have ht : (((1 : ℕ).totient : ℝ) / ((1 : ℕ) : ℝ)) = 1 := by norm_num
  rw [ht]
  have heq : ∀ n, BoundedGaps.WeightedMertens.gMuSqTotientCoprime 1 n
      = BoundedGaps.SingularSeries.gMoebiusSqTotient n := by
    intro n
    unfold BoundedGaps.WeightedMertens.gMuSqTotientCoprime
    rw [if_pos (Nat.coprime_one_right n)]
  simp only [heq]
  exact BoundedGaps.SharpMertens.sharp_mertens_unconditional

/-- **UNCONDITIONAL contour-free Path-Y `s1` main term (`𝔖 = 1`).** At `W = 1` the W-coprime base
is `sharp_mertens_unconditional`, so the y-space Selberg quadratic form converges with NO hypotheses
beyond `ContDiff ℝ 1 F`:
`(∑_{d,e ≤ N, sf} λ_d λ_e/[d,e])/log N → ∫₀¹F²`, `λ_d = yLambda {r≤N sf} F (log N) d`. The first
**fully unconditional** contour-free `s1`-main-term-shaped result — the entire chain (Möbius
inversion → diagonalisation → sharp Mertens) is machine-checked end-to-end, axiom-clean, no PNT. -/
theorem yspace_sieve_quadform_tendsto_one {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Tendsto
      (fun N : ℕ =>
        (∑ d ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r 1),
          ∑ e ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r 1),
            yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r 1))
                F (Real.log N) d
              * yLambda ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r 1))
                F (Real.log N) e
              / (Nat.lcm d e : ℝ)) / Real.log N)
      atTop (nhds (∫ u in (0 : ℝ)..1, F u ^ 2)) := by
  have h := yspace_sieve_quadform_tendsto (W := 1) (F := F) hF base_one
  simpa using h

/-- **The (separable) y-space Selberg sieve weight.** `ν(n) = (∏ᵢ ∑_{d∣n+hᵢ} λ_{d,i})²` with the
inversion-defined coefficient `λ_{d,i} = yLambda (Rset i) (Fs i) (log R) d`. The contour-free
analog of `Sieve.selberg_nu_separable` (which uses `lambdaTransform`, the PNT-gated `d`-space). -/
noncomputable def selberg_nu_yr_sep (k : ℕ) (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ)
    (Rset : Fin k → Finset ℕ) (n : ℕ) : ℝ :=
  (∏ i : Fin k, ∑ d ∈ (n + H.getD i.val 0).divisors,
    yLambda (Rset i) (Fs i) (Real.log R) d) ^ 2

/-- The y-space weight is non-negative (a square), matching the Selberg requirement `ν ≥ 0`. -/
theorem selberg_nu_yr_sep_nonneg (k : ℕ) (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ)
    (Rset : Fin k → Finset ℕ) (n : ℕ) : 0 ≤ selberg_nu_yr_sep k Fs H R Rset n :=
  sq_nonneg _

/-- **Expansion of the y-space sieve sum** (instance of `sieveSum_genProd_sq_expand`).
`sieveSum (selberg_nu_yr_sep …) = ∑_P (∏ᵢ λ_{(P i).1,i}·λ_{(P i).2,i})·count(P)`. The structural
bridge from the y-space `sieveSum` to the bilinear `∑λλ` form; composing with `lattice_count_main_term`
(count → `M/∏[dᵢ,eᵢ]`, shared with the `d`-space) and `gpy_diagonalize_yform_muphi` lands the
contour-free main term `M·∑_{r}(μ²/φ)F²` → `yspace_..._tendsto`. -/
theorem sieveSum_selberg_nu_yr_sep_expand (k : ℕ) (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ)
    (Rset : Fin k → Finset ℕ) (b W : ℕ) (x : ℝ) (hx : 0 < x) :
    BoundedGaps.Sieve.sieveSum (selberg_nu_yr_sep k Fs H R Rset) b W x
      = ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            BoundedGaps.Sieve.sieveDivisors H i.val b W x
              ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
          (∏ i : Fin k, yLambda (Rset i) (Fs i) (Real.log R) (P i).1
            * yLambda (Rset i) (Fs i) (Real.log R) (P i).2)
          * (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card := by
  rw [BoundedGaps.Sieve.sieveSum]
  exact BoundedGaps.Sieve.sieveSum_genProd_sq_expand k
    (fun i => yLambda (Rset i) (Fs i) (Real.log R)) H b W x hx

/-- **`yLambda` vanishes off a divisor-closed set.** If `R` is divisor-closed and `d ∉ R`, then
`yLambda R F L d = 0` (the inner filter `{s∈R : d∣s}` is empty: `d∣s∈R ⟹ d∈R`). The algebraic
key to the candidate-set reconciliation — `yLambda` is supported on `R`. -/
theorem yLambda_eq_zero_of_not_mem (R : Finset ℕ) (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R)
    (F : ℝ → ℝ) (L : ℝ) {d : ℕ} (hd : d ∉ R) : yLambda R F L d = 0 := by
  unfold yLambda
  have hempty : R.filter (fun s => d ∣ s) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro s hs hds
    exact hd (hRdc s hs d hds)
  rw [hempty, Finset.sum_empty, mul_zero]

/-- **Sum-over-superset reduction.** For `R ⊆ T` with `R` divisor-closed,
`∑_{d∈T} yLambda R F L d · g d = ∑_{d∈R} yLambda R F L d · g d` (the `T∖R` terms vanish by
`yLambda_eq_zero_of_not_mem`). Lets the sieve expansion's `∑_{d∈sieveDivisors}` collapse to the
diagonalisation index set `R = sieveDivisors.filter(sf ∧ coprime)`. -/
theorem sum_yLambda_eq_of_subset (R T : Finset ℕ) (hRT : R ⊆ T)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R) (F : ℝ → ℝ) (L : ℝ) (g : ℕ → ℝ) :
    ∑ d ∈ T, yLambda R F L d * g d = ∑ d ∈ R, yLambda R F L d * g d := by
  rw [← Finset.sum_subset hRT]
  intro d _ hdR
  rw [yLambda_eq_zero_of_not_mem R hRdc F L hdR, zero_mul]

end BoundedGaps.S1YSpace
