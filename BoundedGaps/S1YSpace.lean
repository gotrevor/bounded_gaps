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

/-- **y-space `sieveSum = heuristic main + correction`** (pure algebra; `M` = any chosen lattice
main density). Splits `count = M/∏[dᵢ,eᵢ] + (count − M/∏[dᵢ,eᵢ])` termwise on
`sieveSum_selberg_nu_yr_sep_expand`. The heuristic main `∑_P(∏λλ)·M/∏[dᵢ,eᵢ]` factors over
coordinates (`piFinset`) to `M·∏ᵢ ∑_{d,e}λλ/[d,e]` → `gpy_diagonalize_yform_muphi` → the contour-free
`(φ(W)/W)∫F²`; the correction `∑_P(∏λλ)·(count − M/∏[dᵢ,eᵢ])` is the BV-gated `o(main)` obligation
(gap C, shared with the d-space `sieveSum_selberg_nu_eq_heuristic_add_correction`). -/
theorem sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction
    (k : ℕ) (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (Rset : Fin k → Finset ℕ)
    (b W : ℕ) (x : ℝ) (hx : 0 < x) (M : ℝ) :
    BoundedGaps.Sieve.sieveSum (selberg_nu_yr_sep k Fs H R Rset) b W x
      = (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            BoundedGaps.Sieve.sieveDivisors H i.val b W x
              ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
          (∏ i : Fin k, yLambda (Rset i) (Fs i) (Real.log R) (P i).1
            * yLambda (Rset i) (Fs i) (Real.log R) (P i).2)
          * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      + (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            BoundedGaps.Sieve.sieveDivisors H i.val b W x
              ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
          (∏ i : Fin k, yLambda (Rset i) (Fs i) (Real.log R) (P i).1
            * yLambda (Rset i) (Fs i) (Real.log R) (P i).2)
          * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                (fun m => ∀ i : Fin k,
                  (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
              - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))) := by
  rw [sieveSum_selberg_nu_yr_sep_expand k Fs H R Rset b W x hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- **Bilinear sum-over-superset reduction.** For `R ⊆ T` with `R` divisor-closed,
`∑_{d,e∈T} λ_d(λ_e·h d e) = ∑_{d,e∈R} λ_d(λ_e·h d e)` (`λ = yLambda R F L`; both the `d`- and
`e`-sums collapse to `R` by `yLambda_eq_zero_of_not_mem`). Restricts the sieve bilinear form from
the candidate set to the diagonalisation index. -/
theorem sum_yLambda_bilinear_eq_of_subset (R T : Finset ℕ) (hRT : R ⊆ T)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R) (F : ℝ → ℝ) (L : ℝ) (h : ℕ → ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, yLambda R F L d * (yLambda R F L e * h d e))
      = ∑ d ∈ R, ∑ e ∈ R, yLambda R F L d * (yLambda R F L e * h d e) := by
  rw [show (∑ d ∈ T, ∑ e ∈ T, yLambda R F L d * (yLambda R F L e * h d e))
        = ∑ d ∈ T, yLambda R F L d * (∑ e ∈ T, yLambda R F L e * h d e) from
        Finset.sum_congr rfl (fun d _ => (Finset.mul_sum _ _ _).symm)]
  rw [sum_yLambda_eq_of_subset R T hRT hRdc F L
    (fun d => ∑ e ∈ T, yLambda R F L e * h d e)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [sum_yLambda_eq_of_subset R T hRT hRdc F L (fun e => h d e), Finset.mul_sum]

/-- **Per-coordinate y-space factor = `∑_{r∈Rset}(μ²/φ)F²`.** Over `Rset =
`sieveDivisors.filter(sf ∧ coprime W)` (divisor-closed by `sieveDivisors_yspace_hyps`), the
bilinear y-space form is the diagonalised `μ²/φ` sum — a direct restatement of
`gpy_diagonalize_yform_muphi`. With `piFinset_lattice_main_factor` + `sum_yLambda_bilinear_eq_of_subset`
(to drop `sieveDivisors∖Rset`) this is the per-coordinate factor of the y-space heuristic main term,
`→ (φ(W)/W)∫F²` via `yspace_muphi_diagonal_tendsto`. -/
theorem yr_coord_factor_eq_muphi (H : List ℕ) (i b W : ℕ) (x : ℝ) (F : ℝ → ℝ) (R : ℝ) :
    (∑ d ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
       ∑ e ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
        yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) d
          * yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) e
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / Real.log R) ^ 2 := by
  set Rset := (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
      (fun r => Squarefree r ∧ Nat.Coprime r W) with hRset
  obtain ⟨h0, hsf, hdc⟩ := BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i b W x
  rw [← BoundedGaps.Sieve.gpy_diagonalize_yform_muphi Rset h0 hsf hdc F (Real.log R)]
  rfl

/-- **Product-set per-coord factor.** Over `sieveDivisors² ` (the form `piFinset_lattice_main_factor`
produces), the y-space bilinear factor `= ∑_{r∈Rset}(μ²/φ)F²` (`Rset = sieveDivisors.filter(sf∧coprime)`):
`Finset.sum_product` + `sum_yLambda_bilinear_eq_of_subset` (drop `∖Rset`) + `yr_coord_factor_eq_muphi`. -/
theorem yr_coord_sieveDiv_factor (H : List ℕ) (i b W : ℕ) (x : ℝ) (F : ℝ → ℝ) (R : ℝ) :
    (∑ de ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x
          ×ˢ BoundedGaps.Sieve.sieveDivisors H i b W x),
        yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) de.1
          * yLambda ((BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)) F (Real.log R) de.2
          / (Nat.lcm de.1 de.2 : ℝ))
      = ∑ r ∈ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / Real.log R) ^ 2 := by
  set Rset := (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
      (fun r => Squarefree r ∧ Nat.Coprime r W) with hRset
  obtain ⟨h0, hsf, hdc⟩ := BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i b W x
  have hsub : Rset ⊆ BoundedGaps.Sieve.sieveDivisors H i b W x := Finset.filter_subset _ _
  rw [Finset.sum_product]
  rw [show (∑ d ∈ BoundedGaps.Sieve.sieveDivisors H i b W x,
        ∑ e ∈ BoundedGaps.Sieve.sieveDivisors H i b W x,
          yLambda Rset F (Real.log R) d * yLambda Rset F (Real.log R) e / (Nat.lcm d e : ℝ))
      = ∑ d ∈ BoundedGaps.Sieve.sieveDivisors H i b W x,
          ∑ e ∈ BoundedGaps.Sieve.sieveDivisors H i b W x,
            yLambda Rset F (Real.log R) d
              * (yLambda Rset F (Real.log R) e * (1 / (Nat.lcm d e : ℝ))) from by
        refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => by ring))]
  rw [sum_yLambda_bilinear_eq_of_subset Rset (BoundedGaps.Sieve.sieveDivisors H i b W x) hsub hdc
    F (Real.log R) (fun d e => 1 / (Nat.lcm d e : ℝ))]
  rw [← yr_coord_factor_eq_muphi H i b W x F R]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => by ring))


/-- **The y-space heuristic main term IS `M·∏ᵢ∑_{r}(μ²/φ)Fᵢ²`** — fully diagonalised, contour-free.
The heuristic main of `sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction` (with
`Rset i = sieveDivisors_i.filter(sf∧coprime W)`) reduces, via `piFinset_lattice_main_factor`
(coeff-general factoring over coordinates) + `yr_coord_sieveDiv_factor` per coordinate, to
`M·∏ᵢ ∑_{r≤level, sf, (r,W)=1}(μ²/φ)(r)·Fᵢ(log r/log R)²`. Each factor `/log R → (φ(W)/W)∫Fᵢ²`
(`yspace_muphi_diagonal_tendsto`). The complete contour-free `s1` MAIN TERM for the y-space sieve
— NO PNT. (The `o(main)` correction is the separate BV-gated obligation, gap C.) -/
theorem yr_heuristic_main_eq_muphi (k : ℕ) (Fs : Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ)
    (b W : ℕ) (x : ℝ) (M : ℝ) :
    (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
          BoundedGaps.Sieve.sieveDivisors H i.val b W x
            ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
        (∏ i : Fin k,
          yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).1
            * yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).2)
        * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      = M * ∏ i : Fin k, ∑ r ∈ (BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W),
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * Fs i (Real.log r / Real.log R) ^ 2 := by
  rw [BoundedGaps.Sieve.piFinset_lattice_main_factor
    (fun i => BoundedGaps.Sieve.sieveDivisors H i.val b W x
      ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x)
    (fun i de => yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) de.1
      * yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
        (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) de.2) M]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact yr_coord_sieveDiv_factor H i.val b W x (Fs i) R

end BoundedGaps.S1YSpace
