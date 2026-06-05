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

end BoundedGaps.S1YSpace
