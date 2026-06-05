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

end BoundedGaps.S1YSpace
