import Mathlib

open scoped BigOperators
open Filter

/-!
# Squarefree `φ(r)/r²` Mertens-type asymptotic (GPY singular-series coefficient)

The GPY/Maynard diagonalised Selberg form has coefficient `φ(r)/r²` over squarefree `r`
(see `∑_{r sf} (φ(r)/r²) z_r²`). The basic averaging brick is the partial-sum asymptotic

  `(∑_{r ≤ N, r squarefree} φ(r)/r²) / log N → C`   as `N → ∞`,  for some `C > 0`.

This is a mean value of the multiplicative function `r ↦ μ²(r)·φ(r)/r²`. Its Dirichlet series
`∑_{r sf} (φ(r)/r²) r^{-s} = ∏_p (1 + (p-1)/p^{2+s}) = ζ(1+s)·G(s)` with `G` holomorphic and
nonzero near `s = 0` (since `(1 + (p-1)/p^{2+s})(1 - p^{-(1+s)}) = 1 - p^{-(2+s)} - p^{-(2+2s)}
+ p^{-(3+2s)}` converges). Hence the partial sum `∑_{r≤N,sf} φ(r)/r² ∼ C·log N` with
`C = G(0) = ∏_p (1 - 2/p² + 1/p³) > 0` (the residue at `s = 0`).

## Strategy (Lean-friendly, elementary; avoid contour integration)
Write `φ(r)/r² = (1/r)·∏_{p∣r}(1 − 1/p)` for squarefree `r`. Use the Dirichlet hyperbola /
convolution identity: the multiplicative function `f(r) = μ²(r)φ(r)/r²` factors as
`f = (1/r) ⋆ a` (Dirichlet convolution against `1/r`) for a multiplicative `a` with
`∑ |a(d)|/d < ∞` and `∑ a(d)/d = C`. Then
`∑_{r≤N} f(r) = ∑_{d≤N} a(d) ∑_{m ≤ N/d} 1/(dm) = ∑_{d≤N} (a(d)/d)·(harmonic(⌊N/d⌋))`
`= ∑_{d≤N}(a(d)/d)(log(N/d) + γ + o(1)) = C·log N + O(1)`, so dividing by `log N → C`.
(Equivalently: known mean-value theorems for nonnegative multiplicative functions whose
Dirichlet series has a simple pole.) Keep `#print axioms` clean (no `sorry`).

The exact value of `C` is not needed — the existence of a positive limit suffices.
-/

namespace AristotlePhiSq

theorem squarefree_phi_div_sq_asymptotic :
    ∃ C : ℝ, 0 < C ∧ Tendsto
      (fun N : ℕ =>
        (∑ r ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r),
            (Nat.totient r : ℝ) / (r : ℝ) ^ 2) / Real.log N)
      atTop (nhds C) := by
  sorry

end AristotlePhiSq
