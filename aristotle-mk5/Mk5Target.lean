import Mathlib

/-! Standalone target: discharge Maynard's `M₅ > 2` lower bound at the
polynomial-Rayleigh level. All defs below are lifted VERBATIM from the
`bounded_gaps` repo (`BoundedGaps/SievePolynomial.lean`) so the proof ports
back name-for-name. -/

namespace Mk5Target

abbrev MultiIndex (k : ℕ) := Fin k → ℕ

def MultiIndex.degree {k : ℕ} (α : MultiIndex k) : ℕ := ∑ i, α i

structure PolynomialSieveWeight (k : ℕ) where
  terms : Finset (MultiIndex k × ℚ)

noncomputable def monomialIntegral {k : ℕ} (α : MultiIndex k) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) / ((k + α.degree).factorial : ℚ)

noncomputable def dirichletIntegralWithSlack {n : ℕ} (α : Fin n → ℕ) (β : ℕ) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) * (β.factorial : ℚ) /
    ((n + (∑ i, α i) + β).factorial : ℚ)

noncomputable def polynomialMaynardNumerator {k : ℕ}
    (P : PolynomialSieveWeight k) : ℚ :=
  match k, P with
  | 0, _ => 0
  | n + 1, P =>
      ∑ i : Fin (n + 1),
        ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          (p.2 * q.2 : ℚ) /
            (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
          dirichletIntegralWithSlack
            (Fin.removeNth i (p.1 + q.1))
            (p.1 i + q.1 i + 2)

noncomputable def polynomialMaynardDenominator {k : ℕ}
    (P : PolynomialSieveWeight k) : ℚ :=
  ∑ p ∈ P.terms, ∑ q ∈ P.terms, p.2 * q.2 * monomialIntegral (p.1 + q.1)

noncomputable def polynomialMkF {k : ℕ} (P : PolynomialSieveWeight k) : ℚ :=
  polynomialMaynardNumerator P / polynomialMaynardDenominator P

def P5terms : List (MultiIndex 5 × ℚ) := [
    (![0, 0, 0, 0, 0], (14960 : ℚ)),
    (![0, 0, 0, 0, 1], (-40392 : ℚ)),
    (![0, 0, 0, 0, 2], (59136 : ℚ)),
    (![0, 0, 0, 0, 3], (-31416 : ℚ)),
    (![0, 0, 0, 1, 0], (-40392 : ℚ)),
    (![0, 0, 0, 1, 1], (62832 : ℚ)),
    (![0, 0, 0, 1, 2], (-43197 : ℚ)),
    (![0, 0, 0, 2, 0], (59136 : ℚ)),
    (![0, 0, 0, 2, 1], (-43197 : ℚ)),
    (![0, 0, 0, 3, 0], (-31416 : ℚ)),
    (![0, 0, 1, 0, 0], (-40392 : ℚ)),
    (![0, 0, 1, 0, 1], (62832 : ℚ)),
    (![0, 0, 1, 0, 2], (-43197 : ℚ)),
    (![0, 0, 1, 1, 0], (62832 : ℚ)),
    (![0, 0, 1, 1, 1], (-39984 : ℚ)),
    (![0, 0, 1, 2, 0], (-43197 : ℚ)),
    (![0, 0, 2, 0, 0], (59136 : ℚ)),
    (![0, 0, 2, 0, 1], (-43197 : ℚ)),
    (![0, 0, 2, 1, 0], (-43197 : ℚ)),
    (![0, 0, 3, 0, 0], (-31416 : ℚ)),
    (![0, 1, 0, 0, 0], (-40392 : ℚ)),
    (![0, 1, 0, 0, 1], (62832 : ℚ)),
    (![0, 1, 0, 0, 2], (-43197 : ℚ)),
    (![0, 1, 0, 1, 0], (62832 : ℚ)),
    (![0, 1, 0, 1, 1], (-39984 : ℚ)),
    (![0, 1, 0, 2, 0], (-43197 : ℚ)),
    (![0, 1, 1, 0, 0], (62832 : ℚ)),
    (![0, 1, 1, 0, 1], (-39984 : ℚ)),
    (![0, 1, 1, 1, 0], (-39984 : ℚ)),
    (![0, 1, 2, 0, 0], (-43197 : ℚ)),
    (![0, 2, 0, 0, 0], (59136 : ℚ)),
    (![0, 2, 0, 0, 1], (-43197 : ℚ)),
    (![0, 2, 0, 1, 0], (-43197 : ℚ)),
    (![0, 2, 1, 0, 0], (-43197 : ℚ)),
    (![0, 3, 0, 0, 0], (-31416 : ℚ)),
    (![1, 0, 0, 0, 0], (-40392 : ℚ)),
    (![1, 0, 0, 0, 1], (62832 : ℚ)),
    (![1, 0, 0, 0, 2], (-43197 : ℚ)),
    (![1, 0, 0, 1, 0], (62832 : ℚ)),
    (![1, 0, 0, 1, 1], (-39984 : ℚ)),
    (![1, 0, 0, 2, 0], (-43197 : ℚ)),
    (![1, 0, 1, 0, 0], (62832 : ℚ)),
    (![1, 0, 1, 0, 1], (-39984 : ℚ)),
    (![1, 0, 1, 1, 0], (-39984 : ℚ)),
    (![1, 0, 2, 0, 0], (-43197 : ℚ)),
    (![1, 1, 0, 0, 0], (62832 : ℚ)),
    (![1, 1, 0, 0, 1], (-39984 : ℚ)),
    (![1, 1, 0, 1, 0], (-39984 : ℚ)),
    (![1, 1, 1, 0, 0], (-39984 : ℚ)),
    (![1, 2, 0, 0, 0], (-43197 : ℚ)),
    (![2, 0, 0, 0, 0], (59136 : ℚ)),
    (![2, 0, 0, 0, 1], (-43197 : ℚ)),
    (![2, 0, 0, 1, 0], (-43197 : ℚ)),
    (![2, 0, 1, 0, 0], (-43197 : ℚ)),
    (![2, 1, 0, 0, 0], (-43197 : ℚ)),
    (![3, 0, 0, 0, 0], (-31416 : ℚ))]

/-- The degree-3 symmetric witness on the 5-simplex (Maynard-style cubic). -/
noncomputable def P5 : PolynomialSieveWeight 5 := ⟨P5terms.toFinset⟩

/-- TARGET: prove this (replace the `sorry`).

`M₅ > 2` is the threshold for DHL[5,2]. It genuinely requires a *degree-3*
test function: degree ≤2 caps at `2274413/1142625 < 2`. This explicit cubic
`P5` realizes the exact rational Rayleigh value

  `polynomialMkF P5 = 12048682945 / 6016885374 ≈ 2.0024783…`

(numerator `polynomialMaynardNumerator P5 = 2409736589/66528`,
 denominator `polynomialMaynardDenominator P5 = 1002814229/55440`),
which exceeds 2. The intended route: unfold `polynomialMkF`,
`polynomialMaynardNumerator`, `polynomialMaynardDenominator` over the explicit
`P5terms.toFinset` (a 56-element list of monomials), evaluate the finite double
sums of rationals (`Finset.sum` over `List.toFinset`; `decide`/`norm_num`/
`Finset.sum_*` + `Rat` arithmetic), establishing the exact value, then `> 2`.
NOTE these defs are `noncomputable` (so plain `decide`/`native_decide` on
`polynomialMkF P5` directly will NOT fire — you must unfold and compute the
rational sums). Do NOT add `sorry` or new axioms. -/
theorem mk5_ratio_gt_two : polynomialMkF P5 > 2 := by
  sorry

end Mk5Target
