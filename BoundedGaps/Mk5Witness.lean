import BoundedGaps.SievePolynomial

/-!
# `M₅ > 2`: explicit polynomial witness (discharges `mk_5_witness_under_EH`)

Maynard's `M₅ > 2` (threshold for DHL[5,2] under EH) was an `axiom` cited as a
§-numerical "Maple" bound. It is in fact dischargeable: the repo already has
`Sieve.Mk k ≥ polynomialMkF P` (axiom-clean, via the smooth-cutoff + DCT
`Mk_ge_polynomialMkF`), so it suffices to exhibit a polynomial `P` with
rational Rayleigh ratio `polynomialMkF P > 2`.

`M₅ > 2` genuinely needs a **degree-3** test function (degree ≤2 caps at
`2274413/1142625 < 2`). The explicit symmetric cubic `P5` below (56 monomials,
7 orbit-coefficients found by solving the finite generalised eigenproblem in
exact rationals) realises

  `polynomialMkF P5 = 12048682945 / 6016885374 ≈ 2.00248 > 2`.

`polynomialMkF` is `noncomputable` (Finset sums + factorial-ℚ), so we mirror its
numerator/denominator with **computable** `List` evaluators (`numC`/`denC`),
bridge `Finset.sum over toFinset ↔ List.sum` (the 56 monomials are `Nodup`), and
close the exact rational value by `native_decide`.
-/

namespace BoundedGaps.Maynard

open BoundedGaps BoundedGaps.SievePolynomial Sieve

/-- Computable mirror of `monomialIntegral` (defeq: `MultiIndex.degree = ∑ i, ·`). -/
private def monoIntC {k : ℕ} (α : MultiIndex k) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) / ((k + (∑ i, α i)).factorial : ℚ)

/-- Computable mirror of `dirichletIntegralWithSlack` (defeq). -/
private def dirSlackC {n : ℕ} (α : Fin n → ℕ) (β : ℕ) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) * (β.factorial : ℚ) /
    ((n + (∑ i, α i) + β).factorial : ℚ)

private def P5terms : List (MultiIndex 5 × ℚ) := [
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

/-- The explicit degree-3 symmetric witness as a polynomial sieve weight. -/
noncomputable def P5 : PolynomialSieveWeight 5 := ⟨P5terms.toFinset⟩

private def denC : ℚ :=
  (P5terms.map (fun p =>
    (P5terms.map (fun q => p.2 * q.2 * monoIntC (p.1 + q.1))).sum)).sum

private def numC : ℚ :=
  ∑ i : Fin 5, (P5terms.map (fun p =>
    (P5terms.map (fun q =>
      (p.2 * q.2) / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
      dirSlackC (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2))).sum)).sum

private lemma P5nodup : P5terms.Nodup := by native_decide

/-- `Finset.sum` over `P5terms.toFinset` of a double sum collapses to nested
`List.sum` (the monomials are `Nodup`). -/
private lemma dsum (g : (MultiIndex 5 × ℚ) → (MultiIndex 5 × ℚ) → ℚ) :
    (∑ p ∈ P5terms.toFinset, ∑ q ∈ P5terms.toFinset, g p q)
      = (P5terms.map (fun p => (P5terms.map (fun q => g p q)).sum)).sum := by
  rw [List.sum_toFinset _ P5nodup]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  exact List.sum_toFinset _ P5nodup

private lemma den_eq : polynomialMaynardDenominator P5 = denC := by
  unfold polynomialMaynardDenominator denC
  exact dsum (fun p q => p.2 * q.2 * monomialIntegral (p.1 + q.1))

private lemma num_eq : polynomialMaynardNumerator P5 = numC := by
  unfold polynomialMaynardNumerator numC
  apply Finset.sum_congr rfl
  intro i _
  exact dsum (fun p q =>
    (p.2 * q.2) / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ)) *
    dirichletIntegralWithSlack (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2))

private lemma polynomialMkF_P5 : polynomialMkF P5 = 12048682945 / 6016885374 := by
  unfold polynomialMkF
  rw [num_eq, den_eq]
  have hn : numC = 2409736589 / 66528 := by native_decide
  have hd : denC = 1002814229 / 55440 := by native_decide
  rw [hn, hd]; norm_num

/-- **M₅ > 2/ϑ under EH** (Maynard 2015 Thm 1.1). Discharged via the explicit
cubic witness `P5`: `Sieve.Mk 5 ≥ polynomialMkF P5 = 12048682945/6016885374`,
and `ϑ = 999/1000` gives `2/ϑ = 2000/999 < 12048682945/6016885374`. -/
theorem mk_5_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 5 > 2 * 1 / ϑ := by
  have hMk : Sieve.Mk 5 ≥ (polynomialMkF P5 : ℝ) := by
    rw [← polynomialMkF_eq_MkF]; exact Mk_ge_polynomialMkF P5
  refine ⟨999 / 1000, ⟨by norm_num, by norm_num⟩, ?_⟩
  have hlt : (2 : ℝ) * 1 / (999 / 1000) < (polynomialMkF P5 : ℝ) := by
    rw [polynomialMkF_P5]; push_cast; norm_num
  exact lt_of_lt_of_le hlt hMk

end BoundedGaps.Maynard
