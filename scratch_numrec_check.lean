import Mathlib

/-!
# `matchNumSum` recursion (`matchNumSum_cons_eq'`)

This is the numerator analog of an already-proven denominator recursion. `matchDataN La Lb`
enumerates partial matchings of the parts of `La` to those of `Lb`, each as a triple
`(numPairs, W, Gocc)`: `W` = product of factorials, `Gocc` = sum of per-occupied-cell `gWeight`s.
`matchNumSum La Lb k` weights each matching by `k.descFactorial T · W · (Gocc + (k-T)·gWeight 0 0)`
where `T = |La|+|Lb|-numPairs` (occupied columns) and the `(k-T)` empty cells each add `gWeight 0 0`.

GOAL: prove `matchNumSum_cons_eq'` — the recursion expanding `matchNumSum (a::La) Lb k` in terms of
`matchNumSum` AND `matchDenSum` on the `(k-1)`-variable subproblems (the `gWeight a (·)` of the new
first row pulls out a `matchDenSum` term).

This MIRRORS the denominator recursion `matchDenSum_cons_eq'` (already proven), whose proof was:
```
  unfold matchDenSum
  simp +decide [Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul]
  -- two `descFactorial` front-factor rewrites (h_descFactorial / h_descFactorial' below)
  simp +decide [matchData, List.flatMap, List.sum_map_mul_left, List.sum_map_mul_right, ...]
  congr! 1
  · rw [← mul_assoc, ← List.sum_map_mul_left]; exact congr_arg _ (List.map_congr_left ...)
  · refine congr_arg _ (List.ext_get ?_ ?_) <;> simp +decide [Function.comp]; intro m hm; ...
```
Adapt that to the `matchDataN` triple + the `Gocc + (k-T)·gWeight 0 0` weight. Key facts (given as
axioms): `descFactorial_succ_eq'` (unconditional front-factor), `matchData_fst_le_la`, and
`matchDataN_proj` (the first-two-components projection of `matchDataN` is `matchData`, so a
`matchDataN`-sum of a function of `(numPairs, W)` only equals the corresponding `matchData`-sum).

Standard mathlib; no new axioms beyond those provided.
-/

open Finset
open scoped Nat

def gWeight (a b : ℕ) : ℚ := ((a + b + 2).factorial : ℚ) / ((a + 1) * (b + 1) * (a + b).factorial : ℚ)

def matchData : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod)]
  | (a :: La), Lb =>
      (matchData La Lb).map (fun pw => (pw.1, a.factorial * pw.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchData La (Lb.eraseIdx jb.1)).map (fun pw => (pw.1 + 1, (a + jb.2).factorial * pw.2)))

def matchDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ((matchData La Lb).map
    (fun pw => k.descFactorial (La.length + Lb.length - pw.1) * pw.2)).sum

def matchDataN : List ℕ → List ℕ → List (ℕ × ℕ × ℚ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod, (Lb.map (fun b => gWeight 0 b)).sum)]
  | (a :: La), Lb =>
      (matchDataN La Lb).map (fun t => (t.1, a.factorial * t.2.1, gWeight a 0 + t.2.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchDataN La (Lb.eraseIdx jb.1)).map
            (fun t => (t.1 + 1, (a + jb.2).factorial * t.2.1, gWeight a jb.2 + t.2.2)))

def matchNumSum (La Lb : List ℕ) (k : ℕ) : ℚ :=
  ((matchDataN La Lb).map (fun t =>
    let T := La.length + Lb.length - t.1
    (k.descFactorial T : ℚ) * t.2.1 * (t.2.2 + (k - T : ℕ) * gWeight 0 0))).sum

/-- GIVEN: unconditional descending-factorial front-factor recursion. -/
axiom descFactorial_succ_eq' (k n : ℕ) :
    k.descFactorial (n + 1) = k * (k - 1).descFactorial n

/-- GIVEN: every matching records at most `|La|` pairs. -/
axiom matchData_fst_le_la (La Lb : List ℕ) :
    ∀ pw ∈ matchData La Lb, pw.1 ≤ La.length

/-- GIVEN: the (numPairs, W) projection of `matchDataN` is exactly `matchData`. -/
axiom matchDataN_proj (La Lb : List ℕ) :
    (matchDataN La Lb).map (fun t => (t.1, t.2.1)) = matchData La Lb

/-- **MAIN GOAL.** The `matchNumSum` recursion. -/
theorem matchNumSum_cons_eq' (a : ℕ) (La Lb : List ℕ) (k : ℕ) :
    matchNumSum (a :: La) Lb k =
      k * (a.factorial * (matchNumSum La Lb (k - 1)
              + gWeight a 0 * (matchDenSum La Lb (k - 1) : ℚ))
        + ∑ j ∈ Finset.range Lb.length,
            (a + Lb.getD j 0).factorial * (matchNumSum La (Lb.eraseIdx j) (k - 1)
              + gWeight a (Lb.getD j 0) * (matchDenSum La (Lb.eraseIdx j) (k - 1) : ℚ))) := by
  sorry
