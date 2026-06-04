import Mathlib

/-!
# Value-histogram of a padded parts-list multi-index

In a bounded-gaps formalization we encode a monomial's exponent vector over `k` variables as
`ofParts L : Fin k → ℕ`, `ofParts L i = L.getD i.val 0`: a descending list `L` of the positive
exponents, padded with zeros out to length `k`. The Gram-matrix `native_decide` repeatedly needs
the *value-fiber size* `(univ.filter (fun i => ofParts L i = v)).card` (the number of variables
carrying exponent `v`). Computing it by scanning `Fin k` is `O(k)` and lives in the hot loop;
the goal here is the closed form, which is `O(|L|)` and `k`-independent (modulo the `v = 0`
padding term).

The closed form: among the `k` slots, value `v` occurs `L.count v` times within the list part,
plus — only when `v = 0` — once for each of the `k - L.length` padding slots.

Prove `card_filter_ofParts`. The two helper theorems below (`card_filter_ofParts_pos`,
`card_filter_ofParts_zero`) are convenience specializations; prove them too (each should follow
from the main lemma). Everything is standard mathlib; no axioms expected.
-/

open Finset

/-- Count of value `v` among the `k` slots of the padded parts list `L`
(`ofParts L i = L.getD i 0`). Within-list occurrences are `L.count v`; the `k - L.length`
padding slots all read `0`, so they contribute exactly when `v = 0`. -/
theorem card_filter_ofParts (k : ℕ) (L : List ℕ) (hL : L.length ≤ k) (v : ℕ) :
    (univ.filter (fun i : Fin k => L.getD i.val 0 = v)).card
      = L.count v + (if v = 0 then k - L.length else 0) := by
  sorry

/-- Specialization for a positive value `v` (no padding contribution). -/
theorem card_filter_ofParts_pos (k : ℕ) (L : List ℕ) (hL : L.length ≤ k) (v : ℕ) (hv : v ≠ 0) :
    (univ.filter (fun i : Fin k => L.getD i.val 0 = v)).card = L.count v := by
  sorry

/-- Specialization for `v = 0`: the zeros in `L` plus all `k - L.length` padding slots. -/
theorem card_filter_ofParts_zero (k : ℕ) (L : List ℕ) (hL : L.length ≤ k) :
    (univ.filter (fun i : Fin k => L.getD i.val 0 = 0)).card = L.count 0 + (k - L.length) := by
  sorry
