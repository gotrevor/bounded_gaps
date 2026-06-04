import Mathlib

/-!
# Laplace expansion of a permanent-style sum (`permDenSum_laplace`)

`ofParts L i = L.getD i 0` encodes a parts-list as a function `Fin k → ℕ` (positive parts `L`,
padded with zeros). `permDenSum La Lb k = ∑_{ρ ∈ Perm(Fin k)} ∏_i (ofParts La i + ofParts Lb (ρ i))!`
is a permanent (sum over all permutations of a product of factorials).

GOAL: prove `permDenSum_laplace` — the expansion of `permDenSum (a :: La) Lb k` "along the first
row" in terms of `(k-1)`-variable sub-permanents.  The first row entry `ofParts (a::La) 0 = a` is
paired with column `j`; if `j` lands on a zero-padding column (`j ≥ |Lb|`, value `0`, there are
`k-|Lb|` of them) we get `a! · permDenSum La Lb (k-1)`; if it lands on a real `Lb`-column
`j < |Lb|` (value `Lb.getD j 0`) we get `(a+Lb.getD j 0)! · permDenSum La (Lb.eraseIdx j) (k-1)`.

You are GIVEN (as `axiom permDenSum_cons`) the raw Laplace expansion via `Equiv.Perm.decomposeFin`
(already proven elsewhere): it expands over `j : Fin (n+1)` with the inner permutation sum using
`Equiv.swap 0 j (Fin.succ (e x))`.

STRATEGY (the informal proof is solid; your job is the Lean):
1. Set `k = n+1` (from `0 < k`). Apply `permDenSum_cons`.
2. KEY LEMMA — the inner sum collapses: for every `j : Fin (n+1)`,
     `∑ e : Perm (Fin n), ∏ x, (ofParts La x + ofParts Lb (Equiv.swap 0 j (Fin.succ (e x))))!`
       `= permDenSum La (Lb.eraseIdx j.val) n`.
   Proof: the map `x ↦ Equiv.swap 0 j (Fin.succ x)` is an injection `Fin n → Fin (n+1)` whose image
   is `{j}ᶜ`, exactly like `Fin.succAbove j`.  They differ by a permutation `τ` of `Fin n`
   (`∃ τ, ∀ x, Equiv.swap 0 j (Fin.succ x) = Fin.succAbove j (τ x)` — build `τ` via
   `Fin.exists_succAbove_eq`, since `Equiv.swap 0 j (Fin.succ x) ≠ j`).  Absorb `τ` by the
   permutation-invariance of the permanent (reindex the `e`-sum by `τ * e`, see
   `permSum_perm_invariant`).  Finally use the EXACT functional identity
     `ofParts Lb ∘ Fin.succAbove j = ofParts (Lb.eraseIdx j.val)`  (`ofParts_comp_succAbove`),
   which holds because `Fin.succAbove j` skips index `j` in increasing order, exactly as
   `List.eraseIdx` removes index `j`.
3. Split `∑ j : Fin (n+1)` into `j.val < Lb.length` and `j.val ≥ Lb.length`:
   - For `j ≥ |Lb|`: `ofParts Lb j = 0` (out of range), `Lb.eraseIdx j = Lb`, so each term is
     `a! · permDenSum La Lb n`, and there are `(n+1) - |Lb| = k - |Lb|` such `j`.
   - For `j < |Lb|`: `ofParts Lb j = Lb.getD j 0`, reindex the `Fin`-sum over `{j : j < |Lb|}` to
     `∑ j ∈ Finset.range Lb.length`.

Standard mathlib; no new axioms beyond the provided `permDenSum_cons`.
-/

open Finset
open scoped Nat

/-- Padded parts-list multi-index. -/
def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

/-- The permanent-style sum over all permutations of a product of factorials. -/
def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

/-- **GIVEN (already proven):** raw Laplace expansion of `permDenSum` via `decomposeFin`. -/
axiom permDenSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permDenSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), (a + ofParts Lb j).factorial *
        (∑ e : Equiv.Perm (Fin n),
          ∏ x : Fin n, (ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial)

/-- Permutation-invariance of the permanent: reindexing the column function `c` by a permutation
`π` (i.e. precomposing inside the product after the running permutation `e`) leaves the sum fixed. -/
lemma permSum_perm_invariant {n : ℕ} (w c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    (∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, (w x + c (π (e x))).factorial)
      = ∑ e : Equiv.Perm (Fin n), ∏ x : Fin n, (w x + c (e x)).factorial := by
  sorry

/-- **EXACT functional identity:** `ofParts Lb` precomposed with `Fin.succAbove j` (which skips
index `j` in increasing order) equals `ofParts (Lb.eraseIdx j)` (which removes the `j`-th element).
Holds for ALL `j : Fin (n+1)` and all lists. -/
lemma ofParts_comp_succAbove {n : ℕ} (Lb : List ℕ) (j : Fin (n + 1)) :
    (fun x : Fin n => ofParts Lb (Fin.succAbove j x)) = ofParts (Lb.eraseIdx j.val) := by
  sorry

/-- **MAIN GOAL.** Laplace expansion of `permDenSum (a :: La) Lb k` in terms of `(k-1)` permanents. -/
theorem permDenSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permDenSum (a :: La) Lb k =
      (k - Lb.length) * a.factorial * permDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * permDenSum La (Lb.eraseIdx j) (k - 1) := by
  sorry
