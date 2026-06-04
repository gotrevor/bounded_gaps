import Mathlib

/-!
# Laplace (cofactor) expansion of a factorial permanent

`permDenSum La Lb k = ∑_{ρ ∈ S_k} ∏_i (ofParts La i + ofParts Lb (ρ i))!` is the permanent of the
`k×k` matrix `N_{i,j} = (ofParts La i + ofParts Lb j)!`, where `ofParts L i = L.getD i 0` is the
parts list `L` padded with zeros.

`permDenSum_cons` (GIVEN, already proven) is the expansion of the permanent along row `0`
(the head value `a`), via `Equiv.Perm.decomposeFin`: fixing where row 0 maps (column `j`), the
remaining sum is over `S_n` with a `swap 0 j` reindexing.

GOAL: `permDenSum_laplace`. Convert that swap-form expansion into the clean recursion over `k-1`:
each inner sum is the permanent of `N` with row 0 and column `j` deleted, i.e. `permDenSum La Lb' (k-1)`
where `Lb'` is `Lb` with column `j` removed. Split the column index `j : Fin k`:

  * **zero columns** `j ≥ |Lb|` (so `ofParts Lb j = 0`): the factor is `(a+0)! = a!`, and deleting a
    zero column leaves `ofParts Lb` unchanged over `Fin (k-1)`, so the inner permanent is
    `permDenSum La Lb (k-1)`. There are `k - |Lb|` such columns ⇒ contributes
    `(k-|Lb|) · a! · permDenSum La Lb (k-1)`.
  * **positive columns** `j < |Lb|`: factor `(a + Lb.getD j 0)!`; deleting column `j` gives
    `ofParts (Lb.eraseIdx j)` over `Fin (k-1)`, so the inner permanent is
    `permDenSum La (Lb.eraseIdx j) (k-1)`.

The crux is the **column-deletion lemma**: for fixed `j`, the inner sum
`∑_{e ∈ S_{k-1}} ∏_x (ofParts La x + ofParts Lb (swap 0 j (succ (e x))))!`
equals `permDenSum La Lb' (k-1)`. The function `y ↦ ofParts Lb (swap 0 j (succ y))` is a
coordinate-rearrangement (some fixed permutation `π` of `Fin (k-1)`) of `ofParts Lb' : Fin (k-1) → ℕ`,
because they have the same value-multiset; then reindex `e ↦ π ∘ e` (a bijection of `S_{k-1}`).
`permDenSum La M (k-1)` is invariant under permuting `M`'s coordinates, by reindexing `ρ`.

Standard mathlib only; no axioms beyond the GIVEN `permDenSum_cons`. The hardest part is the
multiset equality of `ofParts Lb ∘ (swap 0 j ∘ succ)` with `ofParts (column-deleted Lb)`.
-/

open Finset
open scoped Nat

/-- Padded parts-list multi-index. -/
def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

/-- The sum over all permutations of the product of factorials — the permanent of `(La_i + Lb_j)!`. -/
def permDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ∑ ρ : Equiv.Perm (Fin k), ∏ i : Fin k, (ofParts La i + ofParts Lb (ρ i)).factorial

/-- **GIVEN (already proven).** Laplace expansion of `permDenSum` along the first row, via
`Equiv.Perm.decomposeFin`. -/
axiom permDenSum_cons (a : ℕ) (La Lb : List ℕ) (n : ℕ) :
    permDenSum (a :: La) Lb (n + 1) =
      ∑ j : Fin (n + 1), (a + ofParts Lb j).factorial *
        (∑ e : Equiv.Perm (Fin n),
          ∏ x : Fin n, (ofParts La x +
            ofParts Lb (Equiv.swap (0 : Fin (n + 1)) j (Fin.succ (e x)))).factorial)

/-- **GOAL.** Cofactor expansion in terms of `(k-1)`-permanents: the head value `a` is either matched
to a zero column (`a!`, `k-|Lb|` of them, inner permanent `permDenSum La Lb (k-1)`) or to a positive
column `j < |Lb|` (`(a+Lb_j)!`, inner permanent `permDenSum La (Lb.eraseIdx j) (k-1)`). -/
theorem permDenSum_laplace (a : ℕ) (La Lb : List ℕ) (k : ℕ)
    (hk : 0 < k) (hlenB : Lb.length ≤ k) :
    permDenSum (a :: La) Lb k =
      (k - Lb.length) * a.factorial * permDenSum La Lb (k - 1) +
        ∑ j ∈ Finset.range Lb.length,
          (a + Lb.getD j 0).factorial * permDenSum La (Lb.eraseIdx j) (k - 1) := by
  sorry
