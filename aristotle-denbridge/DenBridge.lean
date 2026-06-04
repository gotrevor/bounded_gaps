import Mathlib

/-!
# Denominator bridge: orbit-sum of products of factorials = the matchings sum

This is the combinatorial heart of a bounded-gaps formalization. We encode a monomial's exponent
vector over `k` variables as `ofParts L i = L.getD i 0` (positive parts `L`, padded with zeros).
The "orbit" of such a vector is its set of distinct coordinate-permutations.

The Gram-matrix denominator entry is, up to a constant factorial, the **orbit sum**
`∑_{p ∈ orbit La} ∑_{q ∈ orbit Lb} ∏_i (p i + q i)!`. We claim it equals a **matchings sum** that
is independent of the enumeration: a sum over partial matchings of the parts of `La` to the parts
of `Lb`, weighted by a falling factorial `k.descFactorial T` and a product `W` of factorials.

THE IDENTITY (verified numerically — `La=[2,1], Lb=[1,1], k=3`: orbit-sum `= 132`,
`autParts La = 1`, `autParts Lb = 2`, `matchDenSum = 264 = 1·2·132`):

  `autParts La * autParts Lb * (∑_{p ∈ orbitFin La k} ∑_{q ∈ orbitFin Lb k} ∏ i, (p i + q i)!)`
    `= matchDenSum La Lb k`.

`orbitFin L k` = the image of `Fin k`-permutations acting on `ofParts L` (a `Finset (Fin k → ℕ)`,
deduplicated). `matchData` is a bijective enumeration of partial matchings (each `La`-head is left
unmatched — `×a!` — or matched to a current `Lb` entry — erase it, `×(a+b)!`, `numPairs+1`).
`autParts L = ∏_v (multiplicity of v in L)!`.

Prove `denom_bridge`. This is a genuine permanent/rook-polynomial expansion (the permanent of the
matrix `[(La_iᵢ + Lb_jⱼ)!]` grouped by overlap pattern); expect to need induction on `La` mirroring
`matchData`'s recursion, plus the orbit↔permutation bookkeeping (`autParts` accounts for repeated
parts via the orbit-stabilizer count). It is HARD — partial progress / key lemmas are valuable.
Standard mathlib; no axioms expected. (`hpos*` say the parts are positive; `hlen*` that they fit.)
-/

open Finset
open scoped Nat

/-- Padded parts-list multi-index. -/
def ofParts {k : ℕ} (L : List ℕ) : Fin k → ℕ := fun i => L.getD i.val 0

/-- The orbit of `ofParts L`: distinct coordinate-permutations, as a `Finset (Fin k → ℕ)`. -/
def orbitFin (L : List ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Finset.image (fun σ : Equiv.Perm (Fin k) => fun i => (ofParts L) (σ i)) Finset.univ

/-- `aut L = ∏_v (multiplicity of value v in L)!`. -/
def autParts (L : List ℕ) : ℕ := (L.dedup.map (fun v => (L.count v).factorial)).prod

/-- Bijective enumeration of partial matchings of `La`-parts to `Lb`-parts: `(numPairs, W)` with
`W = ∏ paired (a+b)! · ∏ unmatched a! · ∏ unmatched b!`. -/
def matchData : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod)]
  | (a :: La), Lb =>
      (matchData La Lb).map (fun pw => (pw.1, a.factorial * pw.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchData La (Lb.eraseIdx jb.1)).map (fun pw => (pw.1 + 1, (a + jb.2).factorial * pw.2)))

/-- `matchDenSum = ∑_M k.descFactorial (|La|+|Lb|-numPairs) · W(M)`. -/
def matchDenSum (La Lb : List ℕ) (k : ℕ) : ℕ :=
  ((matchData La Lb).map
    (fun pw => k.descFactorial (La.length + Lb.length - pw.1) * pw.2)).sum

/-- **The denominator bridge: orbit-sum of `∏(pᵢ+qᵢ)!` equals the matchings sum** (up to the
`aut` over-count from repeated parts). -/
theorem denom_bridge (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    autParts La * autParts Lb *
      (∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k, ∏ i, (p i + q i).factorial)
      = matchDenSum La Lb k := by
  sorry
