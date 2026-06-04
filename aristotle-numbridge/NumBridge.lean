import Mathlib

/-!
# Numerator bridge: orbit-sum of `(∏(pᵢ+qᵢ)!)·∑ g(pᵢ,qᵢ)` = the matchings numerator sum

Companion to the denominator bridge (job `0b5bf5be`, `DenBridge.lean`). Same setup: a monomial's
exponent vector over `k` variables is `ofParts L i = L.getD i 0` (positive parts `L`, zero-padded);
its "orbit" `orbitFin L k` is the set of distinct coordinate-permutations.

The Gram-matrix NUMERATOR entry is, up to a constant factorial, the **orbit sum**
`∑_{p ∈ orbit La} ∑_{q ∈ orbit Lb} (∏ᵢ (pᵢ+qᵢ)!) · (∑ᵢ g(pᵢ,qᵢ))`,
where `g a b = (a+b+2)! / ((a+1)(b+1)(a+b)!)` is the per-cell weight (`g 0 0 = 2`). We claim it
equals a **matchings sum** `matchNumSum` that is independent of the enumeration: a sum over partial
matchings of the parts of `La` to the parts of `Lb`, weighted by a falling factorial
`k.descFactorial T`, a product `W` of factorials, and the `g`-weight aggregate
`Gocc + (k-T)·g(0,0)` (occupied tokens carry their `g`; the `k-T` empty slots each carry `g 0 0`).

THE IDENTITY (numerically anchored — `La=[2,1], Lb=[1,1], k=3`: the orbit-sum is `1176`,
`autParts La = 1`, `autParts Lb = 2`, `matchNumSum = 2352 = 1·2·1176`; equivalently
`gramNumEntry = matchNumForm = 7/2160`, both verified by `native_decide` in the host repo):

  `autParts La * autParts Lb *
      (∑_{p ∈ orbitFin La k} ∑_{q ∈ orbitFin Lb k} (∏ i, (p i + q i)!) · (∑ i, g (p i) (q i)))
    = matchNumSum La Lb k`.

This is the NUMERATOR analog of the denominator bridge: the same permanent/rook expansion grouped
by overlap pattern, but with the rational per-cell `g`-weights attached. Everything is over `ℚ`.

`orbitFin L k` = image of `Fin k`-permutations on `ofParts L` (a `Finset (Fin k → ℕ)`, deduplicated).
`matchDataN` is a bijective enumeration of partial matchings (each `La`-head is left unmatched —
`×a!`, add `g(a,0)` — or matched to a current `Lb` entry — erase it, `×(a+b)!`, add `g(a,b)`,
`numPairs+1`). `autParts L = ∏_v (multiplicity of v in L)!` (the orbit-stabilizer over-count).

Prove `num_bridge`. Expect induction on `La` mirroring `matchDataN`'s recursion, the orbit↔permutation
bookkeeping (`autParts` for repeated parts), and the key cell-regrouping `∑ᵢ g(pᵢ,qᵢ) = Gocc +
(#empty)·g(0,0)`. It is HARD — partial progress / key lemmas are valuable. Standard mathlib; no
axioms expected. Likely reusable: the denominator bridge's orbit-counting lemmas carry over, since
the orbit Finset and the `∏(pᵢ+qᵢ)!` factor are identical; only the `g`-weight aggregate is new.
(`hpos*` say the parts are positive; `hlen*` that they fit.)
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

/-- `g(a,b) = (a+b+2)!/((a+1)(b+1)(a+b)!)`; `g(0,0)=2`. The numerator's per-cell weight. -/
def gWeight (a b : ℕ) : ℚ := ((a + b + 2).factorial : ℚ) / ((a + 1) * (b + 1) * (a + b).factorial : ℚ)

/-- Bijective enumeration of partial matchings carrying `(numPairs, W, Gocc)`. -/
def matchDataN : List ℕ → List ℕ → List (ℕ × ℕ × ℚ)
  | [], Lb => [(0, (Lb.map Nat.factorial).prod, (Lb.map (fun b => gWeight 0 b)).sum)]
  | (a :: La), Lb =>
      (matchDataN La Lb).map (fun t => (t.1, a.factorial * t.2.1, gWeight a 0 + t.2.2))
      ++ ((List.range Lb.length).zip Lb).flatMap (fun jb =>
          (matchDataN La (Lb.eraseIdx jb.1)).map
            (fun t => (t.1 + 1, (a + jb.2).factorial * t.2.1, gWeight a jb.2 + t.2.2)))

/-- `matchNumSum = ∑_M k.descFactorial (|La|+|Lb|-numPairs) · W · (Gocc + (k-T)·g(0,0))`. -/
def matchNumSum (La Lb : List ℕ) (k : ℕ) : ℚ :=
  ((matchDataN La Lb).map (fun t =>
    let T := La.length + Lb.length - t.1
    (k.descFactorial T : ℚ) * t.2.1 * (t.2.2 + (k - T : ℕ) * gWeight 0 0))).sum

/-- **The numerator bridge: orbit-sum of `(∏(pᵢ+qᵢ)!)·∑ g(pᵢ,qᵢ)` equals the matchings numerator
sum** (up to the `aut` over-count from repeated parts). -/
theorem num_bridge (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    (autParts La : ℚ) * (autParts Lb : ℚ) *
      (∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k,
        (∏ i, ((p i + q i).factorial : ℚ)) * (∑ i, gWeight (p i) (q i)))
      = matchNumSum La Lb k := by
  sorry
