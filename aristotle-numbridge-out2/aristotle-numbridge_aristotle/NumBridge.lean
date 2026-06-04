import NumBridgeHelpers

open Finset
open scoped Nat

/-! ## Base case lemma -/

lemma num_bridge_nil (Lb : List ℕ) (k : ℕ)
    (hlenB : Lb.length ≤ k)
    (hposB : ∀ x ∈ Lb, 0 < x) :
    (autParts ([] : List ℕ) : ℚ) * (autParts Lb : ℚ) *
      (∑ p ∈ orbitFin [] k, ∑ q ∈ orbitFin Lb k,
        (∏ i, ((p i + q i).factorial : ℚ)) * (∑ i, gWeight (p i) (q i)))
      = matchNumSum [] Lb k := by
  rw [orbitFin_nil]
  simp +decide [matchNumSum, autParts_nil]
  rw [Finset.sum_congr rfl fun x hx => by rw [orbit_prod_eq Lb k x hx, orbit_gsum_eq Lb k x hx]]
  convert congr_arg (fun x : ℚ => x *
      (∏ i : Fin k, ((ofParts Lb i).factorial : ℚ)) *
      (∑ i : Fin k, gWeight 0 (ofParts Lb i)))
    (orbit_stabilizer Lb k hlenB hposB) using 1
  · simp +decide [mul_assoc, Finset.mul_sum _ _ _]
  · rw [show matchDataN [] Lb =
        [(0, (Lb.map Nat.factorial).prod, (Lb.map (fun b => gWeight 0 b)).sum)] from ?_]
    · rw [prod_ofParts_factorial Lb k hlenB, sum_gWeight_ofParts Lb k hlenB]; norm_num
    · cases Lb <;> aesop

/-! ## The main theorem -/

/-- **The numerator bridge: orbit-sum of `(∏(pᵢ+qᵢ)!)·∑ g(pᵢ,qᵢ)` equals the matchings numerator
sum** (up to the `aut` over-count from repeated parts). -/
theorem num_bridge (La Lb : List ℕ) (k : ℕ)
    (hlenA : La.length ≤ k) (hlenB : Lb.length ≤ k)
    (hposA : ∀ x ∈ La, 0 < x) (hposB : ∀ x ∈ Lb, 0 < x) :
    (autParts La : ℚ) * (autParts Lb : ℚ) *
      (∑ p ∈ orbitFin La k, ∑ q ∈ orbitFin Lb k,
        (∏ i, ((p i + q i).factorial : ℚ)) * (∑ i, gWeight (p i) (q i)))
      = matchNumSum La Lb k := by
  induction La with
  | nil => exact num_bridge_nil Lb k hlenB hposB
  | cons a La ih =>
    /- The inductive step requires decomposing the orbit sum for (a :: La) by
       the "permanent expansion by the first row": grouping orbit pairs (p, q) by what value
       the position carrying 'a' in p is paired with in q. This mirrors the two branches of
       matchDataN's recursion: either a is "unmatched" (paired with q_i = 0), contributing
       a! to W and g(a,0) to Gocc, or a is "matched" to some b ∈ Lb (paired with q_i = b),
       contributing (a+b)! to W and g(a,b) to Gocc.

       The orbit-stabilizer lemma (orbit_stabilizer) handles the aut-counting, and the
       inductive hypothesis (ih) provides the identity for the sub-problems La with Lb and
       La with (Lb.eraseIdx j). The key combinatorial step is showing that the orbit sum
       over (a :: La) decomposes as the sum of these contributions.

       This step is the core of the numerator bridge and is extremely involved; it requires
       a careful orbit decomposition / permanent expansion argument. -/
    sorry
