import Mathlib

/-!
# A computable, factorial-free `Nat.multinomial` via `Finset.fold`

`Nat.multinomial s f = (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!` evaluates the big `(∑ f)!` factorial,
which is bignum-heavy for `native_decide` when `∑ f` is large. The list-based fix
(`multinomialFast` over `s.toList`) is unusable here because `Finset.toList` is **noncomputable**.

`Finset.fold`, by contrast, is computable. Folding the commutative–associative "merge" operation
`multMerge` over the singletons `(f x, 1)` accumulates `(∑ f, multinomial)` using only
`Nat.choose` (the Pascal recurrence), no factorial. The goal is `multFold_eq`.

`multMerge (s₁,m₁) (s₂,m₂) = (s₁+s₂, m₁·m₂·(s₁+s₂).choose s₁)`: think of merging two disjoint
groups of sizes `s₁,s₂` with internal multinomials `m₁,m₂` — the combined multinomial multiplies
by the binomial choosing which combined slots belong to the first group. Commutativity uses
`Nat.choose_symm_diff`/`(s₁+s₂).choose s₁ = (s₁+s₂).choose s₂`; associativity is the identity
`(s₁+s₂).choose s₁ · (s₁+s₂+s₃).choose (s₁+s₂) = (s₂+s₃).choose s₂ · (s₁+s₂+s₃).choose s₁`
(both equal the trinomial `(s₁+s₂+s₃)! / (s₁! s₂! s₃!)`).

Prove the two instances and the three theorems. Everything is standard mathlib; no axioms.
-/

open Finset

/-- Merge two (size, multinomial) accumulators. -/
def multMerge : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ :=
  fun p q => (p.1 + q.1, p.2 * q.2 * (p.1 + q.1).choose p.1)

instance : Std.Commutative multMerge := by
  sorry

instance : Std.Associative multMerge := by
  sorry

/-- Computable, factorial-free multinomial: fold `multMerge` over the singletons `(f x, 1)`. -/
def multFold {α : Type*} (s : Finset α) (f : α → ℕ) : ℕ :=
  (s.fold multMerge (0, 1) (fun x => (f x, 1))).2

/-- The fold accumulates exactly `(∑ f, Nat.multinomial s f)`. The key induction lemma. -/
theorem multFold_pair {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    s.fold multMerge (0, 1) (fun x => (f x, 1)) = (∑ i ∈ s, f i, Nat.multinomial s f) := by
  sorry

/-- `multFold` computes `Nat.multinomial` (factorial-free, `native_decide`-friendly). -/
theorem multFold_eq {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    multFold s f = Nat.multinomial s f := by
  sorry
