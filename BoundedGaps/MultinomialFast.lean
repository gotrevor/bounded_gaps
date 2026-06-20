import Mathlib

/-!
# native_decide-efficient `Nat.multinomial`

`Nat.multinomial s f := (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!` is defined via the *factorial*
quotient, so `native_decide`/`#eval` on `Nat.multinomial univ f` computes `(∑ f)!` — a number
with ~`(∑ f)·log(∑ f)` digits (e.g. `200!` ≈ 375 digits). In our application `∑ f` can be ~200,
making the Gram-matrix `native_decide` factorial-heavy.

mathlib provides the telescoping recurrence
  `Nat.multinomial_cons : multinomial (s.cons a ha) f = (f a + ∑_{s} f).choose (f a) * multinomial s f`
which expresses the multinomial as a product of *binomial* coefficients. `Nat.choose` is computed
by the (cheap, factorial-free) Pascal recurrence. The goal is a structurally-recursive list-based
`multinomialFast` that `native_decide` evaluates via `Nat.choose` only, proven equal to
`Nat.multinomial` over a Finset's `toList`.

Everything below is standard mathlib; no axioms. Prove `multinomialFast_eq`.
-/

open Finset

/-- List-based multinomial via the binomial (Pascal) recurrence — `native_decide`-cheap. -/
def multinomialFast {V : Type*} (f : V → ℕ) : List V → ℕ
  | [] => 1
  | x :: xs => (f x + (xs.map f).sum).choose (f x) * multinomialFast f xs

/-- `multinomialFast` over a list with no duplicates equals `Nat.multinomial` over its `toFinset`.
This is the form that lets `native_decide` avoid large factorials. -/
theorem multinomialFast_eq {V : Type*} [DecidableEq V] (l : List V) (hl : l.Nodup) (f : V → ℕ) :
    multinomialFast f l = Nat.multinomial l.toFinset f := by
  induction l with
  | nil => simp [multinomialFast, Nat.multinomial]
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    simp only [multinomialFast]
    rw [ih hl.2, List.toFinset_cons,
        Nat.multinomial_insert (show x ∉ xs.toFinset by simpa using hl.1) f,
        List.sum_toFinset f hl.2]

/-- Specialization to a `Finset`'s own `toList` (what the application uses): the fast list
multinomial over `s.toList` equals `Nat.multinomial s f`. -/
theorem multinomialFast_toList_eq {V : Type*} [DecidableEq V] (s : Finset V) (f : V → ℕ) :
    multinomialFast f s.toList = Nat.multinomial s f := by
  rw [multinomialFast_eq s.toList]
  · rw [Finset.toList_toFinset]
  · exact Finset.nodup_toList s
