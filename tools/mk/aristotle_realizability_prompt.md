# Aristotle target: joint-type realizability (orbit-free re-indexing crux)

Self-contained converse direction needed to make `orbitCore_eq_multinomial_sum`
orbit-free. Forward direction (`sum_joint_eq_fiber` / `_col`) is already proven in
the repo. This is the only new content. Stated in plain Lean 4 + mathlib (no
bounded_gaps defs) so the proof ports straight back.

```lean
import Mathlib
open Finset

/-- **Joint-type realizability.** Let `α β : Fin k → ℕ`. Given a contingency table
`X : ↥(image α) → ↥(image β) → ℕ` whose row margins equal α's value-fiber sizes and
whose column margins equal β's value-fiber sizes, there is a permutation `σ` of the
`k` slots such that the joint histogram of `(α ∘ σ, β)` is exactly `X`. -/
theorem joint_realizability {k : ℕ} (α β : Fin k → ℕ)
    (X : ↥(univ.image α) → ↥(univ.image β) → ℕ)
    (hrow : ∀ v, ∑ b, X v b = (univ.filter (fun i => α i = v.val)).card)
    (hcol : ∀ b, ∑ v, X v b = (univ.filter (fun i => β i = b.val)).card) :
    ∃ σ : Equiv.Perm (Fin k),
      ∀ (v : ↥(univ.image α)) (b : ↥(univ.image β)),
        (univ.filter (fun i => α (σ i) = v.val ∧ β i = b.val)).card = X v b := by
  sorry
```

## Math proof strategy (to guide the formalization)

Think of the `k` slots partitioned by their β-value into "columns" b, with
`#{i : β i = b}` slots per column. We must place α-values into these slots by
permuting α, so that within column b the value v appears exactly `X v b` times.

- **Supply = demand on rows:** the total demand for value v across all columns is
  `∑_b X v b = #{i : α i = v}` (hypothesis `hrow`), which is exactly the number of
  slots originally carrying α-value v. So the multiset of α-values to be placed
  equals the multiset α already provides.
- **Supply = demand on columns:** within column b the total slots to fill is
  `∑_v X v b = #{i : β i = b}` (hypothesis `hcol`), exactly the column size.

Because both margins match, a permutation σ realizing X exists. Clean construction:
build a bijection between the original slots (grouped by α-value) and the target
slots (grouped by (column b, value v) with multiplicity X v b). Equivalently, list
the `k` slots in two ways — by original α-value and by target cell — both lists are
permutations of the same multiset, giving σ. A `Finset.card`-preserving bijection /
`Equiv` assembled cell-by-cell (`Equiv.Perm` via matching equal-cardinality fibers,
e.g. `Finset.equivOfCardEq` per cell glued together) is the expected shape.

## Deliverable

A complete Lean 4 + mathlib proof of `joint_realizability` with the `sorry`
removed. Standalone file, no external axioms. Keep the exact statement (types and
hypotheses) so it drops into the repo unchanged.
