# Summary of changes for run 581ae825-8458-4a7d-9903-8ce131f5b216
## Summary of Progress on `denom_bridge`

The theorem `denom_bridge` is a deep combinatorial identity relating orbit sums of products of factorials to a matchings sum (a permanent/rook-polynomial expansion). I made substantial progress, reducing the problem from a single monolithic sorry to a clean proof architecture with only **2 remaining sorries** out of ~20 lemmas.

### What was proved (sorry-free):

**Orbit-stabilizer infrastructure:**
- `autParts_nil`, `orbitFin_nil`, `prod_comp_perm`, `prod_ofParts_factorial`, `orbitFin_prod_factorial_eq` — basic lemmas about orbits and automorphisms
- `autParts_cons` — recursion for autParts when adding an element
- `orbit_count_val`, `orbit_count_zero` — each orbit element has the same value histogram
- `mem_orbitFin_iff_count` — orbit membership characterized by matching value counts
- `orbit_update_zero_mem`, `orbit_update_val_mem` — orbit membership transfers via Function.update
- `orbit_card_cons` — orbit size recursion via double counting bijection
- `orbit_card_mul_aut` — the orbit-stabilizer counting theorem: `autParts L * |orbitFin L k| = k.descFactorial L.length`

**Permutation sum bridge:**
- `permDenSum` — defined as the sum over all permutations
- `orbit_sum_eq_perm_sum` — converts orbit sums to permutation sums (orbit-stabilizer for sums)
- `lhs_eq_perm` — the orbit-side of the identity equals `k! * permDenSum` up to scaling
- `permDenSum_nil`, `rhs_eq_perm_nil` — base cases for the permanent ↔ matching connection
- `descFactorial_succ_eq`, `descFactorial_mul_factorial` — key descending factorial identities
- `matchDenSum_cons_eq` — matchDenSum recursion in terms of (k-1)
- `permDenSum_cons` — Laplace expansion of permDenSum via `Equiv.Perm.decomposeFin`

**Main theorem reduction:**
- `denom_bridge` — proved modulo `rhs_eq_perm`, via `nlinarith` from `lhs_eq_perm` and `rhs_eq_perm`
- `denom_bridge_nil` — base case proved

### What remains (2 sorries):

1. **`permDenSum_laplace`** — The Laplace expansion of permDenSum connecting it to permDenSum of sub-problems with `k-1` variables. This requires showing that the inner permanent sum (after fixing which column position 0 maps to) equals a permanent of a submatrix, using column permutation invariance of the permanent.

2. **`rhs_eq_perm`** — The permanent = matching identity. With `permDenSum_laplace` proved, this would follow by induction on `La` using `matchDenSum_cons_eq` and the inductive hypothesis to connect the matchings sum to the permanent via the Laplace expansion.

The remaining sorries encapsulate the hardest part of the proof: the column permutation invariance of the permanent and its connection to the matching recursion. The proof sketch for `rhs_eq_perm` is fully worked out in the informal proof passed to the subagent — it's a clean algebraic argument that distributes factorial scaling factors and applies the IH.