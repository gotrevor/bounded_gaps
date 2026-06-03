# PENDING WORK — open axioms, attack paths, and the numerical-endgame diagnosis

Last updated: 2026-06-03. Branch `path-a-selberg-nu`.

This file is the actionable inventory. The headline finding this lap **corrects two rounds of
handoffs**: the symmetric-reduction numerical endgame was NOT "just data + `native_decide`". The
committed `gram*Entry` defs enumerate `MarginCorrectTables = univ.filter` over
`CTable = img(α)→img(β)→Fin(k+1)`, i.e. `(k+1)^(cells)` tables — astronomically infeasible for
any real witness. This was verified empirically (an img-3 entry `native_decide`/`#eval` does NOT
finish even at `k=6`). Two reformulations now fix the table **count**; the remaining bottleneck is
precisely diagnosed below.

---

## A. The numerical `Mk k > 4` endgame (main thread)

### Mathematical facts established (Python, exact LDL; `tools/mk/`)
- Infinite-dimensional `M_k` crosses `4` only around `k ≈ 50`. So `k = 50, 54` (the named
  flagships) are razor-thin (`M_54 ≈ 4.0024`) → need a **near-optimal high-degree** polynomial.
  No low-complexity witness exists for them.
- For **larger `k`, lower degree suffices**: at symmetric degree `D = 7` (`#orbits = 45`),
  `M_k(7) > 4` for `k ≳ 200` (`M_200(7) ≈ 4.003`, `M_300(7) ≈ 4.011`). The exact LDL witness at
  `k = 300` has Rayleigh quotient `4.00694 > 4` (a genuine rational certificate). `tools/mk/_ldl.py`
  produces the exact integer orbit-coefficient vector `c`.
- A witness needs orbits with **≥ 3 distinct exponent values** (img ≥ 3): an img≤3-only basis
  never clears `4` (checked `D = 7,9,11`, `k` up to 2000). The 3 img-4 orbits at `D = 7`
  (`[4,2,1]`, `[3,2,1,1]`, `[3,2,1]`) are essential.

### What's DONE in Lean (committed, axiom-clean, verified)
- **`SymmetricReductionOrbitFree.lean`**: `Mk_gt_of_symWeight_witness{,_computable}`,
  `mk_*_of_symWeight*`, the full chain `symWeight → Gram quotient → Mk (n+1) > T`. Sound.
- **Margin-bounded reformulation** (`CTableBdd`, `gram*EntryBdd`, `Mk_gt_of_symWeight_witness_bdd`):
  re-types entries to `Fin (min(rowM,colM)+1)` — img-3 enumeration drops `(k+1)⁹ → (k+1)·2⁸`.
- **Fréchet-windowed reformulation** (`CTableW`, `entryW`, `gram*EntryW`,
  `Mk_gt_of_symWeight_witness_W`): `marginCorrect_frechet` caps the dominant `0`-cell free range at
  `k - max(rowM,colM) = #nonzero-positions ≤ 2·deg`, so the table enumeration is **fully
  k-independent** `∏(window+1)`. Verified correct (`11/3360`, `7/2160` at k=3; agrees with Bdd at
  k=12; img-4 accepted-table count = 43).

### The remaining bottleneck (precisely diagnosed)
`native_decide` of a full `Mk 200 > 4` witness is still not box-feasible. With table COUNT fixed by
windowing, the dominant cost is now **factor 1**: `entryW`/`cellLo` and the margin filter in
`MarginCorrectTables*` recompute `(univ.filter (fun i => a i = v)).card` over `Fin k` *per cell /
per row*, ~`O(k)` each, in the hot enumeration loop. (Bignums — factor 3 — only hit the few
*accepted* tables, so they are secondary; mathlib's `Nat.multinomial_cons` already gives the
cheap Pascal recurrence.) At `k=200` a single img-3 entry takes ~seconds; ×2025 entries = hours.

### Three attack paths (do ONE; they compose)
1. **Hoist the value-histogram (kills factor 1).** Parametrize the Gram entries by the precomputed
   margin histograms `histA, histB : List (ℕ × ℕ)` (value, count) instead of recomputing
   `(univ.filter …).card`. Prove `gramDenEntryH a b (trueHist a) (trueHist b) = gramDenEntry a b`,
   where `trueHist (op L)` is read off the parts list `L` (no `Fin k` scan). The witness then
   supplies histograms as **literals**, so `native_decide` never scans `Fin k`. This is the
   single highest-leverage step. (Repo refactor, ~150 lines; thread `hist` through
   `MarginCorrectTables`, `cellLo/Hi`, `gram*EntryW`.)
2. **Matchings closed form (kills factors 1+3 together, the principled endgame).** Prove
   `gramDenEntry a b = (∑_{partial matchings M of parts(a),parts(b)} k.descFactorial T_M · W_M) /
   (aut a · aut b · (k+|a|+|b|)!)` — the `tools/mk/mk_sym.py reduced_closed` formula, validated
   numerically. `k.descFactorial T_M` (T_M ≤ 2·deg) is a cheap product; the matchings count is
   k-independent; **one** factorial per entry (not per table). This is the genuine combinatorial
   bridge (table-sum ↔ matchings-sum); substantial but definitive. Likely multi-session /
   Aristotle-grade (needs `crossDenominator`/`orbitSum`/`monomialIntegral` context).
3. **Multinomial-fast (kills residual factor 3; in flight on Aristotle).** Replace the
   factorial-based `Nat.multinomial` in `gram*Entry` with a Pascal-`Nat.choose` recurrence.
   Aristotle job `f84ef793-0670-47bb-b72c-248002484355` (`aristotle-multinomialfast/`) proves the
   `multinomialFast = Nat.multinomial` equivalence; port it into `gram*EntryW` afterward. Helps the
   per-entry denominator `(k+2deg)!` and the accepted-table multinomials, but NOT factor 1 — do it
   *with* path 1 or 2.

### After feasibility: the payoff
`Mk_gt_of_symWeight_witness_W R c hR 4 (by native_decide)` for the `k=200`, `D=7` data → `Mk 200 > 4`
→ `Targets.H1_le_of_Mk_witness 200 H hAdm hLen` (a PROVEN, unconditional bridge via
Bombieri-Vinogradov) → `liminfGap 1 ≤ diameter H` for an admissible 200-tuple `H`. This would be the
**first kernel-checked `M_k > 4`** in the project — no `mk_*_witness` axiom. (A good admissible
200-tuple is needed for a meaningful diameter; `Engelsma` has 48–54 + 5511, not 200 — harvest one,
or use `exists_admissible_of_length` for a valid-but-weak bound first.)

The named flagships (`mk_54_witness_under_EH`, `mk_eps_50_witness`) need `k=50/54` at degree ~20+
(n ~ 600 orbits) — even with the above, much heavier; **host-better** and a separate push.

---

## B. Other open axioms (status / why deferred)

- **`Prerequisites.geh_implies_eh`** (`sorry`): needs a faithful `GEH` body (still opaque `axiom`)
  + Vaughan's identity to rebuild `Λ` from Type I/II convolutions. Multi-session; deferred.
- **Sieve bridges** `s1/s2_holds_from_*`, `exists_separable_F_of_Mk_gt`, `Mk_truncated`
  variants (`Sieve.lean`): the GPY/Maynard asymptotic sieve sums and the density realization of
  `M_k`. Deep analytic NT / functional analysis. `exists_separable_F_of_Mk_gt` is the most
  tractable (density of separable F + continuity of `MkF` ⟹ sup over separable = `M_k`) but still a
  big functional-analysis lift.
- **`BombieriVinogradov`, `GEH`, `GeneralizedBombieriVinogradov`, `MPZ_polymath8a`**
  (`Prerequisites.lean`): genuine external analytic-NT inputs; cite-only until mathlib/PNT+ ships.
- **`narrowness_*_ge_*`** (Clark–Jarvis 2001 exhaustive enumeration) and **`narrowness_*_le`** for
  large `k` (Hensley–Richards constructions, `k` up to `3.5e9`): combinatorial, out of scope at
  scale. `narrowness_5511_le` is done (Aristotle-assisted `native_decide`).
- **`Zhang.H1_le_70M`** (`sorry`): Zhang's method-faithful GPY+MPZ sieve; result already free via
  `Polymath8b.H1_le_246`. Deferred.
- **`Polymath8b.twin_primes_or_near_miss_Goldbach`** (`sorry`): §8, weeks of work. Deferred.

---

## C. Aristotle
- In flight: `f84ef793-0670-47bb-b72c-248002484355` — multinomialFast = Nat.multinomial.
- When it returns: verify in our kernel + `#print axioms`, port into `gram*EntryW`, then submit the
  next (candidate: the matchings closed form, path A.2, or a histogram-count lemma for path A.1).
