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

### The remaining bottleneck — EMPIRICALLY RE-DIAGNOSED 2026-06-03 (this overturns "factor 1 is gating")
Lap 2026-06-03 BUILT and MEASURED all three factors. Findings (timed `native_decide`/`#eval`):

- **Factor 1 (Fin-k scan) — SOLVED.** Committed `card_filter_ofParts` (Aristotle `656d6b54`) +
  `partsHist k L` (= `L.count v + (v=0 ? k - L.length : 0)`, the k-INDEPENDENT margin, no `Fin k`
  scan). The `WH` layer (`entryWH/MarginCorrectTablesWH/gram*EntryWH` + `gram*EntryWH_eq` bridges,
  `Mk_gt_of_symWeight_witness_WH`) threads margins as explicit `ℕ→ℕ` functions. Measured: an img-4
  enumeration `card` at `k=300` went **>280s (timeout) → 41s** by swapping the `histArr` Fin-k scan
  for `partsHist`. ⚠️ **`histArr` (a `let arr := …scan…; fun v => arr.getD v 0`) does NOT materialize
  under `native_decide`** — it rebuilt the array per lookup (k=30: 125s, k=300: timeout, i.e. cost
  ∝ k). So **never rely on per-entry `let`-materialization in `native_decide`; the margin MUST be
  genuinely k-independent (`partsHist` from the parts list).**
- **THE REAL WALL (new): the windowed table COUNT itself.** An img-4 orbit (4 distinct exponent
  values, e.g. `[4,2,1]`) ⇒ 4×4 = 16 cells ⇒ `univ : CTableW` has `4·2^15 = 131072` tables, and this
  is **k-independent** (can't shrink by lowering k). The margin filter is cheap now, but
  `native_decide` still ENUMERATES all 131072 per entry (~41s for the card alone). The 3 essential
  img-4 orbits (`[4,2,1]`,`[3,2,1,1]`,`[3,2,1]`) give 9 img-4×img-4 entries at ~41s+ each
  (+factorials) ⇒ the full 45-orbit witness is ~tens of min–hours and likely OOM/too-slow even on a
  host. img-4 is mathematically REQUIRED (img≤3 bases never clear 4, checked `D=7,9,11`,
  `tools/mk/img3only.py`). **Windowing fixed the 0-cell range but NOT the 2^(#offdiag-cells) blowup.**
- **Factor 3 (bignums) — partially handled, not the gate.** Per accepted table, the column multinomial
  `Nat.multinomial univ (fun v => entryW…)` sums to the 0-column margin (~297 at k=300) ⇒ `297!`.
  `multinomialFast` (Aristotle `f84ef793`, committed in `MultinomialFast.lean`, kernel-clean) routes
  this through `Nat.choose` (Pascal). ⚠️ but `Finset.toList` is **noncomputable**, so
  `multinomialFast f s.toList` can't be used in a `native_decide` def directly — need a COMPUTABLE
  fast multinomial. Aristotle job `3591b35b` (`aristotle-multfold/`) is proving `multFold` (via
  `Finset.fold` of binomials = `Nat.multinomial`). ALSO note `Nat.choose`'s naive Pascal recursion is
  itself slow for *balanced* args — prefer the `descFactorial` form (matchings, below).

### THE path forward: A.2 matchings closed form is now the ONLY box-feasible route
Because the table COUNT (not the per-table work) is the wall, the enumeration must be REPLACED by a
sum that is small AND k-independent. That is the **matchings closed form** (`tools/mk/mk_sym.py`,
function `_entry_sums`/`reduced_closed`, validated vs brute + the Lean `11/3360` spot-check):

    gramDenEntry lam mu = (1/(aut lam · aut mu)) · (∑_M ff(k,T_M) · W(M)) / (k+|lam|+|mu|)!
    gramNumEntry lam mu = (1/(aut lam · aut mu)) · (∑_M ff(k,T_M) · W(M) · (Gocc(M)+(k-T_M)·g(0,0)))
                            / (k+|lam|+|mu|+1)!
  where (lam,mu = the NONZERO parts lists; rl=|lam|, rm=|mu|):
    M       ranges over partial matchings pairing some lam-parts with some mu-parts (t pairs,
            t=0..min(rl,rm); choose t-subsets of each + a bijection) — count is k-INDEPENDENT, ~34
            for rl=rm=3.
    T_M     = rl + rm − |M|   (occupied slots)
    ff(k,T) = k·(k−1)···(k−T+1) = `k.descFactorial T`   (T ≤ 2·deg ≤ 14 — a CHEAP product, no factorial)
    W(M)    = ∏_{paired (a,b)} (lam_a+mu_b)! · ∏_{lam-only a} lam_a! · ∏_{mu-only b} mu_b!
    aut(lam)= ∏_v (mult of value v in lam)!
    g(a,b)  = (a+b+2)!/((a+1)(b+1)(a+b)!);  g(0,0)=2
    Gocc(M) = ∑ over occupied tokens of g(content): paired→g(lam_a,mu_b), solo→g(lam_a,0)/g(0,mu_b)
  ⇒ ~34 cheap terms/entry, ONE factorial/entry, descFactorial only ⇒ full witness `native_decide`
  in milliseconds, AND makes the flagships k=50/54 (degree ~20) feasible too.

**LANDED THIS LAP (committed `ca3d47f`):** the matchings-form DEFS + WITNESS are in
`SymmetricReductionOrbitFree.lean`: `matchData/matchDenSum/autParts/matchDenForm` (denominator),
`gWeight/matchDataN/matchNumSum/matchNumForm` (numerator), `#eval`/`native_decide`-INSTANT even at
k=300 img-4; numerically validated (`11/3360`, `7/2160` = the Lean spot-checks). The two bridge
identities are DISCLOSED AXIOMS `gramDenEntry_eq_matchDenForm`, `gramNumEntry_eq_matchNumForm`, and
`Mk_gt_of_symWeight_witness_match` wires them (`#print axioms` = the 3 std + those 2; no sorry).

So A.2 has TWO remaining pieces:
1. **Prove the 2 bridge axioms** — the genuine combinatorial identity (contingency-table-sum =
   partial-matchings-sum, equivalently the orbit/permanent `∑_{p∈orbit a}∑_{q∈orbit b}∏ᵢ(pᵢ+qᵢ)!`
   = `∑_M ff(k,T_M)W(M)`, a permanent/rook expansion over `S_k` grouped by overlap pattern). The
   repo already proves orbit-sum = table-sum (`orbitPair_denominator_shapeForm`); the new work is
   orbit-sum = matchings-sum. Substantial, multi-session. Denominator first (numerator adds the
   `Gocc`/`g` weights). Hard to state self-contained for Aristotle (entangled with the orbit/table
   machinery) — likely a local incremental proof.
2. **Re-key the witness theorem on parts-lists / `Fin 45`** (CAPSTONE feasibility). Measured this lap:
   `Mk_gt_of_symWeight_witness_match` sums over `R : Finset (MultiIndex (n+1))` with `c, P` as
   functions on `MultiIndex` — evaluating `c a`/`P a` per summand requires a 45-way match over
   200-entry functions (`#eval` of the full witness CRASHED, code 134 / ~7e9 lookup ops). FIX: a
   variant `…_parts (Ls : List (List ℕ)) (cs : List ℤ) …` whose sum is `∑ i j, cs[i]·cs[j]·matchForm
   Ls[i] Ls[j] (n+1)` (DIRECT indexing, no `MultiIndex` matching), related to `∑ over R = (Ls.map
   ofParts).toFinset` (dedup + `ofParts` injectivity + orbit-disjointness from distinct parts-lists).
   This also subsumes the old "margin materialization" fix (margins `partsHist (n+1) Lᵢ`, Lᵢ in hand).

### After both: the capstone payoff
With (1)+(2): `Mk_gt_of_symWeight_witness_match_parts witLs witCs … (by native_decide)` for the k=200
D=7 data (45 orbits, ratio 4.002898 — Python-confirmed, `/tmp/gen_witness_lean.py`) → `(4:ℝ) < Mk 200`
resting ONLY on the 2 (then-proven) bridge identities → `Targets.H1_le_of_Mk_witness 200 H hAdm hLen`
(PROVEN, unconditional, via Bombieri-Vinogradov) → `liminfGap 1 ≤ diameter H` for an admissible
200-tuple `H`. **First kernel-checked `M_k > 4`** in the project. (`Engelsma` has 48–54 + 5511, not
200 — harvest a 200-tuple or use `exists_admissible_of_length` for a valid-but-weak diameter first.)
NOTE: the heavy `native_decide` (2025 matchForm terms, ~100-digit coeffs, 214! factorials) may be
HOST-only (box hit intermittent OOM/SIGABRT this lap even on mathlib olean loads).

Witness data IN HAND (`tools/mk/_ldl.py`, exact LDL): k=200 D=7 ratio 4.002898, k=300 ratio 4.006944,
45 orbits each, ~100-digit integer orbit coeffs (regenerate via `PYTHONPATH=. python3` over
`partitions_upto(7)` + `reduced_closed(orbs,K)` + the `ldl_inertia` witness). So `(R,c)` is ready;
only the FEASIBLE entry evaluation (A.2) is missing.

**No small-witness shortcut** (`tools/mk/subset.py`): greedy 31/45 orbits → 3.78; full 45 → 4.011.
Need ~all 45 orbits incl. the 3 essential img-4 orbits. ⇒ **A.2 (matchings closed form) is now the
gating step** — A.1 (filter-card hoist) is DONE but insufficient: the windowed table COUNT
(`~131072` per img-4 entry, k-independent), not the per-table cost, is the wall.

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

## C. Aristotle (status 2026-06-03)
- DONE+ported: `f84ef793` multinomialFast=Nat.multinomial (→ `MultinomialFast.lean`, kernel-clean);
  `656d6b54` card_filter_ofParts (→ re-proved in `SymmetricReductionOrbitFree.lean`).
- IN FLIGHT: `3591b35b` (`aristotle-multfold/`) — `multFold` (Finset.fold of binomials) =
  `Nat.multinomial`, a COMPUTABLE fast multinomial (resolves noncomputable `Finset.toList`). When it
  returns: verify kernel + `#print axioms`, port as `multC` into `gram*EntryWH`.
- NEXT candidate: the A.2 matchings-form bridge (`gramDenEntry a b = matchForm a b`) — the gating
  theorem. Architect as a self-contained combinatorial identity (table-sum = matchings-sum) with the
  formula above inlined. Hard; may need decomposition into sub-lemmas.
