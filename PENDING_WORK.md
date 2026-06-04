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

**LANDED (committed `ca3d47f`):** the matchings-form DEFS + WITNESS are in
`SymmetricReductionOrbitFree.lean`: `matchData/matchDenSum/autParts/matchDenForm` (denominator),
`gWeight/matchDataN/matchNumSum/matchNumForm` (numerator), `#eval`/`native_decide`-INSTANT even at
k=300 img-4; numerically validated (`11/3360`, `7/2160` = the Lean spot-checks).

**LANDED 2026-06-03 (commits `c9cb696`, `8d46bcd`, `ef2b071`, `8a5a6ba`):** both bridges are now
**THEOREMS**, and the witness is re-keyed on parts-lists. The two A.2 pieces collapsed to:

1. **Bridges PROVEN modulo two atomic combinatorial cores.** `gramDenEntry_eq_matchDenForm` /
   `gramNumEntry_eq_matchNumForm` are no longer axioms — they're theorems. All surrounding plumbing
   is discharged in-kernel: `gramDenEntry = orbit-sum/(k+|α|+|β|)!` (`orbitPair_denominator_
   computable` ∘ `orbitPair_denominator_eq`), the numerator analog (`crossNumerator_orbitSum` ∘
   `orbitPair_numerator_eq` ∘ `numerator_combinatorial_factored`, `markedCellFactor_eq_gWeight`),
   `ofParts_degree` (= `L.sum`), and the `autParts>0` cancellation. The two **atomic** permanent/rook
   identities were `denom_bridge` / `num_bridge`. **STATUS 2026-06-03 (commits `b8fd8f5`, `d18ca93`):
   BOTH ELIMINATED as deep axioms.**
   - **`denom_bridge` — FULLY PROVEN (axiom gone).** Discharged via the **permanent route** (NOT the
     orbit-recursion P2 below). Define `permDenSum La Lb k = ∑_{ρ∈Perm(Fin k)} ∏ᵢ(ofParts La i +
     ofParts Lb(ρ i))!`. Then `lhs_eq_perm` (orbit double-sum·(k-|La|)!(k-|Lb|)! = k!·permDenSum, via
     the proven `ofParts_autParts_orbit_sum`) and `rhs_eq_perm` (matchDenSum·(...) = k!·permDenSum, by
     induction on `La`) share `permDenSum` and cancel. The hard core `permDenSum_laplace` (the inner
     perm-sum after `permDenSum_cons`/decomposeFin collapses to permDenSum on the column-removed list)
     was cracked via: swap↦succAbove perm bridge (`Fin.exists_succAbove_eq`), `permSum_perm_invariant`,
     and the EXACT identity `ofParts Lb ∘ Fin.succAbove j = ofParts (eraseIdx j)` (`ofParts_comp_succAbove`).
     Also `descFactorial_succ_eq'` (UNCONDITIONAL) makes `matchDenSum_cons_eq'` unconditional.
   - **`num_bridge` — FULLY PROVEN (axiom gone), incl. `matchNumSum_cons_eq'` (commit `6d8e23f`).**
     Same permanent route, ℚ-valued, with the extra `∑ᵢ gWeight(pᵢ,qᵢ)` factor. `permNumSum`,
     `permNumSum_cons` (`Fintype.sum_prod_type`), `permSum_gw_invariant`, `inner_num_eq`/`inner_den_eq`,
     `permNumSum_laplace` (j-row gWeight term splits into permDenSum + permNumSum), `lhs_num`,
     `rhs_num` (induction: IH for num + the proven `rhs_eq_perm` for den), `num_bridge`. The
     `matchNumSum_cons_eq'` recursion proved via unmatched/matched branch split + per-entry `weight_elt`
     + `matchDenSum_dataN` (helpers: `list_sum_flatMap`, `sum_range_eq_list`, `zip_range_eq_map`).
   - **`Mk_200_gt_4` is AXIOM-CLEAN: `[propext, Classical.choice, Quot.sound, native_decide]`** — NO
     mathematical axioms remain. The entire symmetric-reduction → Gram-quotient → matchings chain is
     kernel-proven (native_decide only for the concrete k=200 witness computation). NOTHING left to do
     here; the broader `bounded_gap_of_Mk_200` rests on cited analytic NT (§B) owned by another thread.
2. **Re-keying DONE** (`ef2b071`): `Mk_gt_of_symWeight_witness_match_parts (LCs : List (List ℕ × ℚ))`
   — the Gram quotient is the DIRECT list-form double sum `(LCs.map (fun la => (LCs.map (fun lb =>
   la.2·lb.2·matchForm la.1 lb.1 (n+1))).sum)).sum`; no 45-way `MultiIndex` match. Reduces to
   `…_witness_match` via `R = (LCs.map (ofParts∘fst)).toFinset` + noncomputable `partsInv`/`coefInv`
   (`ofParts` inj on `LCs` by `hnodup`; reindex via `List.sum_toFinset`×2). k=3 regression
   (`8a5a6ba`) fires the `native_decide` on the list-form quotient end to end.

(Superseded note — the OLD 2-pieces, for history:)
- ~~Prove the 2 bridge axioms (orbit-sum = matchings-sum, permanent/rook over `S_k`).~~ → now atomic
  `denom_bridge`/`num_bridge`, plumbing done, on Aristotle.
- ~~Re-key the witness on parts-lists / `Fin 45`.~~ → DONE (`…_witness_match_parts`). Measured prior:
   `Mk_gt_of_symWeight_witness_match` sums over `R : Finset (MultiIndex (n+1))` with `c, P` as
   functions on `MultiIndex` — evaluating `c a`/`P a` per summand requires a 45-way match over
   200-entry functions (`#eval` of the full witness CRASHED, code 134 / ~7e9 lookup ops). FIX: a
   variant `…_parts (Ls : List (List ℕ)) (cs : List ℤ) …` whose sum is `∑ i j, cs[i]·cs[j]·matchForm
   Ls[i] Ls[j] (n+1)` (DIRECT indexing, no `MultiIndex` matching), related to `∑ over R = (Ls.map
   ofParts).toFinset` (dedup + `ofParts` injectivity + orbit-disjointness from distinct parts-lists).
   This also subsumes the old "margin materialization" fix (margins `partsHist (n+1) Lᵢ`, Lᵢ in hand).

### The capstone payoff — ✅ DONE ON-BOX 2026-06-03 (commits 72f80c3, fff0e29)
**`BoundedGaps.OrbitFree.Mk_200_gt_4 : (4:ℝ) < Sieve.Mk 200`** is LANDED in
`BoundedGaps/MkWitness200.lean` (built by the default target, full build 8271 jobs). It instantiates
`Mk_gt_of_symWeight_witness_match_parts` with the exact k=200 D=7 witness `witnessLCs200` (45 orbits,
exact-LDL coeffs, rational Rayleigh quotient 4.002898). **First kernel-checked `M_k > 4`.**
`#print axioms Mk_200_gt_4 = [propext, Classical.choice, Quot.sound, native_decide]` (2026-06-03,
commit `6d8e23f`: both `denom_bridge` and `num_bridge` are now FULLY PROVEN theorems — NO
mathematical axioms remain; native_decide only for the concrete k=200 witness).

The companion **`bounded_gap_of_Mk_200`** feeds it into `Targets.H1_le_of_Mk_witness` →
`∃ H, Admissible H ∧ H.length = 200 ∧ liminfGap 1 ≤ diameter H` — the first **unconditional**
bounded-gap result in the repo (vs `Targets.H1_le_246`, which is conditional on the unproven
`Mk 50 > 4`). It rests on `[3 std, denom_bridge, num_bridge, BombieriVinogradov,
exists_separable_F_of_Mk_gt, s1/s2_holds_*, native_decide]` — the bridges + cited analytic NT only.

**❗ The "HOST-only / box OOMs" claim in every prior handoff was WRONG.** The failure was
`deep recursion at 'interpreter'` (interpreter stack used in native_decide/decide setup), NOT OOM.
Fix: `weakLeanArgs = ["--tstack=2000000"]` on `[[lean_lib]]` in `lakefile.toml` (weak ⇒ no full
rebuild). The matchings closed form is genuinely cheap; all three native_decides + two decides run
on-box in ~50s. **Do not re-assume host-only for heavy native_decide — bump tstack first.** When the
two bridge axioms land (Aristotle `0b5bf5be`/`9d05dbaa`), this is a fully kernel-clean (mod
native_decide) `M_200 > 4` → unconditional bounded gaps.

~~The numeric diameter in `bounded_gap_of_Mk_200` is the cheap factorial tuple's (`199·200!`).~~
**✅ GILDED 2026-06-04 (commit `60cd99c`).** `bounded_gap_of_Mk_200` now uses the explicit narrow
admissible 200-tuple `tuple200` (diameter **1304**, greedy residue-sieve, proven admissible via the
Engelsma `checkAdm` bundled-`native_decide` pattern). New: `liminfGap_one_le_1304 : liminfGap 1 ≤
1304` (the concrete H_1 bound) and `narrowness_200_le_1304 : H(200) ≤ 1304`. `Mk_200_gt_4` stays
axiom-clean; `bounded_gap_of_Mk_200` rests only on the 4 analytic-NT axioms (BV, exists_separable_F,
s1/s2) + native_decide.

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
- **`exists_separable_F_of_Mk_gt` — NARROWED 2026-06-04 to a single pure-density axiom.** Was a
  cited deep Polymath8b §6 polynomial-optimisation axiom (one of the 4 gating the UNCONDITIONAL
  `bounded_gap_of_Mk_200`). Now a THEOREM resting only on **`separable_dense_sup`** (sup-norm
  density of finite-separable smooth simplex-supported functions — pure approximation theory, NO
  number theory). The chain (all in `Sieve.lean`, axiom-clean except the lone density axiom):
  `exists_separable_F_of_Mk_gt` ⟸ `exists_F_of_Mk_gt` (proven `sSup` extraction) + `sep_approx`
  (now a theorem) ⟸ `mkF_sub_lt_of_sup_le` (the MkF-ratio sup-continuity, **fully kernel-clean**:
  num/den sup-continuity `mkF_{numerator,denominator}_sub_le_const` via `J_i_sub_le_const` /
  `Ji_integrand_integrableOn` + quotient rule) + `separable_dense_sup` (the density nut).
  `#print axioms exists_separable_F_of_Mk_gt = [propext, Classical.choice, Quot.sound,
  separable_dense_sup]`. **Truncated sister also narrowed** (`separable_dense_sup_truncated`, reuses
  the same continuity).
  - **ε sister FULLY DONE (2026-06-04):** (1) ported the continuity machinery to the ε-domains
    (`mkF_eps_sub_lt_of_sup_le` axiom-clean: `Ji_eps_integrand_integrableOn`, `J_i_eps_sub_le_const`,
    `mkF_eps_{num,den}_sub_le_const`; inner length `L=1+ε−∑s≤1+ε`, requires `0≤ε`), making
    `sep_approx_eps` a theorem; (2) then ELIMINATED the eps density axiom: `separable_dense_sup_eps`
    is a THEOREM reducing to base `separable_dense_sup` via the dilation `simplex_eps k ε =
    (1+ε)•simplex k` (`Measure.setIntegral_comp_smul_of_pos` Jacobian, `Module.finrank_fin_fun`).
    `epsilon_trick` now rests on `separable_dense_sup`, not a separate _eps axiom (Sieve axioms 11→10).
  - **REMAINING NUT — `separable_dense_sup`** (+ `_truncated`: per-coord cap `t i ≤ α`, so does NOT
    reduce by dilation — shares the same wall). The intended proof is the SEPARABLE box-tensor:
    `G(t) := ∑_{φ:Fin k→I} F(c_φ)·∏_i ρ_{φ(i)}(t_i)`, `{ρ_m}` a 1-D smooth partition of unity (mesh h).
    Two reusable in-kernel CORES landed this lap (axiom-clean): **`tensor_partition_of_unity`**
    (`∑_φ ∏_i ρ_{φ i}(t_i)=1` from a 1-D PoU, via `Fintype.prod_sum`) and **`isFiniteSeparable_tensor_sum`**
    (any finite tensor sum `∑_φ a(φ)∏g(φ i)(t_i)` IS `IsFiniteSeparable`, via `Fintype.equivFin`
    reindexing). With these, the separability + the `F−G=∑(F−F(c_φ))∏ρ` decomposition are in hand;
    the **residual hard piece** is purely analytic: "∃ a 1-D smooth PoU on ℝ, supp(ρ_m) in a width-h
    window, ∑_m ρ_m=1" + the modulus-of-continuity sup-bound + the support/smoothness assembly. That
    1-D PoU is a STANDARD, dimension-1, problem-independent fact (more elementary than the bespoke
    sieve density) — the right residual axiom if not fully closed. Attack paths: (a) build the 1-D PoU
    from `ContDiffBump` (mathlib `Analysis/Calculus/BumpFunction/`) by normalising a periodic bump sum;
    (b) **Aristotle** — job `c46a7778` (sepdense) grinding the base case (verify `#print axioms` on return);
    (c) Stone–Weierstrass + separable cutoff (heavier, support control is the snag).
- **Other Sieve bridges** `s1/s2_holds_from_*` (`Sieve.lean`): the GPY/Maynard asymptotic sieve
  sums. Deep analytic NT (leaf 1 = GPY port, paper-gated for the constant; see §Z).
- **`BombieriVinogradov`, `GEH`, `GeneralizedBombieriVinogradov`, `MPZ_polymath8a`**
  (`Prerequisites.lean`): genuine external analytic-NT inputs; cite-only until mathlib/PNT+ ships.
- **`narrowness_*_ge_*`** (Clark–Jarvis 2001 exhaustive enumeration) and **`narrowness_*_le`** for
  large `k` (Hensley–Richards constructions, `k` up to `3.5e9`): combinatorial, out of scope at
  scale. `narrowness_5511_le` is done (Aristotle-assisted `native_decide`).
- **`Zhang.H1_le_70M`** (`sorry`): Zhang's method-faithful GPY+MPZ sieve; result already free via
  `Polymath8b.H1_le_246`. Deferred.
- **`Polymath8b.twin_primes_or_near_miss_Goldbach`** (`sorry`): §8, weeks of work. Deferred.

---

## C. Aristotle (status 2026-06-04, lap ~05:40Z)

### 🏆🏆 GATE DISCHARGED — `∑μ²/φ = Θ(log N)` is now FULLY UNCONDITIONAL (commit `e8b00d7`).
Proved the prime-power tail bound `∑_{n≤N, IsPrimePow ∧ ¬Prime} Λ(n)/n ≤ 3` **from scratch**
(NOT via Aristotle — beat the `3f137191` job to it), discharging the last gate:
- `tail_eq_kge2`: `Chebyshev.sum_PrimePow_eq_sum_sum` regroups the tail as
  `∑_{k=2}^{⌊logN/log2⌋} ∑_{p≤⌊N^{1/k}⌋}(log p)/p^k` (filter-split off the k=1 primes).
- `tail_kge2_le ≤ 3`: **widen each k-slice's prime range to [2,N]** so the `k,n` ranges become
  independent → `Finset.sum_comm` (NO hard interdependent Fubini!) → `geom_tail_le`
  (`∑_{k≥2}n^{-k} ≤ 1/(n(n-1)) ≤ 2/n²`) → `sum_log_div_sq_le` (`∑(log n)/n² = O(1)`, integral cmp).
- `prime_power_tail_le_three`, then UNCONDITIONAL: `mertens_prime_log_two_sided`
  (`|∑(log p)/p − logN| ≤ log4+7`), **`mertens_theta_log`** (`log N ≤ ∑μ²/φ ≤ exp(1+D)·log N`),
  `mertens2_two_sided` (`∑1/p = loglog N + O(1)`, coeff 1). ALL `#print axioms` clean, no sorry.
- **Aristotle `3f137191` (pptail, proving `≤ 1`) is now SUPERSEDED** — `≤ 3` suffices for O(log N).
  If it returns `≤ 1` it only tightens constants (log4+7 → log4+5); not needed. Free the slot for
  the next rung when it finishes.
- **NEXT RUNG (new top priority):** connect `mertens_theta_log` to the GPY singular-series
  asymptotic that gates `s1_*_holds_from_nonprime_asym` in `Sieve.lean` (the actual consumer).
  Big jump — needs sieve context; read `ANALYTIC_AXIOM_BURNDOWN.md` + Sieve.lean s1 statement.

### EARLIER THIS LAP (~04:30–05:00Z, 11 commits `12e307e`…`f779d0c`, all axiom-clean):
**The ENTIRE sharp chain to the headline `∑μ²/φ = Θ(log N)` is now BUILT, reduced to a SINGLE
remaining gate: `prime_power_tail_le` (in flight `3f137191`).** New in `BoundedGaps/Mertens.lean`:
- `vonMangoldt_split_prime`: `∑Λ(n)/n = ∑_{p≤N}(log p)/p + (proper-prime-power tail)`.
- `mertens_prime_log_two_sided_of` (+`_upper_of_tail`): tail≤1 ⇒ `|∑(log p)/p − log N| ≤ log4+5`.
- **Sharp Mertens 2nd, BOTH halves (coefficient 1):** `mertens2_abel` (2nd Abel identity, weight
  `1/log n`), helpers `log_telescope_eq/_le`, `leading_term_bound/_ge`, `reindex_inv_log`,
  `leading_sum_bound/_ge`, `sum_one_div_n_log_n_ge`; `mertens2_upper_of`/`mertens2_lower_of`
  (`A_n = log n ± C ⇒ ∑1/p = loglog N ± O(1)`); `mertens2_two_sided_of_tail` (bundled textbook
  `∑1/p = loglog N + O(1)` conditional on tail).
- **Headline:** `prime_idx_eq`, `prod_euler_le_exp` (`∏(1+1/(p-1)) ≤ exp(∑1/(p-1))`),
  `euler_exponent_le` (`∑1/(p-1) ≤ ∑1/p+1`), `mertens_upper_of` (`∑μ²/φ ≤ exp(1+D)·log N = O(log N)`),
  `mertens_theta_log_of_tail` (two-sided `Θ(log N)` ⟸ tail). **All ONE `exact` from unconditional.**
- **mathlib unlock for the tail:** `Chebyshev.sum_PrimePow_eq_sum_sum` IS the prime-power regrouping
  `∑_{n≤x, IsPrimePow} f(n) = ∑_{k=1}^{⌊log x/log2⌋} ∑_{p≤x^{1/k}} f(p^k)` — confirms the tail is
  tractable (k=1 slice = primes; tail = k≥2 slices). Aristotle has the right tool.

### THE ONE REMAINING GATE: ✅ DISCHARGED (see above) — `prime_power_tail_le_three` is real.
- `3f137191` (pptail `≤ 1`) superseded; the conditional `*_of_tail` theorems remain as documentation
  of the dependency structure but are no longer needed (unconditional versions exist).
- **🎉 SHARP MERTENS 1st LANDED this lap** (`7412132`): `mertens_vonMangoldt_two_sided`
  `|∑_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4` — the **coefficient-1** estimate. Built from
  `vonMangoldt_hyperbola` (Aristotle `cc0dfbaf`), `sum_log_le`/`le_sum_log` (Stirling via mathlib
  `integral_log`), `cast_div_le_self`/`sub_one_le_cast_div` (floor), and **mathlib's
  `Chebyshev.psi_le_const_mul_self`** (`ψ(N) ≤ (log4+4)N` — the hard ψ≤CN bound is ALREADY in
  mathlib's `Mathlib/NumberTheory/Chebyshev.lean`!). `mertens_vonMangoldt_lower`/`_upper` are the halves.
- **REMAINING sharp chain → headline `∑μ²/φ = Θ(log N)`:**
  1. prime-power tail (in flight `3f137191`) ⇒ **sharp** `∑_{p≤N}(log p)/p = log N + O(1)`.
  2. **sharp Mertens 2nd** `∑_{p≤N} 1/p = log log N + O(1)` (coefficient 1): 2nd Abel step on the
     SHARP `∑(log p)/p` via `abel_summation_identity`. ⚠️ NOTE: `mertens_second_term_bound` is for the
     CRUDE route (bounds `(1+log n)(…)` wholesale → coeff `1+1/log2`). For coeff-1, SPLIT
     `A_n(1/log n − 1/log(n+1)) = log n·(…) + (A_n − log n)·(…)`: leading `log n·(1/log n−1/log(n+1))`
     sums to `log log N + O(1)` (coeff 1, via `sum_one_div_n_log_n_le`), remainder `(A_n−log n)·(…)`
     is `O(1)·∑(1/log n − 1/log(n+1))` which TELESCOPES to `O(1)`. Needs sharp `A_n = log n + O(1)`.
  3. `∑_{p≤N} 1/(p−1) ≤ ∑1/p + 1` (`prime_tail_le`, landed) + `1+x≤eˣ` ⇒ `∏(1+1/(p−1)) = O(log N)`
     (now coeff-1 ⇒ genuine `O(log N)`, NOT the crude `(log N)^3.4`) ⇒ `∑μ²/φ = O(log N)` ⇒
     two-sided `Θ(log N)` with `mertens_lower`.
- **LANDED THIS LAP (17 commits `a2e4c60`…`7412132` on `path-a-selberg-nu`, all axiom-clean,
  full build green 8272 jobs):** the complete 1D-analytic toolkit in `BoundedGaps/Mertens.lean`:
  - sharp Mertens 1st: `vonMangoldt_hyperbola`, `sum_log_le`, `le_sum_log`, `cast_div_le_self`,
    `sub_one_le_cast_div`, `mertens_vonMangoldt_lower/_upper/_two_sided`.
  - `mertens_prod_upper`/`mertensSummand_eq_prod` (`∑μ²/φ ≤ ∏(1+1/(p-1))`), proved locally.
  - `chebyshev_theta_le`/`chebyshev_theta_le'` (`θ(N) ≤ N·log 4`, plain + indicator form).
  - `abel_div_le` (Aristotle `32baa99f`, weight `1/n` summation-by-parts) + `mertens_first_le`
    (`∑_{p≤N}(log p)/p ≤ log4·(1+log N)`) + `mertens_first_le'` (indicator form).
  - `telescope_tail_eq/le`, `prime_tail_le` (`∑_{p≤N}(1/(p-1)−1/p) ≤ 1`).
  - `hasDerivAt_log_log`, `continuousOn/antitoneOn_one_div_x_log_x`, `integral_one_div_x_log_x`
    (FTC: `∫_2^N 1/(x log x)=log log N−log log 2`), `sum_one_div_n_log_n_le` (sum-integral comparison).
  - `abel_summation_identity` (Aristotle `431512dd`, GENERAL-weight summation-by-parts).
  - `mertens_second_term_bound` (`(1+log n)(1/log n−1/log(n+1)) ≤ (1+1/log2)/(n log n)`).
- **⚠️ KEY INSIGHT (sharp vs crude).** The `abel_div_le`-based route gives Mertens 1st with a LOSSY
  `log 4 ≈ 1.386` coefficient (from Chebyshev `θ≤N log4`), so the second Abel step yields only
  `∑1/p ≤ C·log log N` with NON-SHARP `C = log4·(1+1/log2) ≈ 3.4`. Exponentiating gives
  `∑μ²/φ = O((log N)^{3.4})`, **NOT** the sharp `Θ(log N)`. The two-sided `∑μ²/φ ~ log N` (needed
  for sub-step (c)'s main term) requires the SHARP Mertens 1st `∑(log p)/p = log N + O(1)`
  (coefficient exactly 1), via the von Mangoldt / `log(N!)` / Stirling route — hence the `cc0dfbaf` job.
- **NEXT bricks — two tracks:**
  - **(crude, ~80 lines, OPTIONAL milestone)** Assemble qualitative **Mertens 2nd** `∑_{p≤N}1/p = O(log log N)`
    from the landed pieces: `abel_summation_identity` with `a k=[k prime](log k)/k`, `w k=1/log k`
    (⇒ `a k·w k=[k prime]/k`); `A_n` bounded by `mertens_first_le'`; split off n=1 (A₁=0, junk weight);
    bound the difference-sum termwise via `mertens_second_term_bound` then `sum_one_div_n_log_n_le`
    (mind the `Icc 2 (N-1)` vs `Ico 2 N`/`n=3..N` index shift, +`1/(2log2)` for the n=2 term).
    Famous theorem, but non-sharp constant — does NOT give the headline `∑μ²/φ=Θ(log N)`.
  - **(SHARP, the real headline path)** von Mangoldt route: `vonMangoldt_hyperbola` (in flight) →
    Stirling `N log N−N+1 ≤ ∑_{m≤N}log m ≤ N log N` (use mathlib `integral_log` +
    `MonotoneOn.integral_le_sum`; ALL tooling present) → `⌊N/n⌋=N/n−frac`, ψ(N)=∑Λ(n)≤C·N
    (Chebyshev) → `∑Λ(n)/n = log N + O(1)` → drop prime-power tail (`∑_{k≥2}(log p)/p^k` converges)
    → SHARP `∑(log p)/p = log N+O(1)` → sharp Abel (reuse `abel_summation_identity`) → `∑1/p=log log N+O(1)`
    → `∑μ²/φ = Θ(log N)`. mathlib has `ArithmeticFunction.vonMangoldt_sum`, `vonMangoldt_apply_prime`,
    `vonMangoldt_le_log`, `Stirling.le_log_factorial_stirling`.
- **DONE+ported 2026-06-04 — `6c45fd6b` `mertens_crux`** (the analytic on-ramp's nut): returned
  sorry-free, verified + ported into `BoundedGaps/Mertens.lean` as part of `mertens_lower`
  (`log N ≤ ∑ μ²/φ`), `#print axioms = [propext, Classical.choice, Quot.sound]`. One `grind`
  regression (radical(p^k)=p) hand-fixed; mathlib v4.29.1 DOES have `radical`.
- **DONE+ported (earlier): the two bridge cores.** `0b5bf5be` denom_bridge, `9d05dbaa` num_bridge —
  both eliminated (handoff `d977260`); `Mk_200_gt_4` axiom-clean.
- DONE+ported (earlier): `f84ef793` multinomialFast (→ `MultinomialFast.lean`); `656d6b54`
  card_filter_ofParts (→ re-proved). `3591b35b` multfold = dead path (enumeration abandoned).
- After both bridges land: the ONLY remaining gap to a kernel-checked `Mk 200 > 4` is the heavy
  capstone `native_decide` on `Mk_gt_of_symWeight_witness_match_parts witLCs … ` — likely HOST-only
  (2025 matchForm terms, 214! factorials; box OOMs). The witness `LCs` literal still needs to be
  generated from `tools/mk/_ldl.py` (k=200 D=7, 45 orbits) and `#eval`-checked > 4 (fast, computable).
- **NEW — analytic-NT burn-down track (2026-06-03), for the fleet to pick up in due course:**
  `6c45fd6b-3757-4a2c-87ba-059478d10cff` (`mertensSummand`/`mertens_crux`) — the entry lemma for the
  s1/s2 sieve-asymptotic burn-down: `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)` (radical-fiber/Euler-product
  rearrangement; mathlib has no `radical:ℕ→ℕ` nor `∑∏=∏∑` over `primeFactors`). On return: verify
  in-kernel + `#print axioms` (Aristotle pins v4.28; we're v4.29.1), then it discharges the lone
  real `sorry` in the skeleton `scratch_mertens.lean` (repo root, untracked, typechecks — the endpoint
  `log N ≤ harmonic N` already compiles via `log_le_harmonic_floor`). **Full map of why this matters and
  the whole analytic-axiom ladder (BV / Large Sieve / s1/s2 / PNT) is in `ANALYTIC_AXIOM_BURNDOWN.md`.**
  A NEW, EH-free, weeks-scale on-ramp — independent of the `Mk` main thread above.

---

## Z. Analytic-NT burn-down thread (s1/s2 via weighted Mertens) — added 2026-06-04 PM

Separate from the numerical `Mk` endgame above. State after this lap: front #4 (1-D weighted
Mertens) **reduced to ONE analytic axiom**; 8 axiom-clean lemmas + full Abel reduction in
`BoundedGaps/WeightedMertens.lean`. Build green (8276 jobs).

### Open items (this sub-thread)
- **`WeightedMertens.riemann_sum_log_weight`** — the ONLY axiom under `weighted_mertens`. Pure
  real-analysis Riemann-sum limit `(∑_{2≤n≤N}F(log n/log N)/n)/log N → ∫₀¹F`.
- **`Sieve.s1_holds_from_nonprime_asym`**, **`s2_*`** — multidimensional generalization of weighted
  Mertens (the genuine multi-month nut: singular series + simplex integral).
- **`Sieve.exists_separable_F_*`** — near-optimal separable `F` (Polymath8b §5-6).
- **`Prerequisites.geh_implies_eh`** (`sorry`) — needs GEH body + Vaughan's identity; deep-deferred.

### Three attack paths each

**`riemann_sum_log_weight` (ONE lap from front #4 being axiom-free):**
1. PORT Aristotle `930e468a` (`aristotle-wmertens/`); statement is byte-identical → paste body
   under our axiom name; `#print axioms` to catch v4.28→v4.29 `sorryAx`.
2. Local monotone special case via `Analysis/SumIntegralComparisons`
   (`sum_mul_Ico_le_integral_of_monotone_antitone`, weight `1/n` antitone), squeeze; extend to C¹
   `F` via `F=∫F'` BV decomposition.
3. Substitution `∫_2^N F(log t/logN)/t dt = log N·∫_{log2/logN}^1 F` (CoV moved in v4.29.1 →
   `integral_image_eq_integral_abs_deriv_smul`) + sum-vs-integral error killed by
   `weighted_avg_majorant_tendsto_zero`.

**`s1_holds_from_nonprime_asym` (multidimensional lift):**
1. STATE the k-dim weighted Mertens (Polymath8b §3 sfg-1/lflg): `sieveSum(selberg_nu)` → k-fold
   product of 1-D weighted sums × singular series `𝔖`; `weighted_mertens` is the 1-D factor.
2. Build `𝔖(H)` as a convergent Euler product (reuse `SharpMertens` `eulerProduct_tprod` machinery);
   finiteness + positivity = the `alphaMainTerm` normalization.
3. Separable rank-1 (`J=1`, `F=∏F_i`) case first → `sieveSum` factors, each factor is exactly
   `weighted_mertens`; then `IsLittleO` glue (sub-step (d)); generalize by linearity over `∑_j c_j∏_i`.

**`s2_*`:** mirror s1 with `θ(n+h_i)` on one coordinate (EH/MPZ supplies level of distribution);
only structural diff is the `ϑ/2` (resp `1/4+ϖ`) normalization (Polymath8b §3 theta-oo). Do s1 first.

**`exists_separable_F_*`:** (a) explicit Bernstein/polynomial witness + numeric Rayleigh
(`SievePolynomial`); (b) Stone–Weierstrass density of tensor polynomials on the simplex; (c) extract
near-optimal separable witness from the `MkSet_bddAbove` sup definition.

### Next-lap pointer
item 1/P1 DONE (`riemann_sum_log_weight` ported, front #4 axiom-free). Sub-step (c) **algebra**
now also DONE — `SieveExpansion.lean` has the GPY diagonalization ladder (all axiom-clean,
2026-06-04 continuation): `gpy_diagonalize` (`∑_{d,e}w(d)w(e)/[d,e]=∑_r φ(r)(∑_{r∣d}w(d)/d)²`),
`gpy_diagonalize_moebius` (the `w=μ·g` sieve form = per-coordinate quadratic form in the expansion),
`gpy_yvar_substitution` (`y_r=(μ(r)/r)·∑_{(r,s)=1}μ(s)g(rs)/s`), `gpy_quadform_nonneg` (PSD).
Sub-step (c) ALGEBRA LADDER now COMPLETE (8 axiom-clean commits this lap): also added
`gpy_diagonalize_moebius_squarefree`, `gpy_yvar_eq_zero_of_not_squarefree`,
`gpy_diagonal_asymptotic_form` (canonical capstone `∑μμgg/[d,e]=∑_{r sf}(φ(r)/r²)z_r²`),
`piFinset_lattice_main_factor` + `heuristic_main_term_diagonalized` (heuristic main = `M·∏ᵢ`
diagonalized form), and the (s1) REDUCTION `sieveSum_separable_eq_heuristic_add_correction`
(`sieveSum = heuristic_main + correction`). The whole algebra of sub-step (a)→(c) is machine-checked.
**Three purely-analytic obligations remain** (see ANALYTIC_AXIOM_BURNDOWN.md tail): (1) the
diagonal-sum asymptotic `∑_{r sf}(φ(r)/r²)z_r²→const` (smooth core = Aristotle `3e2b6a8d`); (2) the
correction bound `∑_P coeffₚ(countₚ−M/∏[Pᵢ])=o(main)` via the W-trick discharge
(`lattice_count_offdiag_vanish_Wtrick`) + diagonal `O(1)` error (`lattice_count_main_term`) with
`M=(B−A)/W`; (3) sub-step (d) `IsLittleO` glue into `alphaBound`. Reusable analytic bricks in
`WeightedMertens.lean`: `weighted_cesaro_tendsto_zero`, `weighted_avg_majorant_tendsto_zero`,
`harmonic_div_log_tendsto_one`, `sum_log_mul_log_diff_le_sq`, `Bdisc`/`discrepancy_*`, `abel_tail_*`,
`weighted_mertens_of_riemann`, `weighted_mertens_of_contDiff`.

**UPDATE 2026-06-04 lap N+1 (commits `af0a3e6`…`e8dd497`, 8 axiom-clean, build green 8277):**
The CROSS-TERM (`j≠j'`) algebra is now also done (prior lap was single-`F` diagonal only), and a
**Cauchy–Schwarz collapse** reduced the main-term obligation to the DIAGONAL block alone. New in
`SieveExpansion.lean`: `gpy_diagonalize_bilinear`/`_moebius_bilinear[_squarefree]`/
`gpy_diagonal_asymptotic_form_bilinear` (cross diagonalization ladder); `sieveDivisors_pos`/
`_dvd_closed`; `heuristic_main_selberg_nu_canonical` (FULL `selberg_nu` main term in canonical
`∑_{j,j'}cⱼcⱼ'M∏ᵢ∑_{r sf}(φ/r²)z₁z₂` form); `correction_weight_factor[_split]` (correction weight →
∏ of 1-D Möbius sums — but LOOSE, see burndown); **`gpy_bilinear_cauchy_schwarz`**
(`B(g₁,g₂)²≤B(g₁,g₁)B(g₂,g₂)` ⟹ cross blocks auto-bounded by the diagonal). **Net: `s1` now needs
only the SINGLE diagonal limit `∑_{r sf}(φ/r²)z_r²→I(F)` (Aristotle `weighted_riemann_2d`, in
flight) + off-diag-main `o(main)` + `∑_{diag}|coeff|` size bound + `IsLittleO` glue.** Diagonal
`O(1)` error already wired via `lattice_count_main_term` → `diag_error_bound`. Full map in
`ANALYTIC_AXIOM_BURNDOWN.md` tail.

### UPDATE 2026-06-04 lap N+2 (commits `691a239`,`3a3dbef`,`e7dc3ae`,`8f55d07`; build green 8277)
**Leaves (2) and (4) of `s1_holds_from_nonprime_asym` are now DONE in-kernel.** Cauchy–Schwarz
(prior lap) had collapsed the main term to the diagonal, leaving 4 analytic leaves. This lap closed
two of them:
- **Leaf (2) `∑_{diag}|coeff|=o(main)` — DONE.** `SieveExpansion.hyperbola_count_le` proves the
  k-dim Dirichlet count `#{d∈[1,N]^k:∏dᵢ≤N} ≤ N(1+log N)^{k-1}` fully in-kernel (was queued for
  Aristotle; no longer needed there). Induction on k + `Fin.cons`/`Fin.tail` `card_bij'` fiber
  bijection + `harmonic_le_one_add_log`. Bridge `lattice_count_le_hyperbola` + capstone
  `diagonal_weight_le_hyperbola` give `∑_{diag}|coeff| ≤ C²⌊R⌋₊(1+log⌊R⌋₊)^{k-1}`. Residual: the
  parameter tail `R=o(M log R)` (GPY plumbing, not analysis).
- **Leaf (4) `IsLittleO` glue — DONE (modular chain).** `Sieve.alphaBound_of_sub_littleO`/
  `betaBound_of_sub_littleO` (positive-part `max(f,0)=O f` ⟹ two-sided diff o(main) suffices) +
  `alphaBound_of_heuristic_correction`/`betaBound_of_heuristic_correction` (split `sieveSum=Aheur+Bcorr`;
  heuristic limit + correction bound ⟹ alphaBound). Machine-checks `leaf 1 ∧ leaf 3 ⟹ s1`.

**s1 remaining nuts:**
1. **Leaf (1) diagonal asymptotic** `∑_{r sf}(φ(r)/r²)z_r² → I(F)·const`. **SMOOTH CORE CLOSED
   (lap N+3, commit `68e9eb0`, axiom-clean):** the 2-D simplex limit
   `InnerUniformReduction.weighted_riemann_2d` is PROVEN UNCONDITIONALLY in-kernel (all of `psi_tendsto`
   + the Pólya reduction chain machine-checked; the 3 Aristotle leaf-1 jobs cancelled as redundant).
   **REMAINING for leaf 1 = the GPY port (multi-lap, the new frontier):** connect
   `gpy_diagonal_asymptotic_form`'s output `∑_{r sf}(φ(r)/r²) z_r²` (with `z_r=∑_{(s,r)=1}μ(s)g(rs)/s`,
   `g(d)=F(log d/log R)`) to the `weighted_riemann_2d` double-sum shape. Three attack paths:
   (a) expand `z_r² = ∑_{s,s'}μ(s)μ(s')g(rs)g(rs')/(ss')`, swap to `∑_{s,s'}(…)∑_{r}(φ(r)/r²)[r∣…]`,
   recognise the inner `r`-sum as the singular series `𝔖`; (b) rank-1/separable case first (single
   coordinate, `F=∏Fᵢ`) to validate the shape before the general `J`-basis; (c) reuse `SharpMertens`
   `eulerProduct_tprod` for the `𝔖(H)=∏_p(1-ν_p/p)(1-1/p)^{-k}` Euler product. NB this port consumes
   the now-proven `weighted_riemann_2d` as a black box — design carefully (needs the GPY paper).
2. **Leaf (3) off-diagonal heuristic main = o(main)** = `M·∑_{¬diag}w_P/∏[Pᵢ] = o(M(log R)^k)` (the
   phantom main over W-trick-incompatible tuples whose actual count is 0). Infra:
   `correction_abs_bound` already routes the correction to exactly (leaf 2 diag weight) + (this
   off-diag main). Attack: singular-series discrepancy + W-trick prime gain; needs `W=∏_{p≤D₀}p`,
   `M=(B−A)/W`, `R=x^{θ/2}` parameter plumbing. NOT a clean isolated lemma — coupled to 𝔖(H).

### Witness-axiom thread — feasibility probe result (2026-06-04 lap N+2)
Probed discharging `mk_54_witness_under_EH` (needs `Mk 54 > 4`) via the `Mk_gt_of_symWeight_witness_match_parts`
+ explicit symmetric witness route (as `Mk_200_gt_4` does). **Riskiest assumption FAILS:**
`tools/mk/gen_witness7.py` (degree D=7) sweeps K≥160 and prints "no positive pivot (M_K≤4)" for
small K — i.e. a degree-7 symmetric witness does NOT reach 4 at k=54 (the achievable Rayleigh bound
grows with k; k=200 is near the deg-7 threshold). To get `Mk 54 > 4` (true value 4.00238, Polymath8b)
needs a HIGHER-degree witness (D≥8 ⟹ much larger Gram `native_decide`) AND still rests on the
`denom_bridge`/`num_bridge` realizability axioms (the central gap, on Aristotle). So this thread is a
heavy multi-lap lift, not a clean lap win. Same applies a fortiori to `mk_5511`(>6)/`mk_41588`(>8)/etc.
(higher thresholds). Conclusion: the `mk_*_witness` axioms are gated on the bridge axioms + a
higher-degree witness pipeline; defer until the bridge axioms land. Monotonicity of `Mk` does NOT help
(k<200 witnesses need k-specific constructions; k>200 ones need thresholds >4).

### Leaf (1) DECOMPOSED — 2-D simplex limit reduced to inner uniform convergence (lap N+2, commit `9206855`)
`BoundedGaps/WeightedRiemann2D.lean` (axiom-clean, build green 8278): the deep leaf-1 nut (the 2-D
weighted Riemann limit `weighted_riemann_2d`) is PROVEN modulo a single clean ingredient. Proved
in-kernel: `phi_continuousOn` (Φ_G continuous), `perturbed_riemann` (the MAIN+ERROR perturbed
Riemann core — if `a R m → Φ` uniformly in m, the a-weighted log-sum → ∫₀¹F·Φ), `two_d_factor` (the
double sum factors), `weighted_riemann_2d_of_inner` (capstone). **Remaining = `inner_uniform`**:
`(∑_{n≤R/m}G(log n/log R)/n)/log R → ∫₀^{1-log m/log R}G` uniformly in m∈[2,R]. Three attack paths:
1. **Aristotle** — `aristotle-inner-uniform/Problem.lean` is WRITTEN & typechecks (statement +
   `riemann_sum_log_weight` axiom + split-at-`R^{1-δ}` proof sketch). Submit when the current 2-D
   slot frees, OR immediately if the monolithic `weighted_riemann_2d` (`3e2b6a8d`) fails.
2. **Local split proof** — `m∈[2,R^{1-δ}]`: `R'=⌊R/m⌋≥R^δ→∞`, uniform Riemann via equicontinuity of
   `u↦G((1-s)u)` (G unif. cont. on compact [0,1]); `m∈(R^{1-δ},R]`: `1-s<δ` so sum and integral both
   `O(δ)`. Take δ from ε then R large. The scale-change `inner/logR=(1-s)·(∑G((1-s)·)/n)/logR'` +
   `riemann_sum_log_weight` on `G_s(u)=G((1-s)u)` gives the pointwise piece.
3. **Harvest the monolithic 2-D** — if `weighted_riemann_2d` (`3e2b6a8d`) returns, port directly
   (don't even need the decomposition for the port; the decomposition stays as a cleaner proof/hedge).
Then: connect `weighted_riemann_2d` to the repo's `gpy_diagonal_asymptotic_form` (the Selberg-diagonal
↔ double-Riemann GPY manipulation) — the remaining port step for leaf (1).
