# ROADMAP.md — Depth into the sieve

Written 2026-05-26. State at `master` commit `ff95d39` (PR #39 merged).

## Why this document exists

We've been counting sorries. Sorry count is a weak metric on this project
because **every `axiom` already hides what `sorry` makes visible**, and the
axiom-vs-sorry classification was inconsistent: some axioms were genuine
citations (Brun-Titchmarsh, EH, paper §3 numerical), others were "small
proofs we haven't gotten to" (`Mk_le_one_of_k_le_one`,
`MkSet_nonempty`/`bddAbove` sisters).

The reframe:

- **Axiom-by-citation is the contract, not the debt.** Citing
  Bombieri-Vinogradov, paper-§ numerical bounds, MIT exhaustive
  enumerations, or another formalization project's eventual results is
  normal mathematical practice. These stay axioms by design.
- **Axiom-as-"I owe you a proof" is `sorry`'s job, not `axiom`'s.** Using
  `axiom` for these inflates the trust base and lies to the metric.
- **Depth into the sieve is the real metric.** The actual mathematical
  content of Polymath8b is in §3 (sieve asymptotics). Discharging
  *those* axioms is the only thing that turns the project from a
  blueprint-with-citations into a verified result. Everything else is
  bookkeeping.

This file is a **falsifiable commitment**: tier-by-tier estimates of work,
with a measurement checkpoint in one month (2026-06-26) to compare
estimate vs actual.

## Current axiom inventory

**As of 2026-05-28 (post-PR #62)**: **37 axioms, 3 opaques, 15 sorries.**
**Pre-reclassification snapshot (when this doc was first written 2026-05-26)**:
45 axioms, 3 opaques, 15 sorries.

Net delta over the 2026-05-26 → 2026-05-27 session (PRs #39-#48):
- Axioms 45 → 35 (-10): 9 from Bucket B/C reclassification (PR #41),
  2 from Bucket A trim (PR #43, `SieveTheoreticArgument` + `parity_barrier`
  documentation-as-axiom removal), +1 new Bucket A citation
  (`mk_5_witness_under_EH`, PR #46).
- Sorries 15 → 19 (+4): 9 from reclassification, -5 from real
  discharges (`MkSet_truncated_bddAbove`, `MkSet_eps_nonempty`,
  `H1_le_12_under_EH`, `polynomialMaynardNumerator`,
  `polynomialMaynardDenominator`).
- Opaques 3 → 3 (unchanged). NB: Tier-1 *construction* work has since
  happened (PRs #52/#55/#56 encoded the full nuform ladder
  `lambdaTransform → selberg_nu_separable → selberg_nu_basis`), but no
  opaque is *discharged* yet — that awaits the s1/s2 interface decision.

Honest-debt sum (axioms + sorries + opaques): 63 → 57.
- -3 from documentation-as-axiom removal (PR #43).
- -3 from real discharges net of the +1 citation axiom (PRs #45-47).
- Reclassification (PR #41) was honest-debt-sum-neutral by design.

Classified into four buckets:

### Bucket A — Forever-axiom by design (31 axioms)

Citations to external truths. Discharging them is **not a goal**; they
stay axioms unless an upstream project lands a mathlib-importable version.

| Group | Count | Citation |
|---|---|---|
| `Prerequisites.EH`, `GEH`, `MPZ` (Props) | 3 | Polymath8b §2 |
| `BombieriVinogradov`, `GeneralizedBombieriVinogradov`, `MPZ_polymath8a` | 3 | BV-class; upstream of BKLNW / PrimeNumberTheoremAnd / Polymath8a; eventually `import`-able from a discharged mathlib |
| `Engelsma.tuple_5511_admissible` | 1 | MIT primegaps exhaustive enumeration |
| Paper §6 numerical Mk witnesses (50, 35410, 1649821, 75845707, 3473955908) | 5 | Polymath8b §6, `mke-lower` table |
| Paper §6 under-EH witnesses (54, 5511, 41588, 309661) | 4 | Polymath8b §6 under EH |
| Paper §6 under-GEH witnesses (3, 51) | 2 | Polymath8b §6 + Theorem `piece` (k=3) |
| Admissibility lower bounds (50, 51, 54) | 3 | MIT primegaps construction |
| Admissibility upper bounds (35410, 41588, 309661, 1649821, 75845707, 3473955908) | 6 | Polymath8b §10 constructive |
| `narrowness_asymptotic_{upper, lower}` | 2 | Polymath8b §10 asymptotics |
| `parity_barrier` | 1 | Polymath8b §7 |
| `SieveTheoreticArgument` (Prop → Prop wrapper) | 1 | Design-quirky; revisit |

**These should never count against the project's debt.** They're what
makes the proof a citation chain, like any normal math paper.

### Bucket B — Mis-classified: should be sorries (7 axioms) ✅ Reclassified 2026-05-26

"Small proofs we haven't gotten to." Using `axiom` here inflated the
trust base. **Done**: re-classified as `theorem ... := sorry` (PR #41).
Discharge proofs are still pending; see Tier 2 below.

| Axiom | File:line | Real cost |
|---|---|---|
| `Mk_le_one_of_k_le_one` | ✅ Done (PR #62) | k=0 (#42) + k=1 (#62, funUnique CoV + Jensen on $[0,1]$). |
| `MkSet_nonempty` | Sieve.lean:277 | 1-2 sessions. Smooth-bump witness. |
| `MkSet_bddAbove` | Sieve.lean:286 | 2-3 sessions. Polymath8b Cor `mk-upper`. |
| `MkSet_truncated_{nonempty, bddAbove}` | Sieve.lean:327, 333 | sisters of above |
| `MkSet_eps_{nonempty, bddAbove}` | Sieve.lean:432, 439 | sisters of above |

**Expected effect on metrics**: axioms 45 → 38, sorries 15 → 22, honest-
debt sum unchanged. The point is the metric stops lying.

### Bucket C — Substantive bookkeeping (2 axioms) ✅ Reclassified 2026-05-26

Real proofs, but mostly `Finset`/`Nat` bookkeeping rather than math.
**Reclassified as sorries** (PR #41): same logical category as Bucket B —
in-project proofs we owe, not citation contracts to external libraries
we can `import`. Size doesn't grant citation status. Discharge proofs
still pending (Tier 2 / Tier 3).

| Axiom | File:line | Cost |
|---|---|---|
| `DHL_gives_freq_primeAt_gap` | Basic.lean:724 | 5-15 sessions. ~200-line `Finset.count` translation. |
| `narrowness_realized` | Basic.lean:672 | 5-10 sessions. Hensley-Richards / Erdős $k$-tuple. |

### Bucket D — Sieve-core analytic (5 axioms + 3 opaques) — **the real math**

The actual content of Polymath8b §3. **This is the bar.** Discharging
*any* of these is the move that turns this project from a structural
blueprint into a real verification.

| Item | File:line | Polymath8b ref | Cost (confidence) |
|---|---|---|---|
| `selberg_nu` (opaque → real def) | Sieve.lean (`opaque selberg_nu`) | §3 eqns `nuform` (3.6)-(3.7) | construction DONE (#56 `selberg_nu_basis`); discharge = s1/s2 interface decision, ~1 session (80%) |
| `alphaBound` (opaque → real def) | Sieve.lean:82 | §3 eqn (s1) | 2-3 sessions (70%) |
| `betaBound` (opaque → real def) | Sieve.lean:88 | §3 eqn (s2) | 2-3 sessions (70%) |
| `wtrick_data` | Sieve.lean:594 | §3 W-trick lemma | 5-15 sessions (50%) |
| `s1_holds_from_nonprime_asym` | Sieve.lean:606 | §3 line 889 (i) | 10-30 sessions (40%) |
| `s2_holds_from_prime_asym_under_EH` | Sieve.lean:625 | §3 line 862 (i) + EH | 10-30 sessions (40%) |
| `s1_eps_holds_from_nonprime_asym` | Sieve.lean:761 | §5 epsilon-trick reduction | template sister of s1 (50%) |
| `s2_eps_holds_from_prime_asym_under_EH` | Sieve.lean:781 | §5 epsilon-trick + EH | template sister of s2 (50%) |

Confidence column reflects probability the cost lands in the stated
range; lower confidence on the (s1)/(s2) family because we don't yet
know which mathlib Mertens/PNT/divisor-sum lemmas exist vs need to be
added.

## Tier roadmap

Each tier is "interesting milestone outside this project." Estimated
cost is in *sessions* (one focused evening, 3-5 PRs in our observed
pace).

### Tier 1 — Encode the three opaques (5-8 sessions, 75% confidence)

- `selberg_nu`, `alphaBound`, `betaBound` → real `noncomputable def`s,
  citing Polymath8b §3 eqns (s1)/(s2)/`nuform` explicitly.
- **Milestone**: project's structural skeleton stops being self-citing.
  Every type is real except for the things we've axiomatized as paper
  citations.

### Tier 2 — Discharge structural-sorries (3-8 sessions, 85% confidence)

- ✅ Re-classify 7 mis-typed axioms (Bucket B) as `theorem := sorry` (#41).
- ✅ Discharge `Mk_le_one_of_k_le_one` (k=0 #42, k=1 #62 via Jensen on [0,1]).
- ✅ Discharge `MkSet_eps_nonempty` (#45) and `MkSet_truncated_bddAbove` (#42).
- Discharge `MkSet_nonempty` + remaining sisters (smooth-bump witness).
- Discharge `MkSet_bddAbove` + sisters (paper Cor `mk-upper`).
- **Milestone**: trust base shrinks 45 → 38 axioms. No more "axiom-for-
  things-we-could-prove" debt.

### Tier 3 — Discharge `wtrick_data` (5-15 sessions, 50% confidence)

- Mertens product asymptotic + CRT density. Mathlib has `ZMod`,
  `Nat.totient`, partial summation; gaps are likely in Mertens API.
- May require 1-3 upstream mathlib PRs for missing partial-summation
  lemmas.
- **Milestone**: first sieve-core axiom discharged. *Lean has touched
  the sieve.* This is the first place outside this room would care.

### Tier 4 — Discharge first (s1)/(s2) family member (10-30 sessions, 40% confidence)

- Pick the simpler of `s1_holds_from_nonprime_asym` or
  `s2_holds_from_prime_asym_under_EH`.
- Divisor-sum expansion + smooth ν asymptotic.
- Likely surface 3-5 missing mathlib lemmas (partial summation,
  divisor convolution, dominated convergence in specific shape).
- **Milestone**: a Polymath8b §3 main proof is real in Lean. *Publishable
  intermediate result.*

### Tier 5 — Discharge the rest of the sieve core (20-60 sessions, 30% confidence)

- ε and truncated sisters of (s1)/(s2): template clones if Tier 4 is
  cleanly templated; full re-derivation if each has wrinkles.
- **Milestone**: project sits on Bucket A (citation-only) axioms.
  *Real Lean verification of Polymath8b modulo paper-cited numerical
  bounds and BV/EH/GEH/MPZ as Props.*

### Tier 6 (out of scope for this project) — Discharge Bucket A citation axioms

- Wait for or contribute to BKLNW / PrimeNumberTheoremAnd / Polymath8a
  to land BV-class results in mathlib.
- Engelsma enumeration: `native_decide` on extended tuple search.
- Paper §6 numerical witnesses: re-derive in Lean or absorb from a
  different formalization project.

**This tier is explicitly not a goal of this project.** It's what
"verification of bounded gaps to the very foundations of mathematics"
would require, and that's a different project (probably several
different projects).

## Out-of-scope citation axioms (forever-axiom by design)

For clarity: items below stay `axiom` for the lifetime of this project
unless upstream projects (BKLNW, PrimeNumberTheoremAnd, mathlib's
analytic NT push) land discharges we can `import`.

- All `Prerequisites.*` (EH, GEH, MPZ, BV, GBV, MPZ_polymath8a)
- `Engelsma.tuple_5511_admissible`
- All `Polymath8b.mk_*_witness` (paper §6 numerical)
- All `Polymath8b.narrowness_*` (admissible-tuple bounds + asymptotics)
- `Polymath8b.parity_barrier`
- `Polymath8b.SieveTheoreticArgument` (revisit shape; design-quirky)

## Measurement protocol

**Checkpoint date**: 2026-06-26 (one month from today).

At the checkpoint:

1. Count sessions spent per tier (filling the ledger below).
2. Compare actual cost to estimate; update confidence intervals.
3. If tiers 1-2 are complete and tier 3 is in progress: estimate was
   roughly right.
4. If we haven't cleared tier 1: estimates were too aggressive;
   recalibrate the lower tiers before pushing higher.
5. If we've cleared tier 3: estimates were too conservative; the
   AI-pace leverage is higher than modelled.

## Session ledger (fill as we go)

Format: `YYYY-MM-DD | tier | what landed | session-equivalents (1.0 = full evening)`

| Date | Tier | What landed | Sessions |
|---|---|---|---|
| 2026-05-26 | 0 | This ROADMAP.md; PR-A1b-ii epsilon_beyond statement fix (PR #39); HANDOFF refresh PR #38 | 1.0 |
| 2026-05-26 | 2 (reclassification only) | Reclassify 9 mis-typed axioms → `theorem := sorry`: 7 Bucket B (`MkSet_nonempty`/`bddAbove` + ε/trunc sisters, `Mk_le_one_of_k_le_one`) + 2 Bucket C (`DHL_gives_freq_primeAt_gap`, `narrowness_realized`). Axioms 45→36, sorries 15→24, honest-debt unchanged. No discharges yet, metric just stops lying. (PR #41) | 0.2 |
| 2026-05-27 | 2 | `MkSet_truncated_bddAbove` discharged via `BddAbove.mono` + subset (`simplex_truncated k α ⊆ simplex k`, same value function). Routes through `MkSet_bddAbove`'s sorry; local body is real. Also extracted `Mk_zero_le_one` (new no-sorry theorem) and split `Mk_le_one_of_k_le_one` into `k=0` (discharged) + `k=1` (sorry, Cauchy-Schwarz future PR). Sorries 24→23 (real -1). (PR #42) | 0.2 |
| 2026-05-27 | A-trim | Removed `SieveTheoreticArgument` + `parity_barrier`: pure documentation-as-axiom, never consumed by any theorem. Pure trust-base shrink. Axioms 36→34 (-2), sorries unchanged. (PR #43) | 0.2 |
| 2026-05-27 | meta | HANDOFF refresh + ledger update (PR #44). | 0.1 |
| 2026-05-27 | 2 | `MkSet_eps_nonempty` discharged via shared F + `setIntegral_mono_set`. Added `simplex_isClosed` / `simplex_isCompact` reusable helpers. Sorries 23→22 (real -1). (PR #45) | 0.3 |
| 2026-05-27 | "new flagship" | Maynard k=5 chain: `tuple_5` admissibility (real, decide-based), `narrowness_5_le_12` (real, no axiom), `mk_5_witness_under_EH` (Bucket A citation), `dhl_5_2_under_EH` (real), `H1_le_12_under_EH` discharged. Sorries 22→21, axioms 34→35. (PR #46) | 0.4 |
| 2026-05-27 | "polynomial def bodies" | `polynomialMaynardNumerator` + `polynomialMaynardDenominator` real `noncomputable def`s with closed-form rational formulas; new `dirichletIntegralWithSlack` helper. Sorries 21→19 (real -2). Unblocks `polynomialMkF_eq_MkF` (~30 lines per TRIAGE). (PR #47) | 0.3 |
| 2026-05-27 | meta | HANDOFF refresh #48 — session wrap-up. | 0.1 |
| 2026-05-27 | "top-down flagship" | `maynard_trunc` discharged via new `selberg_sieve_data_truncated_from_F` sister of PR-A5; added 1 new MPZ-flavor (s2) cited axiom + 1 new extraction lemma; 4 truncated-Mk witness axioms updated to expose `0 < 1/4 + ϖ ∧ 0 < δ`. Sorries 19→18, axioms 35→36. (PR #49 / PR-A1b-iii-a) | 0.4 |
| 2026-05-27 | "top-down flagship" | `epsilon_beyond` discharged via new `selberg_sieve_data_beyond_from_F` sister of PR-A6; added 2 new beyond-flavor (s1, s2) cited axioms under GEH with `HasVanishingMarginal` rider. Sorries 18→17, axioms 36→38. (PR #50 / PR-A1b-iii-b) | 0.4 |
| 2026-05-27 | meta | HANDOFF + ROADMAP refresh #51 + scorecard against original predictions; whitespace cleanup of `1/4` → `1 / 4`. | 0.2 |
| 2026-05-28 | **Tier 1 (first brick)** | Real `lambdaTransform g R n := ∑ d∣n, μ(d)·g(log d/log R)` — the 1D Möbius-divisor operator under the `selberg_nu` nuform. + `lambdaTransform_{zero,one}`. First real piece of §3 sieve-core machinery; `selberg_nu` still opaque (basis-decomposition design choice deferred). (PR #52) | 0.3 |
| 2026-05-28 | "§1 combinator" | `hm_asymp_from_dhl_and_narrowness` discharged — real Filter/asymptotics proof (k_m = max(⌈Cdhl·exp(αm)⌉, m+1+k₀), IsBigO.bound, ℕ∞→ℝ≥0∞ coercion). Added `0 < α` hyp. Sorries 17→16. (PR #53) | 0.4 |
| 2026-05-28 | meta | HANDOFF + ROADMAP refresh #54. | 0.1 |
| 2026-05-28 | "Tier-1 construction" | `selberg_nu_separable` (#55, separable J=1 nuform) + `selberg_nu_basis` (#56, full general nuform eqn 837 over explicit basis) — both fully real from `lambdaTransform`, + nonneg/empty/single bridge lemmas. Nuform construction ladder complete; opaque `selberg_nu` not yet discharged (awaits s1/s2 interface decision). HANDOFF/ROADMAP refresh #57/#58. | 0.4 |
| 2026-05-28 | "lambda-algebra" | 6 real `lambdaTransform_*` lemmas (#59): `_prime` (g(0)−g(log p/log R)), `_prime_of_support` (paper eqn lambdan-prime), `_add`/`_smul`/`_neg`/`_linear`. Toolkit for the s1/s2 divisor-sum expansions. HANDOFF #60. | 0.3 |
| 2026-05-28 | **"Dig" round (Tier 2 + cleanup)** | Systemic consumption audit → dropped orphan axiom `narrowness_asymptotic_lower` (uses=0, **37 axioms**, #61); discharged `Mk_le_one_of_k_le_one` k=1 via `funUnique` change-of-vars + Jensen on [0,1] (**15 sorries**, #62, load-bearing for `H1_le_of_Mk_witness`). First metric moves since the flagship burst. | 0.5 |

#### Ledger gap 2026-05-28 → 2026-06-02 (reconstructed retroactively 2026-06-03)

The ledger went dark while the work pivoted to one big **off-roadmap thread**: discharge the
`Polymath8b.mk_*_witness` numerical axioms (ROADMAP Bucket A / Tier-6 "out of scope") by *proving*
`Mk k > 4` in Lean via a symmetric-reduction → orbit-basis Gram-quotient pipeline (branch
`path-a-selberg-nu`). Condensed arcs (session-weights are estimates; ~55 commits total):

| Date | Tier | What landed | Sessions |
|---|---|---|---|
| 2026-06-01/02 | **off-roadmap (Mk>4 build)** | Symmetric-reduction Gram pipeline: `orbitSum`→ cross-orbit denominator+numerator bilinear forms → orbit-free re-index over `MarginCorrectTables` → computable `gram*Entry` → `Mk_gt_four_of_symWeight_witness` / general-threshold `Mk_gt_of_symWeight_witness`; `disjoint_of_histogram` mechanizes the orbit-disjointness `hR`. `mk_54_witness_under_EH` reduced to data + 2 `native_decide`s. End-to-end `Mk 3 > 1` regression. | ~3.0 |
| 2026-06-02 | **off-roadmap (eps path)** | `SymmetricReductionEpsOrbitFree`: full ε-trick analog (eps-denominator + eps-numerator Gram, `affineSlackRat` marked-coordinate factorization, `pairOrbit_regroup` reused) → `mk_eps_50_witness` conditional discharge, axiom-clean. Both named flagships reduced to data + `native_decide`. | ~2.0 |
| 2026-06-03 | **off-roadmap (feasibility R&D)** | Discovered the committed `gram*Entry` table enumeration is `native_decide`-INFEASIBLE for real witnesses (`(k+1)^cells`). Built + measured 3 reformulations: margin-bounded (`gram*EntryBdd`), Fréchet-windowed (`gram*EntryW`, k-independent), filter-card-hoisted (`partsHist`, A.1). Empirically diagnosed the real wall = the windowed table COUNT itself (`~131072`/img-4 entry). Aristotle: `multinomialFast`, `card_filter_ofParts` ported. | ~2.0 |
| 2026-06-03 | **off-roadmap (A.2 matchings)** | The box-feasible route: matchings closed form (`matchDenForm`/`matchNumForm`, k-independent ~34-term sums, `#eval`-instant at k=300). Landed as defs + witness `Mk_gt_of_symWeight_witness_match` resting on 2 disclosed bridge axioms (numerically validated). `ofParts_inj`. | ~1.5 |
| 2026-06-03 (late) | **off-roadmap (bridge discharge)** | Both bridges turned from axioms into **theorems** (`c9cb696`/`8d46bcd`): all orbit-sum↔table-sum↔matchings plumbing discharged in-kernel, reducing the gap to 2 *atomic* combinatorial cores `denom_bridge`/`num_bridge` (numerically pre-verified, both submitted to Aristotle). Witness re-keyed on parts-lists `Mk_gt_of_symWeight_witness_match_parts` (`ef2b071`, capstone-feasible direct list-form quotient) + k=3 regression. | ~1.5 |

**Net on this thread:** the named numerical witnesses `mk_54_witness_under_EH` / `mk_eps_50_witness`
are reduced from opaque citations to `data + native_decide` resting on 2 atomic permanent/rook
identities (on Aristotle) + the witness `LCs` literal + one host-scale `native_decide`. This is
**Tier-6 work the ROADMAP deferred as out-of-scope** — so it's both ahead of stated scope (attacking
Bucket A) and orthogonal to Tiers 1–5 (which sat untouched: the 3 opaques are still opaque).

### Scorecard at ~10% of one-month horizon (2026-05-27 ~18:00, 20h post-ROADMAP)

| Tier | Estimate | Done so far | Comment |
|---|---|---|---|
| Tier 1 | 5-8 sessions | 0/3 opaques *discharged*; full nuform *construction* encoded (#52/#55/#56) | Construction done; discharge = s1/s2 interface decision next. |
| Tier 2 | 3-8 sessions | ~5 of ~7 items (#41/#42/#45/#62) | ~70% through. Ahead of pace. Remaining: `MkSet_nonempty`, `MkSet_bddAbove` + sisters. |
| Tier 3-5 | 5-60 sessions each | 0 | Expected (Tier 1 first). |
| Off-roadmap | n/a | 4/4 §5 flagships real | All Polymath8b §5 main theorems now compose through real analytic cores. Cost: +3 cited axioms in Bucket D. |

Pace matches model. The "off-roadmap" pattern (top-down vs bottom-up
ROADMAP) is the main delta — worth a tier-ordering reconsideration at
checkpoint.

(One row per work-unit. Tier 0 = scaffolding, planning, statement fixes
that don't discharge axioms. Tiers 1-5 = real depth-into-sieve progress.)

## Honesty disclaimer

This document was drafted by Claude (Ren) at Trevor's prompting after a
back-and-forth where Trevor pushed back on:

1. Mis-classifying "small proofs we haven't gotten to" as axioms
   (correct — that's a sorry).
2. The reflexive "this is a multi-year project, give up" framing
   (correct — the dependency chain is bounded and the AI-pace leverage
   shifts estimates 5-10x vs pre-2025 baselines).

The estimates above are honest first-pass guesses, anchored on observed
session-pace from May 2026 PRs (#34, #35, #37, #39). They will be
wrong. The measurement protocol exists so that "wrong" becomes
"measurable" rather than "vibes."

🪷
