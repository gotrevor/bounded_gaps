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

## Current axiom inventory (45 axioms, 3 opaques, 15 sorries)

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

### Bucket B — Mis-classified: should be sorries (7 axioms)

"Small proofs we haven't gotten to." Using `axiom` here inflates the
trust base. Cleanup pass: re-classify as `theorem ... := sorry`.

| Axiom | File:line | Real cost |
|---|---|---|
| `Mk_le_one_of_k_le_one` | Sieve.lean:294 | 1 session. Cauchy-Schwarz on $[0, 1]$. |
| `MkSet_nonempty` | Sieve.lean:277 | 1-2 sessions. Smooth-bump witness. |
| `MkSet_bddAbove` | Sieve.lean:286 | 2-3 sessions. Polymath8b Cor `mk-upper`. |
| `MkSet_truncated_{nonempty, bddAbove}` | Sieve.lean:327, 333 | sisters of above |
| `MkSet_eps_{nonempty, bddAbove}` | Sieve.lean:432, 439 | sisters of above |

**Expected effect on metrics**: axioms 45 → 38, sorries 15 → 22, honest-
debt sum unchanged. The point is the metric stops lying.

### Bucket C — Substantive bookkeeping (2 axioms)

Real proofs, but mostly `Finset`/`Nat` bookkeeping rather than math.

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
| `selberg_nu` (opaque → real def) | Sieve.lean:581 | §3 eqns `nuform` (3.6)-(3.7) | 1-2 sessions (80%) |
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

- Re-classify 7 mis-typed axioms (Bucket B) as `theorem := sorry`.
- Discharge `Mk_le_one_of_k_le_one` (smallest, Cauchy-Schwarz).
- Discharge `MkSet_nonempty` + sisters (smooth-bump witness).
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
