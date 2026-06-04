# Handoff: bounded_gaps — OFFLINE CEILING reached (corrects the 0530 "chase numerics" plan)

**Date**: 2026-05-31 ~04:05 UTC · **Branch**: `path-a-selberg-nu` · **HEAD** `0687c32` (tree clean, 14 local commits — host must push). **Supersedes the "Next actions" of `HANDOFF-SESSION-2026-05-31-0530.md`.** The bridge work in 0530 stands and is correct; only its forward plan is corrected here.

## TL;DR
The polynomial-witness bridge (`polynomialMkF_eq_MkF`, `Mk_gt_four_of_polynomial_witness`) is **done and axiom-clean** `[propext, Classical.choice, Quot.sound]` — real achievement, keep it. **But every remaining leaf of the formalization is walled for an offline (lean-yolo-box) session.** "Chase the §6 numerics for H1 ≤ 240" is *not* a tractable next action — it rests on a mistake. Verdict below was read from source this session, not assumed.

## Why "chase the numerics for H1 ≤ 240" is the wrong target

1. **`H1 ≤ 240` requires `Sieve.Mk 49 > 4`, which is OPEN MATHEMATICS.** Not a computation. `Targets.lean:120-128` ("The wall, honestly") already records it: Polymath8b tried symmetric polynomials to degree 23 and **could not** push M₄₉ past 4; 11 years, nobody has. The *published* result is `H1 ≤ 246` via `Mk 50 > 4` (`Targets.H1_le_246`) — that, not 240, is the real ceiling target.

2. **Even `Mk 50 > 4` is computationally infeasible in the current representation.** `PolynomialSieveWeight` stores `terms : Finset (MultiIndex k × ℚ)` — *individual* monomials. Polymath8b's witness is a symmetric polynomial of degree ~23 in 50 variables → ~10¹³ individual monomials when expanded, and `polynomialMaynardNumerator`/`Denominator` are `terms × terms` double sums. `native_decide` cannot touch that. A feasible path needs a **new symmetric-orbit integral layer** (integrate per partition-orbit via `|orbit(λ)| · ∏λᵢ!/(k+|λ|)!`, not per monomial) — substantial new infrastructure, and it still closes nothing without #3.

3. **The coefficients aren't available offline.** Polymath8b §6's optimized coefficients are a Maple output; "barely cleared 4" means you can't guess them. No internet, no Maple, no SDP solver in the box.

## The 4 remaining `:= sorry` leaves — all walled offline (read this session)
- `Prerequisites:90` `geh_implies_eh` and `:97` `eh_implies_mpz` — the in-file triage comments say "**unprovable as stated**": EH/GEH/MPZ are opaque `axiom _ : Prop` with no content, so no proof term exists until mathlib ships discrepancy-bound machinery. NOT "trivial ~10 lines."
- `Zhang:36` `liminfGap 1 ≤ 70000000` — the entire Zhang machinery (smooth-moduli equidistribution). Far outside mathlib.
- `Polymath8b:796` `TwinPrimesConjecture ∨ NearMissGoldbach` — §8, GEH-conditional.

The cited sieve core (`s1`/`s2` axioms, Mertens/Selberg/singular-series) stays cited — infeasible offline, ROADMAP Bucket D.

## There is NO offline on-thread win (verified this session — corrects my own earlier draft)
I suspected `Engelsma.tuple_49/50_admissible` might still be a `native_decide`-closeable sorry (the `Targets.lean:100` comment says "currently 1 sorry on the all-primes check"). **That comment is STALE.** Read from source: `tuple_50_admissible` (`:629`), `tuple_49_admissible` (`:639`), `48/51/54` are all **already proven** via `admissible_of_check_small_primes … native_decide`. The lengths/diameters/sortedness are proven too. The *only* admissibility gap is `tuple_5511_admissible` (`Engelsma:702`) — an **`axiom`**, not a sorry, because `native_decide` OOMs on the 5511-tuple — and it feeds only the §8 twin/Goldbach conditional path, not `H1_le_246`. So `H1_le_246` is already fully discharged on the admissibility side; nothing offline-tractable remains on this thread.

## 🎬 Next actions (recommended order)
1. **PIVOT.** bounded_gaps is at its honest offline ceiling — every remaining leaf is open math, deep analytic NT outside mathlib, or a §8 GEH-conditional. The warm anti-[[sum-product]] target is **Erdős #403** (carry-ceiling lemma) at `~/src/erdos-403/` — genuinely closeable in the box; see `erdos-formalization-hunt` + `erdos-403` KB notes. Do NOT build the symmetric-orbit integral layer speculatively — it closes nothing without the offline-unavailable M₅₀ coefficients.
2. **Do NOT** re-open `polynomialMkF_eq_MkF` / `Mk_ge_polynomialMkF` (done, axiom-clean) or charge `Mk 49 > 4` (open math). Do NOT chase the Engelsma admissibility — already done.
3. On the host (not the box): push the 14-commit `path-a-selberg-nu` branch + open the PR for the bridge work (`HANDOFF-PR64.md` has the cmds). That's the real bankable deliverable from the 0530 session.

## 📁 Key files
- `BoundedGaps/Targets.lean` — `H1_le_of_Mk_witness`, `H1_le_246` (Mk 50), `H1_le_240_if_Mk_49_witness` (Mk 49 = open), `H1_le_236_if_Mk_48_witness`.
- `BoundedGaps/SievePolynomial.lean` — bridge + `Mk_gt_four_of_polynomial_witness` (axiom-clean); `PolynomialSieveWeight` per-monomial rep (the Wall-2 bottleneck) at line 51.
- `BoundedGaps/Prerequisites.lean` — the 2 opaque-Prop sorries (90, 97).
- `BoundedGaps/Engelsma.lean` — admissibility tuples (the candidate offline win).
