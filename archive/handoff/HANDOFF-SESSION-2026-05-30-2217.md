# Handoff: bounded_gaps — DHL flagships sorryAx-free; next is the H₁ gap bounds

**Date**: 2026-05-30 22:17 UTC · **Branch**: `path-a-selberg-nu` (8 stacked commits, local-only, in the **lean-yolo-box** — no push/PR from here)

## 🎯 What we're doing
Formalizing Polymath8b (bounded gaps between primes) in Lean 4 / mathlib v4.29.1, discharging the sieve's `sorry`/`axiom`/`opaque` leaves down to genuine citations. This session cleared Tiers 1+2 and the Lemma-crit analytic core.

## 🧠 Context to carry forward
- **The real metric is `#print axioms` on the flagships, not sorry-count.** A flagship is "done modulo citations" when every axiom dep is a genuine external citation (BV/EH/GEH props, paper §6 numerical `Mk` witnesses, the cited §3 s1/s2/beyond asymptotics) — NOT `sorryAx` or a gutted/false axiom. As of this session **`dhl_50_2` (EH) and `dhl_3_2_under_GEH` (GEH) are both sorryAx-free** — verified, were not before.
- **The DHL flagships ≠ the H₁ gap bounds.** `dhl_*` (the DHL[k,m+1] criterion, a `Set.Infinite`) is now clean. But `H1_le_246` / `liminfGap` bounds go DHL → narrowness, and that path still hits `narrowness_realized` (`Basic.lean:678`) and `DHL_gives_freq_primeAt_gap` (`Basic.lean:735`), both `sorry`. **That pair is the natural next target** — clearing it makes the actual H₁ numbers sorryAx-free too.
- **Two hypotheses had to be ADDED** to `witness_eventually_from_sieve_data` (it's unprovable without them, and Polymath8b assumes both): `1 ≤ W` and `ν ≥ 0`. Supplied from `wtrick_data` (W≥1) and `selberg_nu_basis_nonneg` (ν is a square). Threaded through `dhl_criterion`'s `hSieve` existential and all four `selberg_sieve_data_*_from_F` providers. If you add more hypotheses to that chain, expect the same 5-site thread.
- **Develop in `BoundedGaps/Scratch.lean`** (`import BoundedGaps.Sieve`, `lake env lean BoundedGaps/Scratch.lean` is fast), then paste into `Sieve.lean` and delete scratch. `lake build` OOMs randomly in the box (TwinPrimes/Maynard/SievePolynomial) — just retry, succeeds in 2-4 tries.
- The **s1/s2/beyond sieve-core axioms stay cited** (the real §3 analytic asymptotics — Mertens/divisor-sum, 10-30 sessions, needs mathlib API I couldn't confirm offline). Not the next move.

## ✅ State (all observed this session)
- **Full library build green: 8259 jobs** (after box-OOM retries).
- **`dhl_50_2` and `dhl_3_2_under_GEH`: `#print axioms` = standard 3 + citations only, NO `sorryAx`** (verified via a temp AxCheck.lean).
- Code sorries **11 → 10** (`witness_eventually_from_sieve_data` discharged; remaining: Zhang:36, Polymath8b:228/262/751, Basic:678/735, SievePolynomial:151/163, Prerequisites:90/97).
- 8 commits on branch; HEAD `8e2acd7`. Working tree clean except the untracked `HANDOFF-*` docs.
- This session's commits: MkSet_truncated_nonempty+eps_bddAbove (`2bfe6d1`, Tier 2 done), wtrick_data axiom→theorem (`b3a9c21`), witness_eventually (`8e2acd7`).

## 🎬 Next actions
1. **Scope `narrowness_realized` (`Basic.lean:678`) and `DHL_gives_freq_primeAt_gap` (`Basic.lean:735`).** Read both statements + their docstrings/TRIAGE notes. These are Bucket-C (~200-line Finset.count translation / Hensley-Richards). Decide if either is box-tractable; if so, prototype in Scratch.lean. Clearing both makes `H1_le_246` sorryAx-free — the next real milestone.
2. If those are too big, the other standalone code sorries are `SievePolynomial.lean:151/163` — but ⚠️ see Gotchas: `Mk_ge_polynomialMkF` is NOT the easy `le_iSup` its stale TRIAGE claims.

## ⚠️ Gotchas
- **Push/PR is host-only** — no `gh`/`ssh`/GitHub egress in the box. Commits are already on the host via bind mount; Trevor said **skip the PR** this round.
- **Don't touch master `HANDOFF.md`** (it's the clean `master`-baseline, refreshed only post-merge) or `HANDOFF-PR64.md` (PR body for the first 5 commits). The running narrative is in `HANDOFF-SESSION-2026-05-30.md`; this dated file supersedes it for resume.
- `SievePolynomial.lean:163` `Mk_ge_polynomialMkF`'s TRIAGE comment ("~5 lines le_iSup") is **STALE/WRONG**: `Mk = sSup (MkSet k)` and `MkSet` requires `support ⊆ simplex`, but a polynomial has full support, so `MkF k P.toFun ∉ MkSet k`. It needs a cutoff/approximation argument, not `le_csSup`. Don't trust the estimate.
- `~/personal` is read-only in the box; `~/src` and `~/personal/claude` writable.

## 📁 Key files
- `BoundedGaps/Sieve.lean` — the sieve. New this session (~line 152+): `card_fin_filter_eq_countP`, `pigeonhole_bridge`, `betaMainTerm_eq_alphaMainTerm_mul_log`, `alphaMainTerm_isLittleO_betaMainTerm`, `log3x_mul_alphaMainTerm_isBigO`, `m_log3x_err1_isLittleO`, `core_positive`, then the now-proven `witness_eventually_from_sieve_data`.
- `BoundedGaps/Basic.lean` — `narrowness_realized` (678), `DHL_gives_freq_primeAt_gap` (735): the next targets.
- `ROADMAP.md` — tier plan + axiom buckets. `HANDOFF.md` — master baseline (don't edit pre-merge).

---
**→ Next session: this is your starting point. Don't summarize this doc back to Trevor, don't wait for instructions, and don't offer other KB projects — this doc IS the chosen thread. Absorb the context, then start at Next action #1: read `narrowness_realized` and `DHL_gives_freq_primeAt_gap` in `Basic.lean` and assess box-tractability.**
