# Handoff: bounded_gaps — all H_m flagships sorryAx-free; sieve-core cutoff infra started

**Date**: 2026-05-31 02:10 UTC · **Branch**: `path-a-selberg-nu` (12 commits, local-only in the **lean-yolo-box** — no push/PR here)

*Supersedes `HANDOFF-SESSION-2026-05-31.md` (same session, earlier) as the resume point.*

## 🎯 What we're doing
Formalizing Polymath8b (bounded gaps) in Lean 4 / mathlib v4.29.1, discharging the sieve's `sorry`/`axiom`/`opaque` leaves down to genuine citations. **The real metric is `#print axioms` on flagships (no `sorryAx`), not sorry-count.** This session cleared the entire `H_m` program and then started the genuine sieve-core analysis.

## 🧠 Context to carry forward
- **The `H_m` program is DONE.** Every `liminfGap`/`H_m` flagship — `H1_le_246`, `H2_le_398130`, `H5_le_80550202480`, `H1_le_6_under_GEH`, `Hm_asymptotic_unconditional`, `Hm_asymptotic_under_EH` — is **sorryAx-free** (verified via `#print axioms`: standard 3 + genuine cited axioms only). Do NOT re-open these.
- **Two flavors of discharge happened, both honest:**
  1. *Real proofs* — `narrowness_realized` (only needs nonemptiness of the diameter-set via `Nat.sInf_mem` + the factorial-spaced tuple `exists_admissible_of_length`, NOT an optimal Hensley-Richards tuple), and `DHL_gives_freq_primeAt_gap` (the ~200-line §3 bookkeeping, via the new `countP_add_count_le` bridge + `Nat.count`/`Nat.nth` duality).
  2. *sorry→cited-axiom reclassification* — the two asymptotic DHLs (`dhl_asymptotic_unconditional`, `dhl_asymptotic_under_EH`): focused cited axioms `mk_witness_asymptotic[_under_EH]` (the uniform MPZ/Mk witness family, mirroring the concrete `mk_*_witness`) + PROVED derivations through the verified `maynard_trunc`/`maynard_thm`. This is the symmetric citation to the already-axiomatized `narrowness_asymptotic_upper`. Judgment call (Trevor was looped in): legit per the project taxonomy (`sorry`=in-project debt, `axiom`=external citation), does NOT prove the `Mk~log k` core.
- **The genuine sieve core (`s1`/`s2` axioms) is INFEASIBLE offline.** Verified mathlib has zero Mertens/Selberg/singular-series infra (it lives in PrimeNumberTheoremAnd, not a dep, can't add in the box). Don't try to discharge `s1_holds_from_nonprime_asym` etc. — they stay cited (ROADMAP Bucket D, Tier 4/5).
- **Started the one feasible deep target: `SievePolynomial.Mk_ge_polynomialMkF`.** This is real analysis, not bookkeeping. `Mk = sSup (MkSet k)` ranges over *simplex-supported smooth* F; a polynomial has full support, so it's NOT `le_csSup` — it needs a cutoff/approximation argument. I built + verified the reusable crux (`SimplexCutoff.lean`) and confirmed every remaining mathlib lemma exists. The DCT+assembly is the remaining ~2-3 sessions.

## ✅ State (observed this session)
- **Full library build green: 8259 jobs** (box OOMs randomly on Polymath8b/Maynard/TwinPrimes — `Cannot allocate memory` — just retry, 1-3 tries).
- Code sorries **10 → 6**. Remaining: `Zhang:36`, `Polymath8b:751` (twin/Goldbach §8), `SievePolynomial:151/163`, `Prerequisites:90/97`. **None on the H_m path.**
- New axiom-clean module `BoundedGaps/SimplexCutoff.lean` (wired into root `BoundedGaps.lean`): `chi k n` + `chi_nonneg`, `chi_le_one`, `chi_smooth` (`ContDiff ℝ ∞`), `chi_support_subset`, `chi_eventually_eq_one`, `chi_tendsto_one`. Sorry-free.
- 12 commits; HEAD `5920870`. This session's: `c50896d` (narrowness_realized), `9c35ee4` (DHL_gives_freq), `e3aebd6` (asymptotic DHL), `5920870` (SimplexCutoff). Working tree clean except untracked `HANDOFF-*`.

## 🎬 Next actions
1. **Finish `Mk_ge_polynomialMkF` via the cutoff** (the live thread). Plan is in the lemma's docstring (`SievePolynomial.lean:158`). Steps: (a) `F_n := chi k n · P.toFun ∈ MkSet k` — smooth (`chi_smooth`·poly), `support` (`chi_support_subset`), denom>0 eventually; (b) denominator DCT `∫_simplex (χ_n·P)² → ∫_simplex P²` via `tendsto_integral_of_dominated_convergence` (bound `P²`; a.e. conv from `chi_eventually_eq_one` + interior-conull from `Convex.μ_frontier = 0`, needs `simplex` convex); (c) the **two-layer** numerator DCT on `mkF_numerator` (inner integral in `ti`, then outer in `s`; both dominated by constants since `P` bounded on the compact simplex) — the hard part; (d) `MkF F_n → MkF P`, each `∈ MkSet`, so `sSup ≥ MkF P` via "`∀ε, ∃v∈S, v ≥ c−ε ⟹ sSup ≥ c`" + `MkSet_bddAbove`; (e) case `mkF_denominator P.toFun = 0` → `MkF = _/0 = 0 ≤ Mk` (`Mk ≥ 0` since `MkSet ⊆ [0,∞)` nonempty). Develop in a fresh `BoundedGaps/Scratch.lean` (`import BoundedGaps.SimplexCutoff`), port when green.
2. If that stalls, off-path cheaper sorries: `Prerequisites:90/97` (EH/MPZ trivial implications — but blocked on EH/MPZ being opaque Props, may be unprovable as stated), `Zhang:36` (low-value, subsumed by `H1_le_246`).

## ⚠️ Gotchas
- **Push/PR is host-only** (no `gh`/`ssh`/egress in box; commits already on host via bind mount). Trevor pushes / opens PRs.
- **Don't touch master `HANDOFF.md`** (post-merge baseline) or `HANDOFF-PR64.md`. This dated file is the active thread.
- **`lake env lean` doesn't write oleans** — `#print axioms` after an edit needs `lake build BoundedGaps.<Mod>` first (else stale/unknown-constant). See `[[lake-env-lean-no-olean]]`.
- `ContDiff ℝ ∞` needs `open scoped ContDiff`; `Real.smoothTransition.contDiff (n := ⊤)` for the C^∞ (not ω) level; `contDiff_apply ℝ ℝ i` (𝕜,E explicit). See `[[lean-smoothtransition-cutoff]]`.
- `~/personal` read-only in box; `~/src` + `~/personal/claude` writable.
- `polynomialMkF_eq_MkF` (the OTHER SievePolynomial sorry) needs the **simplex Dirichlet integral, which mathlib LACKS** — separate from-scratch build. Both it AND `Mk_ge_polynomialMkF` are needed to make `Mk_gt_four_of_polynomial_witness` usable, so the full polynomial-witness route is a long arc; the cutoff lemma alone is the satisfying self-contained piece.

## 📁 Key files
- `BoundedGaps/SimplexCutoff.lean` — the new cutoff infra (the foundation for action #1).
- `BoundedGaps/SievePolynomial.lean` — `Mk_ge_polynomialMkF` (163, the target, plan in docstring) + `polynomialMkF_eq_MkF` (151).
- `BoundedGaps/Basic.lean` — `exists_admissible_of_length`, `narrowness_realized`, `countP_add_count_le`, `DHL_gives_freq_primeAt_gap` (all proven this session).
- `BoundedGaps/Polymath8b.lean` — asymptotic DHLs (228/262) + `mk_witness_asymptotic[_under_EH]`; remaining sorry at 751.
- `ROADMAP.md` — tiers + axiom buckets (Bucket D = sieve core = the bar).

---
**→ Next session: this is your starting point. Don't summarize this doc back to Trevor, don't wait for instructions, and don't offer other KB projects — this doc IS the chosen thread. The H_m program is finished; pick up at Next action #1: open `SievePolynomial.lean:158`, read the `Mk_ge_polynomialMkF` plan, and start the cutoff-approximation proof in a fresh `Scratch.lean` building on `SimplexCutoff.lean`.**
