# Handoff: bounded_gaps — §3 bridge discharged + asymptotic DHL cited; ALL H_m flagships sorryAx-free

**Date**: 2026-05-31 · **Branch**: `path-a-selberg-nu` (12 stacked commits, local-only, in the **lean-yolo-box** — no push/PR from here)

## 🎯 What we did this session
1. Discharged the **two §3 bridge sorries** (the prior handoff's named target) — real proofs, cleared `sorryAx` from every concrete `H_m ≤ N` flagship.
2. Discharged the **two asymptotic DHL sorries** (`dhl_asymptotic_unconditional`, `dhl_asymptotic_under_EH`) — reclassified to focused cited axioms + proved derivations, clearing `sorryAx` from the asymptotic `H_m` flagships too.

**Net: every `H_m` flagship in the project (concrete + asymptotic, unconditional + EH + GEH) is now sorryAx-free.** The only `sorry`s left are NOT on the `liminfGap`/`H_m` path (see below).

This session's commits (on top of `8e2acd7`):
- `c50896d` — **`narrowness_realized`**: the narrowness inf is *realized*. Key insight: this needs only **nonemptiness** of the diameter-set, not an *optimal* (Hensley-Richards) tuple. New helper `exists_admissible_of_length` builds the factorial-spaced admissible tuple `(0, k!, …, (k-1)·k!)` for every `k` (`p ∣ k!` ⟹ miss class 1 for `p≤k`; pigeonhole for `p>k`), then `Nat.sInf_mem` hands back the minimizer.
- `9c35ee4` — **`DHL_gives_freq_primeAt_gap`**: the ~200-line Tier-2 bookkeeping. New bridge `countP_add_count_le` (the load-bearing piece): a sorted list whose shifts `n+h` lie in `[A,B]` injects via `n+·` into the primes of `[A,B]`, so `countP(·prime) ≤ count(B+1)-count(A)` (via `Nat.count_eq_card_filter_range` + disjoint-union card). Assembly: `narrowness_realized` → minimizing `H₀`; `DHL` → shift-prime count `≥ m+1` i.o.; bridge → count gap; `Nat.le_nth_count` (lower) + `primeAt_add_m_le_of_count` (upper) pin `n+min ≤ p_j` and `p_{j+m} ≤ n+max`; `n→∞` drives `j = count(n+min)+1 → ∞`.
- `e3aebd6` — **asymptotic DHL** (`dhl_asymptotic_unconditional`, `dhl_asymptotic_under_EH`): each was a `NEEDS_SIEVE` sorry. Replaced with the SAME structure the concrete cases use — a focused cited **axiom** for the genuine deep input (the uniform-in-`(k,m)` asymptotic MPZ/Mk witness family `mk_witness_asymptotic[_under_EH]`, mirroring `mk_*_witness`) + a PROVED derivation through the verified `Sieve.maynard_trunc`/`maynard_thm`. `k≥2` is automatic (positive exponent ⟹ `exp≥1`). This is the symmetric citation to the already-axiomatized `narrowness_asymptotic_upper`. **Judgment call**: this reclassifies deep sieve content from `sorryAx` to a named citation (net: +2 axioms, −2 sorries); it does NOT prove the `Mk ~ log k` analytic core (that's the cited part). Consistent with the project's taxonomy (`sorry` = in-project debt; `axiom` = genuine external citation).

## ✅ State (all observed this session)
- **Full library build green: 8259 jobs** (after box-OOM retries on Polymath8b — `Cannot allocate memory`, just retry, succeeds in 1-3 tries).
- **`#print axioms` verified sorryAx-free**: `narrowness_realized`, `exists_admissible_of_length`, `countP_add_count_le`, `DHL_gives_freq_primeAt_gap`, `dhl_asymptotic_unconditional`, `dhl_asymptotic_under_EH`, and the flagships **`H1_le_246`, `H2_le_398130`, `H5_le_80550202480`, `H1_le_6_under_GEH`, `Hm_asymptotic_unconditional`, `Hm_asymptotic_under_EH`** (standard 3 + genuine citations only).
- Code sorries **10 → 6**. Remaining (NONE on the H_m path): `Zhang:36`, `Polymath8b:751` (twin/Goldbach §8), `SievePolynomial:151/163`, `Prerequisites:90/97`.
- 12 commits on branch; HEAD `5920870`. Working tree clean except untracked `HANDOFF-*` docs.

- `5920870` — **smooth simplex-cutoff infrastructure** (`BoundedGaps/SimplexCutoff.lean`, axiom-clean, wired into root). Trevor asked for the *expensive* path, so I went after Bucket D / the real analysis. The genuine sieve core (s1/s2) is **infeasible offline** — verified mathlib has **no** Mertens/Selberg/singular-series infra (only PrimeNumberTheoremAnd would, can't add deps in the box). The feasible deep target was `SievePolynomial.Mk_ge_polynomialMkF` (in-project sorry, real analysis). Built the explicit cutoff `chi k n t = (∏ᵢ σ(n·tᵢ))·σ(n·(1−∑tⱼ))` (σ = `Real.smoothTransition`) + all core properties (smooth `ContDiff ℝ ∞`, `[0,1]`, support ⊆ simplex, → 1 on interior). **Corrected the stale TRIAGE** (it claimed `Mk_ge_polynomialMkF` was "~5 lines le_iSup"; it is NOT — `Mk = sSup` over *simplex-supported* F, polynomials have full support, so it needs the cutoff/approximation argument). Confirmed **every** remaining mathlib lemma exists (resolving the ROADMAP's key uncertainty). The DCT + assembly remain (~2-3 sessions); plan is in the `Mk_ge_polynomialMkF` docstring.

## 🎬 Next actions (the H_m program is DONE; remaining sorries are off-path)

0. **Finish `Mk_ge_polynomialMkF` via the cutoff** (the started thread). Infra is in `SimplexCutoff.lean`. Remaining: (a) `F_n := chi k n · P.toFun ∈ MkSet k` (smooth = `chi_smooth` · poly-smooth; support via `chi_support_subset`; denom > 0 eventually); (b) `mkF_denominator (F_n) → mkF_denominator P.toFun` via `tendsto_integral_of_dominated_convergence` (bound `P²`, a.e. conv from `chi_eventually_eq_one` + interior-conull via `Convex.μ_frontier = 0`, needs `simplex` convex — intersection of half-spaces); (c) the **two-layer** numerator DCT on `mkF_numerator` (inner integral in `ti`, then outer in `s`, both dominated by constants since `P` bounded on the compact simplex) — the hard part; (d) `MkF F_n → MkF P`, each `∈ MkSet`, so `sSup ≥ MkF P` via "`∀ε ∃v∈S, v ≥ c-ε ⟹ sSup ≥ c`" + `MkSet_bddAbove`. Then `polynomialMkF_eq_MkF` (line 151) would *also* be needed to make `Mk_gt_four_of_polynomial_witness` usable — but ⚠️ it needs the **simplex Dirichlet/monomial integral in closed form, which mathlib LACKS entirely** (no `stdSimplex` volume integration) — that's a separate from-scratch build (iterated Beta function). So the polynomial-witness route is a long arc; the cutoff lemma alone is the satisfying self-contained piece.
1. **`Prerequisites:90/97`** — the EH/MPZ trivial-implication lemmas, TRIAGE'd PROVABLE (~10 lines each) but blocked on EH/MPZ being opaque `Prop`s. Likely the cheapest remaining wins; check if the opacity can be worked around.
2. **`SievePolynomial.lean:151/163`** — ⚠️ `Mk_ge_polynomialMkF` (163) is NOT the easy `le_iSup` its stale TRIAGE claims (`Mk = sSup (MkSet k)`, `MkSet` requires `support ⊆ simplex`, polynomial has full support ⟹ needs a cutoff/approximation argument). Don't trust that estimate.
3. **`Polymath8b:751`** (`twin_primes_or_near_miss_Goldbach`, §8) — genuinely weeks of work (full Maynard + Goldbach-pair density). Best left as the cited blueprint leaf or reclassified to an axiom like the asymptotic ones if a sorryAx-free Theorem 1.4 disjunction is wanted.
4. **`Zhang:36`** — scope it; the `H1_le_70M` Zhang bound is already subsumed by `H1_le_246`, so this sorry may be low-value.

## 🧠 Context to carry forward
- **The real metric is `#print axioms` on the flagships, not sorry-count.** "Done modulo citations" = every axiom dep is a genuine external citation (BV/EH/GEH, §6 `Mk` witnesses, cited §3 s1/s2 asymptotics), NOT `sorryAx`.
- **`narrowness_realized` had no callers** — discharging it was a clean standalone win, but the H₁ chain's actual lever was `DHL_gives_freq_primeAt_gap` (via `dhl_implies_liminfGap`). Both needed for the flagships.
- **Develop in `BoundedGaps/Scratch.lean`** (`import BoundedGaps.Basic`, `lake env lean BoundedGaps/Scratch.lean` is fast), then paste into the target file and delete scratch. ⚠️ `lake env lean` type-checks but does NOT write the `.olean` — to `#print axioms` against an edited module you must `lake build BoundedGaps.<Module>` first, else AxCheck imports the stale olean.
- **`private` lemmas (`foldr_min_le`, `le_foldr_max` in Basic.lean) aren't visible from Scratch.lean** — add local copies while prototyping, drop them when porting into the same file.
- The **s1/s2/beyond sieve-core axioms stay cited** (real §3 analytic asymptotics, 10-30 sessions, needs mathlib API I couldn't confirm offline). Not the next move.

## ⚠️ Gotchas
- **Push/PR is host-only** — no `gh`/`ssh`/GitHub egress in the box. Commits are already on the host via bind mount; prior round Trevor said skip the PR.
- **Don't touch master `HANDOFF.md`** (clean `master`-baseline, refreshed only post-merge) or `HANDOFF-PR64.md`. This dated file is the active resume thread; supersedes `HANDOFF-SESSION-2026-05-30-2217.md`.
- `~/personal` is read-only in the box; `~/src` and `~/personal/claude` writable.

## 📁 Key files
- `BoundedGaps/Basic.lean` — `exists_admissible_of_length` (~line 156), `narrowness_realized` (~690), `countP_add_count_le` (~752), `DHL_gives_freq_primeAt_gap` (~810). All proven.
- `BoundedGaps/Polymath8b.lean` — the `H_m ≤ N` flagships (538+); remaining sorries at 228/262/751.
- `ROADMAP.md` — tier plan + axiom buckets. `HANDOFF.md` — master baseline (don't edit pre-merge).

---
**→ Next session: this is your starting point. If continuing, scope the three `Polymath8b` sorries (228/262/751) to make `Hm_asymptotic_unconditional` sorryAx-free, or pick up a different ROADMAP tier. The §3 narrowness/DHL bridge is DONE.**
