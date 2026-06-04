# Handoff: bounded_gaps — DHL flagships now sorryAx-free 🎯, push pending

**Date**: 2026-05-30 (session 2) · **Branch**: `path-a-selberg-nu`
(**8 stacked commits**, local-only)

## 🏆 Headline (commit `8e2acd7`)
**Both DHL flagships are now `sorryAx`-free.** `#print axioms` on
`dhl_50_2` (EH path) and `dhl_3_2_under_GEH` (GEH path) no longer lists
`sorryAx` — each depends only on genuine **citation** axioms (BV / EH / GEH
props, paper §6 numerical `Mk` witnesses, and the cited §3 `s1`/`s2`/`beyond`
sieve-asymptotic estimates). So **DHL[50,2] under EH** and **DHL[3,2] under
GEH** are complete Lean proofs modulo those citations.

This came from discharging `witness_eventually_from_sieve_data` — the
analytic-combinatorial core of Polymath8b §3 Lemma crit (from the sieve
bounds + key ratio, produce the prime-witness `n ∈ [N,2N]`). It was the ONLY
sorry in the flagships' DHL path. Needed two added hypotheses (`1 ≤ W`,
`ν ≥ 0`), threaded through `dhl_criterion`'s `hSieve` and all four
`selberg_sieve_data_*_from_F`. Seven new axiom-clean helpers (Fin-card↔countP,
pigeonhole, `M₂=M₁·log x`, `M₁=o M₂`, the o(M₂) bounds, `core_positive`).
Code sorries 11 → 10.

Self-contained handoff. Written from **inside the lean-yolo-box**
(network-isolated; egress = Anthropic only — no `gh`/`ssh`, GitHub unreachable).
Everything is **committed locally** on shared bind-mounts, so the host already has
the commits; only the **network half** (push / PR) is pending and must run on the
Mac host. Companion files: `HANDOFF.md` (master `@0946c81` baseline — do NOT
overwrite until the branch merges), `HANDOFF-PR64.md` (per-commit PR-body detail
for the first 5 commits).

## 🎯 What this session did
Discharged the **last two MkSet-family sorries** in `Sieve.lean`, completing the
Tier-2 MkSet block. New commit `2bfe6d1` (6th on the branch):

1. **`MkSet_truncated_nonempty`** (was `Sieve.lean:783`). Mirror of `MkSet_nonempty`
   with the product-of-bumps witness, but bump radius scaled to `K = min(1/k, α)`
   so every coordinate of a point in `supp F` lies in `(K/4, 3K/4)`. That gives
   `t i ≤ α` (via `K ≤ α`) on top of `t i ≥ 0` and `∑ t i < 3/4 ≤ 1` (via `k·K ≤ 1`),
   i.e. `supp F ⊆ simplex_truncated k α`. Positive Rayleigh denominator via the same
   `setIntegral_pos_iff_support_of_nonneg_ae` route.

2. **`MkSet_eps_bddAbove`** (was `Sieve.lean:970`). Crude bound
   `M_{k,ε} ≤ (n+1)·max(1+ε,0)`, mirroring `MkSet_bddAbove`. The substantive new
   lemma is **`J_i_eps_le_denom`** (sister of `J_i_le_denom`):
   `J_{i,1-ε}(F) ≤ max(1+ε,0)·I_ε(F)` via `cs_Icc` on the inner `[0, 1+ε−∑s]` slice
   (moving boundary tamed by `support F ⊆ simplex_eps`) + the `integral_insertNth_eq`
   fibration. **Key subtlety vs `J_i_le_denom`:** the theorem has NO `ε > 0`
   hypothesis, so the per-slice bound must hold for all `ε`. Handled by casing on
   `L := 1+ε−∑s`: `L ≥ 0` → Cauchy-Schwarz with `L ≤ 1+ε ≤ max(1+ε,0)`; `L < 0` →
   `Icc 0 L = ∅` forces the inner integral (hence `m s`) to `0`, so `m s² = 0 ≤ C₀·Φ s`
   trivially. Constant `C₀ = max(1+ε,0) ≥ 0` makes both branches uniform.

3. Supporting helpers added before `J_i_eps_le_denom`: **`isCompact_simplex_eps`**
   (closed + sup-norm-bounded by `max(1+ε,0)`) and **`isClosed_simplex_shrunk`**.

Then a separate commit (`b3a9c21`, 7th on the branch):

4. **`wtrick_data` `axiom → theorem`.** Its conclusion had been gutted to the
   trivial `∃ b W, 1 ≤ W ∧ b < W` (the real coprime-residue-class content was
   refactored into the `selberg_nu`/`alphaBound`/`betaBound` predicates and the
   cited `s1_*`/`s2_*` axioms). So it was a vestigial axiom — proved with the
   one-liner `⟨0, 1, le_refl 1, Nat.zero_lt_one⟩`. **This is an honesty/bookkeeping
   reduction, NOT the Tier-3 sieve-core milestone** — it drops `wtrick_data` from
   the flagships' `#print axioms` (verified: it was in both `dhl_50_2` and
   `dhl_3_2_under_GEH` before, gone after) without hiding anything; the deep
   W-trick content stays cited via s1/s2.

## ✅ State (all observed this session)
- **Full library build green: 8259 jobs.** (Attempt 1 OOM'd on `TwinPrimes` — the
  usual random box OOM — attempt 2 replayed clean. Just retry `lake build`.)
- **Project code sorries 13 → 11.** `Sieve.lean` 3 → **1** (only the pre-existing
  `dhl_criterion` `countP` sorry at `Sieve.lean:178` remains).
- All 5 new declarations (`MkSet_truncated_nonempty`, `MkSet_eps_bddAbove`,
  `J_i_eps_le_denom`, `isCompact_simplex_eps`, `isClosed_simplex_shrunk`) verified
  `#print axioms = [propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
  custom axioms.
- Flagships `dhl_50_2` / `dhl_3_2_under_GEH`: the MkSet work left their axiom deps
  unchanged; the `wtrick_data` commit then **removed `wtrick_data`** from both lists
  (one fewer cited axiom each). Remaining flagship axioms are all genuine Bucket-A/D
  citations + the pre-existing `sorryAx`.
- **Honest status: Tiers 1 & 2 of `ROADMAP.md` are now COMPLETE.** All sieve opaques
  discharged (prior sessions), the whole MkSet family discharged (this session), and
  the vestigial `wtrick_data` axiom retired. Everything left is genuinely deep:
  Tier 3+ sieve-core (`s1_*`/`s2_*`, the real §3 asymptotics — 10-30 sessions, need
  Mertens/divisor-sum mathlib API not obviously present offline) or the 5-15-session
  bookkeeping sorries (`narrowness_realized`, `DHL_gives_freq_primeAt_gap`,
  `dhl_criterion`). No more quick honest wins remain in `Sieve.lean`.

## 🎬 Next actions
1. **(Host only)** Push the branch — now **8** commits (`9ca6120`, `48d2288`,
   `4c57f9c`, `7aa2b9a`, `f2a7892`, `2bfe6d1`, `b3a9c21`, `8e2acd7`). NB Trevor
   said **skip the PR** for this round — the commits live on the branch on the
   host via the bind mount; push if/when desired:
   ```bash
   cd ~/src/bounded_gaps
   git push -u origin path-a-selberg-nu
   gh pr create --title "Tier-1/2: discharge sieve opaques + full MkSet family" \
     --body-file HANDOFF-PR64.md   # note: PR64 body covers the first 5; add commit 6 summary
   gh pr merge --admin --merge       # master protected; bypass 30-min GHA queue
   ```
   After merge: refresh master `HANDOFF.md` (opaques 3→0, MkSet family fully
   discharged, sorries → 11, depth-into-sieve up), then trash `HANDOFF-PR64.md`
   + this file. Also tick the KB todo "Push + PR the bounded_gaps Tier-1/2 discharge"
   (in `~/personal/claude/knowledge/todos/README.md` — read-only in the box, edit
   on host).
2. **(Box)** Remaining sorries (10), honest difficulty:
   - **`witness_eventually_from_sieve_data` — ✅ DONE this session** (was the
     `Sieve.lean:178` analytic core; flagships now sorryAx-free).
   - **`narrowness_realized` (`Basic.lean:678`), `DHL_gives_freq_primeAt_gap`
     (`Basic.lean:735`)** — these gate the `H_1 ≤ N` *gap* bounds (DHL → liminfGap).
     The DHL flagships don't touch them, but `H1_le_246` etc do. 5-15 sessions each
     (Hensley-Richards / Erdős k-tuple; ~200-line Finset.count translation).
   - **Tier 3+ `s1_*`/`s2_*` sieve core** (`Sieve.lean` ~1860+): the real §3
     asymptotics, still cited axioms (NOT sorries). 10-30 sessions, needs
     Mertens/divisor-sum mathlib API. The deepest remaining math.
   - **`SievePolynomial.lean` pair** (`polynomialMkF_eq_MkF` :151,
     `Mk_ge_polynomialMkF` :163): ⚠️ **the TRIAGE comments are STALE/WRONG.** They
     claim `Mk_ge_polynomialMkF` is "~5 lines le_iSup once Mk has a real body" — but
     `Mk = sSup (MkSet k)` IS real now, and `MkSet` requires `support ⊆ simplex`. A
     polynomial has full support, so `MkF k P.toFun ∉ MkSet k` and it is NOT a
     `le_csSup`. Proving it needs a cutoff/approximation argument (multiply the
     polynomial by a smooth bump → limit), which is genuine variational content, not
     a quick win. `polynomialMkF_eq_MkF` is more plausible (`MkF` only ever integrates
     over the simplex, so it should match the closed-form monomial integrals termwise)
     but needs Dirichlet-integral-over-simplex API that may be missing. Don't trust
     the "~30 lines / ~5 lines" estimates.

## ⚠️ Gotchas
- Don't overwrite master `HANDOFF.md` until the branch merges.
- `~/personal` is read-only in the box; `~/src` and `~/personal/claude` are writable.
- No general internet / `gh` / `ssh` in the box → push/PR is host-only.
- Prototyping rhythm that worked: develop new lemmas in `BoundedGaps/Scratch.lean`
  (`import BoundedGaps.Sieve` + `open scoped ContDiff` for the `∞` token; then
  `lake env lean BoundedGaps/Scratch.lean`, fast), paste into `Sieve.lean`, delete
  scratch. The `∞` in `ContDiff ℝ ∞` needs `open scoped ContDiff`. Use
  `open MeasureTheory Set in` BEFORE the docstring (not after) — a doc comment must
  sit directly above its declaration.

## 📁 Key files
- `BoundedGaps/Sieve.lean` — `MkSet_truncated_nonempty` (~line 785),
  `isCompact_simplex_eps` / `isClosed_simplex_shrunk` / `J_i_eps_le_denom` /
  `MkSet_eps_bddAbove` (the eps block, after `MkSet_eps_nonempty`). Remaining
  sorry: line 178.
- `ROADMAP.md` — tier plan. `HANDOFF.md` — master baseline. `HANDOFF-PR64.md` —
  PR body for commits 1-5.
