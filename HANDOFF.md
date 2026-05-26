# HANDOFF.md — Bounded Gaps Lean project

Written 2026-05-26 (afternoon), superseding the 2026-05-26 morning version.
Reflects state at `master` commit `85cca97` (PR #32 merged), 10 PRs after
the previous handoff.

This document is self-contained: a fresh session can read it and start
working without scrolling history.

> ⚠️ **Caveat**: file-line numbers below were correct at the time of writing
> but drift with each PR. Re-derive with the build commands in *Build / dev*
> before acting on a specific location.

## TL;DR

- **Sorries: 17.** **Axioms: 38** (every axiom cites a paper-§ or names a
  future-PR target).
- **Front B is fully discharged** — `liminfGap_one_le_iff`,
  `twinPrimes_iff_liminfGap_one`, `dhl_implies_liminfGap` all real.
- **Front A is statement-fixed and structurally decomposed.** `maynard_thm`,
  `epsilon_trick`, `exists_F_*` all real. Only the two
  `selberg_sieve_data_*_from_F` analytic-core leaves remain in Front A —
  these are the Polymath8b §3 `prime-asym` / `nonprime-asym` consumers.
- **Every §1 H_m flagship is now real-down-to-leaves**: `H1_le_246`,
  `H2_le_398130`, `H1_le_6_under_GEH`, etc., all chain through real Lean
  to the same two §3 analytic cores. Same for `Targets.H1_le_246`,
  `Maynard.H1_le_600`, `H2_le_600_under_EH`, etc.
- **Paper-faithful threshold fixes**: `maynard_thm`/`epsilon_trick` now
  use `2m/ϑ` (was `4m/ϑ`); 4 EH witness axioms restated honestly.
- **Strategy note** in `papers/README.md` explains why Polymath8b stays
  the formalization target despite being 12 years old.

## Operating principles (locked in, keep)

1. **Axioms at leaves with citations.** Three flavors:
   - *External evidence* — paper-§ numerical, exhaustive enumerations,
     Brun-Titchmarsh, Clark-Jarvis (Polymath8b §3, §6, etc.).
   - *Substantive bookkeeping* — `DHL_gives_freq_primeAt_gap` (~200 lines
     of `Finset`/`Nat.count` translation), `narrowness_realized`
     (Hensley-Richards / Erdős $k$-tuple construction),
     `Mk_le_one_of_k_le_one` (Cauchy-Schwarz on the unit interval).
   - *Structural set-theoretic* — `MkSet_nonempty`, `MkSet_bddAbove` (and
     `_eps` sisters). All have TRIAGE notes pointing at "future PR can
     replace with real proof".
2. **Twig-splitting decomposition.** Decompose mega-sorries into 2-4
   named sub-lemmas with paper-§ citations; turn the original theorem
   into a real composition. **Increasing the sorry count by 1-3 is fine
   if each new sorry is independently smaller and citable.** Template:
   PRs #25 (`maynard_thm`), #26 (`epsilon_trick`), #30
   (`dhl_implies_liminfGap`).
3. **Verify against the paper, not against the handoff.** The Polymath8b
   §5 source is `papers/src/polymath8b-1407.4897/newergap-submitted.tex`.
   Two threshold bugs were caught this way (J_k integrand in the prior
   session; 2× threshold in this session). The HANDOFF can lie — the
   paper TeX is the source of truth.
4. **Better metrics than raw sorry count**:
   - *PROVABLE-sorries* — strip out cited-axiom candidates.
   - *DAG-closed depth* — for a flagship, fraction of the dependency DAG
     that is real-or-cited-axiom all the way to leaves.
   - *Honest-debt sum* = `sorries + uncited-opaques + uncited-axioms`.
     Inflating axioms while shrinking sorries is a wash.

## Build / dev

```bash
cd ~/src/bounded_gaps

# full build, ~50s warm:
lake build

# incremental:
lake build BoundedGaps.Sieve

# authoritative sorry count:
lake build 2>&1 | grep -c "declaration uses .sorry."

# sorry locations (by file):
lake build 2>&1 | grep "declaration uses .sorry." | awk '{print $2}' | sort

# axiom inventory:
grep -rn "^axiom\b" BoundedGaps/*.lean | wc -l
grep -rn "^axiom\b" BoundedGaps/*.lean

# branch + ship workflow (master is protected, GHA queues 30+ min):
git checkout master && git pull
git checkout -b <feature-name>
# ... edits ...
git add <files> && git commit -m "..."
git push -u origin <feature-name>
gh pr create --title "..." --body "..."
gh pr merge --admin --merge       # fast, bypasses GHA queue
```

**Pre-commit hook blocks commits to master.** Feature branches only.

**`cd` doesn't persist across Bash calls** in the Claude harness — `cd ~/src/bounded_gaps && ...` per call.

## Current state of play (2026-05-26 afternoon)

### What's real all the way to cited-axiom leaves

- **Engelsma.lean** — entire tuple harvest. `tuple_5511_admissible` axiomatized
  (MIT primegaps); everything else real (`native_decide` through k = 54).
- **Polymath8b §7 parity barrier** — informal-axiom leaf.
- **Polymath8b §3 narrowness bounds / Theorem `hk-bound`** — all 14
  declarations real or cited-axiom. Clark-Jarvis (k=50,51,54), MIT
  primegaps (k=5511, k≥35410), Hensley-Richards (asymp upper),
  Brun-Titchmarsh (asymp lower).
- **Sieve.lean variational scaffolding** — `simplex`, `simplex_eps`,
  `simplex_shrunk`, `mkF_(eps_)?numerator`, `mkF_(eps_)?denominator`,
  `MkF`, `MkF_eps`, `Mk`, `Mk_eps`. All concrete `noncomputable def`s.
- **`dhl_criterion`** (PR #17, prior session) — real 3-line composition
  of two §3 sub-lemmas.
- **`Sieve.maynard_thm`** (PR #25) — real 3-line composition:
  `dhl_criterion` ∘ `exists_F_of_Mk_gt` ∘ `selberg_sieve_data_from_F`.
- **`Sieve.epsilon_trick`** (PR #26) — same template, `_eps` flavor.
- **`exists_F_of_Mk_gt`** + **`exists_F_eps_of_Mk_eps_gt`** (PR #27) —
  real via `lt_csSup_iff` + 4 cited side-condition axioms
  (`MkSet_(eps_)?{nonempty,bddAbove}`).
- **`Basic.liminfGap_one_le_iff`** (PR #28) — real via `Filter.liminf_le_iff`
  + `Nat.nth Nat.Prime` helpers (`primeAt_prime`, `primeAt_lt_succ`,
  `primeAt_succ_le_of_prime_gt`).
- **`TwinPrimes.twinPrimes_iff_liminfGap_one`** (PR #29) — real, composing
  PR #28 with `liminfGap_one_ge_two` + the (2,3) edge case.
- **`Basic.dhl_implies_liminfGap`** (PR #30) — real via two cited axioms
  (`narrowness_realized`, `DHL_gives_freq_primeAt_gap`) + the m=0 trivial
  case + PR #28's `liminfGap_le_iff_freqGap` generalization.
- **`Targets.H1_le_of_Mk_witness`** (PR #32) — real via `maynard_thm`
  with `ϑ := 1/Mk + 1/4` constructed from `Mk > 4`, BV gives EH, plus
  `Mk_le_one_of_k_le_one` cited axiom for `k ≥ 2` extraction.
- **Maynard upcasts** (PR #31) — `H1_le_600`, `H2_le_600_under_EH`, both
  asymptotic bounds. Trivial upcasts from Polymath8b's stronger versions
  (`m ≤ m^3` envelope).
- **All Polymath8b §1 flagships** — `H1_le_246`, `H2_le_398130`,
  `H3_le_24797814`, `H4_le_1431556072`, `H5_le_80550202480`,
  `H2_le_270_under_EH` and friends. Real bodies chaining through real
  `dhl_*_under_EH` flagships + real `dhl_implies_liminfGap`.

### Remaining sorries (17, by file)

```
BoundedGaps/Sieve.lean:108           witness_eventually_from_sieve_data
BoundedGaps/Sieve.lean:382           selberg_sieve_data_from_F
BoundedGaps/Sieve.lean:418           maynard_trunc                (statement-buggy)
BoundedGaps/Sieve.lean:453           selberg_sieve_data_eps_from_F
BoundedGaps/Sieve.lean:495           epsilon_beyond               (statement-buggy)
BoundedGaps/SievePolynomial.lean:88  polynomialMaynardNumerator (def body)
BoundedGaps/SievePolynomial.lean:96  polynomialMaynardDenominator (def body)
BoundedGaps/SievePolynomial.lean:115 polynomialMkF_eq_MkF
BoundedGaps/SievePolynomial.lean:127 Mk_ge_polynomialMkF
BoundedGaps/Polymath8b.lean:176      dhl_asymptotic_unconditional
BoundedGaps/Polymath8b.lean:209      dhl_asymptotic_under_EH
BoundedGaps/Polymath8b.lean:364      hm_asymp_from_dhl_and_narrowness
BoundedGaps/Polymath8b.lean:589      twin_primes_or_near_miss_Goldbach
BoundedGaps/Prerequisites.lean:90    geh_implies_eh        (unprovable as stated)
BoundedGaps/Prerequisites.lean:96    eh_implies_mpz        (unprovable as stated)
BoundedGaps/Maynard.lean:86          H1_le_12_under_EH     (needs new k=5 flagship)
BoundedGaps/Zhang.lean:34            H1_le_70M             (method-faithful, leave)
```

### The Front A analytic core (only Front A work left)

The two `selberg_sieve_data_*_from_F` sorries are the only Front A leaves.
Both follow the same paper structure (Polymath8b §3 + §5):

```
selberg_sieve_data_from_F  (and _eps sister)
  := compose
       ν_def_from_F           -- Selberg weight construction (Polymath8b §3 nuform)
       s1_holds_from_F        -- (s1) via Polymath8b nonprime-asym (line 889 in TeX)
       s2_holds_from_F        -- (s2) via Polymath8b prime-asym (line 862 in TeX)
       key_from_MkF           -- ∑β/α > m via the MkF > 2m/ϑ structural relation
```

The natural next PR is a 4-way decomposition of `selberg_sieve_data_from_F`,
surfacing `prime-asym` and `nonprime-asym` as cited Polymath8b §3 axioms.
Same template as PRs #25 (`maynard_thm`), #26 (`epsilon_trick`), #30
(`dhl_implies_liminfGap`). Net +3 to +6 sorries, each focused and citable.

### Front A statement fixes still needed (PR-A1b)

`maynard_trunc` and `epsilon_beyond` have buggy statements (carried over
from before PR #24). Both need *new definitions*, not just numeric edits:

- `maynard_trunc` uses `Mk` (unrestricted sup) where the paper has
  `M_k^[α]` (sup over the *truncated* simplex `t_i ≤ α`). Need a
  `Mk_truncated` def + `MkSet_truncated` named set + `_nonempty`/`_bddAbove`
  cited axioms. Plus 2× threshold fix (`4m/(1/2+2ϖ)` → `m/(1/4+ϖ)` on
  truncated `Mk`).
- `epsilon_beyond` uses `Mk_eps` (sup over all admissible F on
  `(1+ε)·R_k`) where the paper takes a *specific* F with vanishing-marginal
  condition on `(k/(k-1))·R_k`. Need a vanishing-marginal-F predicate +
  a different shape of hypothesis.

These are deferred because they're structural definition work, not the
clean numeric edits in PR #24.

### Smaller open items

- **`Polymath8b.hm_asymp_from_dhl_and_narrowness`** (1 sorry) —
  asymptotic combinator. Now diggable since `dhl_implies_liminfGap` is real.
  ~100 lines of `Real.log` + `Nat.ceil` + `Filter.IsBigO` bookkeeping.
- **`Polymath8b.dhl_asymptotic_{unconditional, under_EH}`** (2 sorries) —
  need asymptotic Mk lower bound at scale (`Mk_asymptotic_lower` cited
  axiom not yet in project) + uniform application of `maynard_thm`.
- **`Maynard.H1_le_12_under_EH`** (1 sorry) — needs a new k=5 flagship
  chain parallel to k=54/5511/41588/309661. `mk_5_witness_under_EH` cited
  axiom + `dhl_5_2_under_EH` real proof + `narrowness_5_le_12`.
- **`SievePolynomial.lean`** (4 sorries) — polynomial sieve weight
  machinery. Subtle: polynomials don't have compact support, so the
  obvious upcast `polynomialMkF_eq_MkF` is actually a bump-multiplication
  limit argument. Stale TRIAGE comments claim cheap; reality is deeper.
- **`Sieve.witness_eventually_from_sieve_data`** (1 sorry) — Polymath8b §3
  Lemma `crit` paragraphs 1-3. Pigeonhole step. Needs project-level
  Chebyshev-θ def.
- **`Prerequisites.{geh_implies_eh, eh_implies_mpz}`** — **NOT 15-min wins**
  despite earlier HANDOFF claim. `EH` and `GEH` are opaque `Prop`s in the
  project; the implications can't be proven without modeling them
  concretely. Both need a substantial design pass first.
- **`twin_primes_or_near_miss_Goldbach`** — Polymath8b §8, multi-week
  BLUEPRINT. Don't touch until everything else lands.
- **`Zhang.H1_le_70M`** — method-faithful Zhang. Captured as corollary
  via `H1_le_70M_via_Polymath8b` (real, PR #20). Leave the
  method-faithful version as a tracked sorry.

### Cited axioms added this session (10 new)

| Axiom | Purpose | Future-PR target |
|---|---|---|
| `MkSet_nonempty` | for k ≥ 2, admissible-F set non-empty | smooth-bump construction |
| `MkSet_bddAbove` | admissible-F set bounded above | Polymath8b Cor `mk-upper`, $M_k \le \tfrac{k}{k-1}\log k$ |
| `MkSet_eps_nonempty` | sister for `Mk_eps` | enlargement of bump |
| `MkSet_eps_bddAbove` | sister for `Mk_eps` | sister bound |
| `narrowness_realized` | for k ≥ 1, narrowness inf is achieved | Hensley-Richards / Erdős $k$-tuple construction |
| `DHL_gives_freq_primeAt_gap` | DHL[k, m+1] + admissible tuple ⟹ ∃ᶠ j with bounded indexed prime gap | ~200 lines `Finset` min/max + countP-to-count + n↦j injection |
| `Mk_le_one_of_k_le_one` | M_k ≤ 1 for k ≤ 1 | Cauchy-Schwarz on unit interval |

Plus the 4 EH witness axioms in Polymath8b.lean were *restated* (not new) to
match the paper-faithful `2m/ϑ` threshold.

## Mathlib lemmas / patterns that came up

Things this session used that future work will likely also use:

- `Filter.liminf_le_iff (h₁ : IsCoboundedUnder ...) (h₂ : IsBoundedUnder ...) : liminf u f ≤ x ↔ ∀ y > x, ∃ᶠ a in f, u a < y` — for ℕ∞ apply at `y = ↑(H+1)` to convert strict to non-strict.
- `Filter.le_liminf_iff` — dual, for lower bounds on `liminf`.
- `Filter.Frequently.mono : (∃ᶠ a, P a) → (∀ a, P a → Q a) → ∃ᶠ a, Q a`.
- `Filter.frequently_atTop : (∃ᶠ n in atTop, P n) ↔ ∀ a, ∃ b ≥ a, P b`.
- `Filter.liminf_const : liminf (fun _ => c) f = c` (in nice settings).
- `Nat.nth_strictMono Nat.infinite_setOf_prime : StrictMono (Nat.nth Nat.Prime)`.
- `Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n : (Nat.nth Nat.Prime n).Prime`.
- `Nat.nth_count (hpn : p n) : Nat.nth p (Nat.count p n) = n` — round-trip.
- `Nat.nth_lt_of_lt_count : k < Nat.count p n → Nat.nth p k < n`.
- `Nat.nth_prime_zero_eq_two : Nat.nth Nat.Prime 0 = 2`.
- `Nat.Prime.odd_of_ne_two : p.Prime → p ≠ 2 → Odd p`.
- `Nat.Prime.even_iff : p.Prime → (Even p ↔ p = 2)`.
- `Set.Infinite.diff (h : s.Infinite) (h' : t.Finite) : (s \ t).Infinite`.
- `lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ ∃ b ∈ s, a < b`.
- `pow_le_pow_right₀ (h : 1 ≤ a) (h' : n ≤ m) : a^n ≤ a^m` — the `₀` suffix is the zero-witness form.
- `one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1/a < 1/b ↔ b < a` — NOT `div_lt_div_iff` (doesn't exist).
- `div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c`.
- `ENNReal.ofReal_le_ofReal : a ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b`.
- `Real.exp_le_exp.mpr : a ≤ b → Real.exp a ≤ Real.exp b`.

## Gotchas from this session

- **The `2m/ϑ` paper threshold bug** — Polymath8b §5 line 935 has `M_k > 2m/ϑ`,
  the Lean had `4m/ϑ` (twice). Witness axioms inflated to match made the
  chain typecheck but lied about citation. PR #24 fixed. **Always read the
  TeX before encoding a threshold.**
- **`Mk` over the wrong support polytope** — `maynard_trunc` and
  `epsilon_beyond` both have this issue. Paper uses a different sup (truncated
  simplex, or specific-F-with-vanishing-marginal). Lean uses bare `Mk` /
  `Mk_eps`. Punted to PR-A1b.
- **`narrowness k` for k without admissible tuples** — `sInf ∅ = 0` (Nat
  convention) but `DHL k (m+1)` is vacuously true. Original
  `dhl_implies_liminfGap` was vacuously *false* for such k. Fixed by
  axiomatizing `narrowness_realized` for k ≥ 1.
- **Polynomials don't have compact support** — `SievePolynomial.Mk_ge_polynomialMkF`
  looks like a cheap `le_csSup` but actually requires a bump-multiplication
  limit argument because `P.toFun` doesn't sit in `MkSet k`. TRIAGE was
  optimistic.
- **`Prerequisites.{geh_implies_eh, eh_implies_mpz}` are NOT 15-min wins**.
  The TRIAGE comments in the file say it explicitly: `EH`/`GEH` are opaque
  `Prop`s, the implications can't be proven without concrete models. Earlier
  HANDOFF claim was wrong.
- **`change` not `show`** — Lean 4.29.1's `linter.style.show` warns on `show`
  that changes (not annotates) the goal. Use `change` for goal-rewrites.
- **Import cycle Polymath8b → Maynard** — the previous direction was vestigial;
  removing the dead `import BoundedGaps.Maynard` from Polymath8b.lean enabled
  the trivial Maynard upcasts. Maynard now correctly imports Polymath8b.

## Recommended next-session plan

Trevor's guidance: **read papers, decompose knarly bits into smaller pieces,
fine to increase sorry count as long as each piece is easier.** Verify against
the paper at every threshold.

Suggested order:

1. **Warm-up** (~10 min): re-derive sorry count + locations; confirm Front A
   selberg cores are the only substantive Front A work; scout
   `SievePolynomial.lean` if you want a side-quest.
2. **PR-A5: Decompose `selberg_sieve_data_from_F`** (~1-2h) — the natural
   next move. Read Polymath8b §3 `prime-asym` (TeX line 862) and
   `nonprime-asym` (line 889). Twig-split into `ν_def_from_F`,
   `s1_holds_from_nonprime_asym`, `s2_holds_from_prime_asym`,
   `key_from_MkF`. The first three become sorries citing Polymath8b §3;
   the last (`key_from_MkF`) should be a real algebra proof. Net +3 to +6
   sorries, each focused. Same pattern for the `_eps` sister (PR-A6).
3. **PR-A1b: `maynard_trunc` + `epsilon_beyond` statement fixes** (~1-2h) —
   need new `Mk_truncated` def + `MkSet_truncated_{nonempty, bddAbove}`
   axioms + a vanishing-marginal-F predicate. Substantive structural work.
4. **PR-E: `hm_asymp_from_dhl_and_narrowness`** (~1-2h) — now achievable
   since `dhl_implies_liminfGap` is real. Substantive `IsBigO` +
   `Real.log` + ceiling arithmetic. Future PR can replace.
5. **Cited-axiom dischargements over time** — turn the structural axioms
   (`MkSet_nonempty`, `MkSet_bddAbove`, `Mk_le_one_of_k_le_one`,
   `narrowness_realized`, `DHL_gives_freq_primeAt_gap`) into real proofs.
   Each is a self-contained PR. Together they reduce honest-debt by 7+.

## Pointers outside the repo

- Knowledge base: `~/personal/claude/knowledge/core/projects/lean-journey/side-quests/`
  - `bounded-gaps.md` — project arc.
  - `bounded-gaps-threads.md` — thread tracker (current through PR #32).
  - `sieve-mkf-handoff.md` — prior session's handoff (completed).
- Memory: `~/personal/claude/memory/`
  - `feedback_axioms_at_leaves.md` — the operating principle.
  - `feedback_verify_against_paper.md` — the threshold-bug lesson.
  - `reference_formalization_metrics.md` — better-than-sorry-count metrics.
  - `reference_lean_tactics_gotchas.md` — Lean v4.29.1 / mathlib landmines.
- Papers: `papers/src/polymath8b-1407.4897/newergap-submitted.tex` is the
  canonical Polymath8b source. `papers/README.md` now has a
  "Why Polymath8b is the formalization target" strategy section.

---

🪷 Last commit on `master` when this file was written: `85cca97`
(merge of PR #32 *Targets.H1_le_of_Mk_witness real*). 10 PRs since the
prior HANDOFF (#24 - #32 + this file's PR).
