# HANDOFF.md — Bounded Gaps Lean project

Written 2026-05-27 (early morning), superseding the 2026-05-26 evening
version. Reflects state at `master` commit `3507f0e` (PR #43 merged),
**6 PRs after the previous handoff** (#39, #40, #41, #42, #43, plus
this refresh #44).

This document is self-contained: a fresh session can read it and start
working without scrolling history.

> ⚠️ **Caveat**: file-line numbers below were correct at the time of writing
> but drift with each PR. Re-derive with the build commands in *Build / dev*
> before acting on a specific location.

## TL;DR

- **Sorries: 23.** **Axioms: 34.** **Opaques: 3** (`alphaBound`, `betaBound`,
  `selberg_nu` — all real-but-unencoded defs, by project convention).
- **The project has a `ROADMAP.md` now** (PR #40). Replaces sorry-count
  with "depth into the sieve" as the strategic metric. 4 axiom-buckets:
  - **A (28)** = forever-cite by design (BV/EH/GEH/MPZ, paper §6 numerical,
    Engelsma, admissibility bounds, asymptotic narrowness)
  - **B & C** = formerly mis-typed; **reclassified as sorries 2026-05-27**
    (PR #41). 9 axioms → 9 sorries; honest-debt unchanged but metric
    stops lying.
  - **D (5 axioms + 3 opaques)** = the actual sieve core. This is the
    real bar; ROADMAP Tier 1 (encode opaques) + Tier 3-4 (discharge
    `wtrick_data`, first `s1`/`s2`) are the real-progress milestones.
- **`epsilon_beyond` is paper-faithful** (PR #39, PR-A1b-ii): explicit $F$
  witness + vanishing-marginal predicate + `J_i_beyond` (third marginal
  def with unclamped inner $[0,\infty)$). Body still a sorry; same blocker
  as `maynard_trunc` (needs a `selberg_sieve_data_*_from_F` sister).
- **`maynard_trunc` is paper-faithful** (PR-A1b-i #37, prior session): now
  uses `Mk_truncated` on the truncated simplex. Body still a sorry.
- **Mid-session structural wins (PR #42, #43):**
  - `Mk_zero_le_one` extracted as standalone discharged theorem
    ($M_0 \le 1$ via `mkF_numerator | 0, _ => 0`).
  - `MkSet_truncated_bddAbove` discharged via subset of `MkSet`
    (routes through `MkSet_bddAbove`'s sorry; local body is real).
  - `SieveTheoreticArgument` + `parity_barrier` removed as
    documentation-as-axiom (never consumed, pure trust-base shrink).

## Session ledger (since 2026-05-26 evening)

| PR | What | Net effect |
|---|---|---|
| #38 | HANDOFF refresh (covers PRs #34-#37) | doc only |
| #39 | epsilon_beyond paper-faithful (PR-A1b-ii) | restate; axioms unchanged |
| #40 | Add ROADMAP.md (depth-into-sieve reframe) | doc only |
| #41 | Reclassify 9 mis-typed axioms → sorries | axioms 45→36, sorries 15→24 |
| #42 | `MkSet_truncated_bddAbove` discharge + `Mk_zero_le_one` extract | sorries 24→23 |
| #43 | Remove `SieveTheoreticArgument` + `parity_barrier` | axioms 36→34 |
| #44 | This HANDOFF refresh + ledger update | doc only |

## Operating principles (locked in, keep)

1. **`opaque` vs `axiom` at leaves.** The project distinguishes:
   - **`opaque`** — for leaves with a REAL underlying def, just unencoded.
     Today: `alphaBound`, `betaBound`, `selberg_nu`. Sister
     `noncomputable def`s exist in principle (Polymath8b §3 eqns (s1),
     (s2), `nuform`); the project hasn't encoded them yet.
   - **`axiom`** — for leaves CITING external truths. Paper-§ numerical
     bounds, exhaustive enumerations (Engelsma), Brun-Titchmarsh, W-trick,
     etc.
   - **Don't auto-convert one to the other** to chase a slogan. PR #36 was
     a revert after an in-session push toward "axioms at leaves" flipped
     `selberg_nu` from opaque to axiom incorrectly — see
     `~/personal/claude/memory/feedback_lean_opaque_vs_axiom.md`.
2. **Axioms at leaves with citations.** Three flavors of axiom:
   - *External evidence* — paper-§ numerical, exhaustive enumerations,
     Brun-Titchmarsh, Clark-Jarvis (Polymath8b §3, §6, etc.).
   - *Substantive bookkeeping* — `DHL_gives_freq_primeAt_gap` (~200 lines
     of `Finset`/`Nat.count` translation), `narrowness_realized`
     (Hensley-Richards / Erdős $k$-tuple construction),
     `Mk_le_one_of_k_le_one` (Cauchy-Schwarz on the unit interval).
   - *Structural set-theoretic* — `MkSet_nonempty`, `MkSet_bddAbove`
     (and `_eps`/`_truncated` sisters). All have TRIAGE notes pointing at
     "future PR can replace with real proof".
3. **Twig-splitting decomposition.** Decompose mega-sorries into 2-4
   named sub-lemmas with paper-§ citations; turn the original theorem
   into a real composition. **Increasing the sorry count by 1-3 is fine
   if each new sorry is independently smaller and citable.** Template
   PRs: #17, #25, #26, #30, **#34 (PR-A5)**, **#35 (PR-A6)**.
4. **Verify against the paper, not against the handoff.** The Polymath8b
   §5 source is `papers/src/polymath8b-1407.4897/newergap-submitted.tex`.
   Three threshold/statement bugs caught this way (the J_k integrand,
   the 2× threshold in maynard_thm, and now the truncated-simplex in
   maynard_trunc). The HANDOFF can lie — the paper TeX is the source of
   truth.
5. **Better metrics than raw sorry count**:
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
grep -c "^axiom\b" BoundedGaps/*.lean | awk -F: '{n+=$2} END {print "axioms:", n}'
grep -rn "^axiom\b" BoundedGaps/*.lean

# opaque inventory:
grep -rn "^opaque\b" BoundedGaps/*.lean

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

## Current state of play (2026-05-26 evening)

### What's real all the way to cited-axiom leaves

- **Engelsma.lean** — entire tuple harvest. `tuple_5511_admissible` axiomatized
  (MIT primegaps); everything else real (`native_decide` through k = 54).
- **Polymath8b §7 parity barrier** — informal-axiom leaf.
- **Polymath8b §3 narrowness bounds / Theorem `hk-bound`** — all 14
  declarations real or cited-axiom.
- **Sieve.lean variational scaffolding** — `simplex`, `simplex_eps`,
  `simplex_truncated` (new in PR-A1b-i), `simplex_shrunk`, all four
  numerator/denominator pairs, `MkF`, `MkF_eps`, `Mk`, `Mk_eps`,
  `Mk_truncated` (new). All concrete `noncomputable def`s. Plus
  `MkF_eps_eq_rayleigh` rfl theorem (new in PR-A6).
- **`dhl_criterion`** (PR #17) — real 3-line composition.
- **`Sieve.maynard_thm`** (PR #25) — real composition of `dhl_criterion`
  + `exists_F_of_Mk_gt` + `selberg_sieve_data_from_F`.
- **`Sieve.epsilon_trick`** (PR #26) — same template, `_eps` flavor.
- **`exists_F_of_Mk_gt`** + **`exists_F_eps_of_Mk_eps_gt`** (PR #27).
- **`Basic.liminfGap_one_le_iff`** (PR #28) — real.
- **`TwinPrimes.twinPrimes_iff_liminfGap_one`** (PR #29) — real.
- **`Basic.dhl_implies_liminfGap`** (PR #30) — real.
- **`Targets.H1_le_of_Mk_witness`** (PR #32) — real.
- **Maynard upcasts** (PR #31) — `H1_le_600`, `H2_le_600_under_EH`, both
  asymptotic bounds.
- **🆕 `Sieve.selberg_sieve_data_from_F`** (PR-A5 #34) — real, decomposed
  into 4 cited axioms (`selberg_nu` opaque + `wtrick_data` +
  `s1_holds_from_nonprime_asym` + `s2_holds_from_prime_asym_under_EH`)
  + the algebraic key step $(\vartheta/2) \cdot M_k(F) > m$.
  `#print axioms` shows no `sorryAx` in its chain.
- **🆕 `Sieve.selberg_sieve_data_eps_from_F`** (PR-A6 #35) — real, mirror
  of PR-A5 with 2 ε-specific new axioms (`s1_eps_holds_*`,
  `s2_eps_holds_*`); reuses `selberg_nu` and `wtrick_data`.
- **All Polymath8b §1 flagships** — `H1_le_246`, `H2_le_398130`,
  `H3_le_24797814`, `H4_le_1431556072`, `H5_le_80550202480`,
  `H2_le_270_under_EH` and friends. Real bodies chaining through real
  `dhl_*_under_EH` flagships + real `dhl_implies_liminfGap` + the now-real
  Front A cores.

### Remaining sorries (15, by file)

```
BoundedGaps/Sieve.lean:108            witness_eventually_from_sieve_data
BoundedGaps/Sieve.lean:638            maynard_trunc        (now paper-faithful;
                                                            blocked on selberg
                                                            sieve data truncated)
BoundedGaps/Sieve.lean:796            epsilon_beyond       (statement-buggy;
                                                            PR-A1b-ii target)
BoundedGaps/SievePolynomial.lean:88   polynomialMaynardNumerator (def body)
BoundedGaps/SievePolynomial.lean:96   polynomialMaynardDenominator (def body)
BoundedGaps/SievePolynomial.lean:115  polynomialMkF_eq_MkF
BoundedGaps/SievePolynomial.lean:127  Mk_ge_polynomialMkF
BoundedGaps/Polymath8b.lean:185       dhl_asymptotic_unconditional
BoundedGaps/Polymath8b.lean:218       dhl_asymptotic_under_EH
BoundedGaps/Polymath8b.lean:373       hm_asymp_from_dhl_and_narrowness
BoundedGaps/Polymath8b.lean:598       twin_primes_or_near_miss_Goldbach
BoundedGaps/Prerequisites.lean:90     geh_implies_eh        (unprovable as stated)
BoundedGaps/Prerequisites.lean:96     eh_implies_mpz        (unprovable as stated)
BoundedGaps/Maynard.lean:86           H1_le_12_under_EH     (needs new k=5 flagship)
BoundedGaps/Zhang.lean:34             H1_le_70M             (method-faithful, leave)
```

### Open work — recommended next moves

#### **PR-A1b-ii: `epsilon_beyond` statement fix** ✅ Done (PR #39)

`Sieve.epsilon_beyond` restated to match Polymath8b §5 line 1028-1037.
Three new defs added (`simplex_scaled`, `HasVanishingMarginal`,
`J_i_beyond`) plus `mkF_beyond_denominator`. Witness axioms
`mk_eps_{3,51}_witness_under_GEH` and consumers `dhl_{3_2,51_3}_under_GEH`
updated. Body still a `sorry` (same blocker as `maynard_trunc`).

#### **PR-A1b-iii: Discharge `maynard_trunc`'s body** (~1-2h)

With `Mk_truncated` infrastructure in place from PR-A1b-i, the natural next
move is a sister analytic-core lemma `selberg_sieve_data_truncated_from_F`
(same template as PR-A5/A6) — pick (b, W, ν), build (s1)/(s2) under MPZ
instead of EH. Polymath8b §3 `prime-asym` case (ii) MPZ + `nonprime-asym`
case (i) trivial. Adds 2-3 cited axioms; turns `maynard_trunc` real.

#### **PR-E: `hm_asymp_from_dhl_and_narrowness`** (~1-2h)

Now achievable since `dhl_implies_liminfGap` is real (PR #30). Substantive
`IsBigO` + `Real.log` + ceiling arithmetic. Future PR can replace.

#### **Structural sorry discharges** (now sorries, not axioms — per PR #41)

All of these were `axiom` until PR #41 reclassified them as
`theorem := sorry`. PR #42 discharged the first two:

| Theorem | Status | Effort |
|---|---|---|
| `Mk_le_one_of_k_le_one` (k = 0 case) | ✅ Done (PR #42 via `Mk_zero_le_one`) | trivial — `mkF_numerator 0 = 0` |
| `Mk_le_one_of_k_le_one` (k = 1 case) | sorry | smallish — Cauchy-Schwarz on $[0,1]$. Future PR; sketch in docstring. |
| `MkSet_truncated_bddAbove` | ✅ Done (PR #42 via subset) | routes through `MkSet_bddAbove` |
| `MkSet_nonempty` | sorry | medium — smooth-bump construction. Future PR. |
| `MkSet_bddAbove` | sorry | medium — Polymath8b Cor `mk-upper`. Future PR. |
| `MkSet_truncated_nonempty` | sorry | medium — bump inside truncated simplex |
| `MkSet_eps_nonempty` | sorry | tried PR #42, backed out: needs `Continuous.integrable_of_hasCompactSupport` chain. Future PR. |
| `MkSet_eps_bddAbove` | sorry | needs separate Polymath8b §5 `(1+ε)/(1-ε)` factor |
| `narrowness_realized` | sorry | medium — Hensley-Richards / Erdős |
| `DHL_gives_freq_primeAt_gap` | sorry | large — ~200 lines `Finset` bookkeeping |

#### **Sieve-core axioms (Bucket D — the real math)**

| Axiom | Effort |
|---|---|
| `selberg_nu` (opaque → real def) | 1-2 sessions — Polymath8b §3 `nuform` (3.6)-(3.7) explicit formula |
| `alphaBound` (opaque → real def) | 2-3 sessions — `Asymptotics.IsLittleO` shape for (s1) |
| `betaBound` (opaque → real def) | 2-3 sessions — sister of `alphaBound` for (s2) |
| `wtrick_data` | 5-15 sessions — Mertens products + CRT; needs mathlib API |
| `s1_holds_from_nonprime_asym` + sisters | 10-30 sessions — divisor-sum expansion |
| `s2_holds_from_prime_asym_under_EH` + sisters | 10-30 sessions — sister + EH |

Together: 12+ honest-debt reductions over time.

### Cited axioms added in PRs #34, #35, #37 (8 new)

| Axiom | Purpose | Future-PR target |
|---|---|---|
| `selberg_nu` (opaque) | Polymath8b §3 `nuform` (3.6)-(3.7) | encode as `noncomputable def` |
| `wtrick_data` | W-trick (b coprime to W, all b+h_i coprime) | Mertens + CRT |
| `s1_holds_from_nonprime_asym` | (s1) asymptotic from §3 line 889 (i) | divisor-sum expansion |
| `s2_holds_from_prime_asym_under_EH` | (s2) asymptotic from §3 line 862 (i) + EH | divisor-sum + EH |
| `s1_eps_holds_from_nonprime_asym` | (s1) ε-flavored, §5 epsilon-trick reduction | sister of above |
| `s2_eps_holds_from_prime_asym_under_EH` | (s2) ε-flavored, §5 epsilon-trick + EH | sister |
| `MkSet_truncated_nonempty` | for k ≥ 2 + α > 0, truncated F-set non-empty | smooth-bump on $\{t ≤ α\}$ |
| `MkSet_truncated_bddAbove` | truncated F-set bounded above | Polymath8b Cor `mk-upper` |

Plus 4 `mk_*_witness` axioms in Polymath8b.lean were *restated* in PR-A1b-i
(not net-added) to use `Mk_truncated` with paper-faithful thresholds.

## Mathlib lemmas / patterns that came up

Things this session used that future work will likely also use:

- `Filter.liminf_le_iff`, `Filter.le_liminf_iff`, `Filter.Frequently.mono`,
  `Filter.frequently_atTop`, `Filter.liminf_const` (Front B chain).
- `Nat.nth_strictMono Nat.infinite_setOf_prime`,
  `Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n`,
  `Nat.nth_count (hpn : p n)`, `Nat.nth_lt_of_lt_count`,
  `Nat.nth_prime_zero_eq_two`, `Nat.Prime.odd_of_ne_two`,
  `Nat.Prime.even_iff` (Front B chain).
- `Set.Infinite.diff`.
- `lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty)`.
- `pow_le_pow_right₀`, `one_div_lt_one_div`, `div_lt_iff₀`.
- `ENNReal.ofReal_le_ofReal`, `Real.exp_le_exp.mpr`.
- **New in PR-A5/A6**: `MeasureTheory.integral_nonneg fun _ => sq_nonneg _`
  (integral of a square ≥ 0); `Finset.mul_sum` (`b * ∑ = ∑ b *`);
  `mul_lt_mul_of_pos_left`; `field_simp` for `(ϑ/2) * (2m/ϑ) = m` with
  `ϑ ≠ 0` discharge.

## Gotchas from this session

(Carried forward from the PM session, plus new items from this evening.)

- **The `2m/ϑ` paper threshold bug** — Polymath8b §5 line 935 has `M_k > 2m/ϑ`,
  the Lean had `4m/ϑ`. PR #24 fixed.
- **The `Mk` vs `Mk_truncated` bug in `maynard_trunc`** — paper uses sup over
  the truncated simplex `{t ∈ [0,α]^k : ∑t_i ≤ 1}`, Lean used unrestricted
  `Mk`. Fixed in PR-A1b-i (#37). Same flavor of bug as the 2× threshold —
  both caught by reading the paper TeX, not the handoff.
- **`epsilon_beyond` is more invasive than `maynard_trunc`** to fix — the
  paper's $J_{i,1-\varepsilon}(F)$ uses inner integral over $[0, \infty)$,
  which only equals the existing `J_i_eps`'s clamped $[0, 1+\varepsilon -
  \sum s_j]$ when F is supported on $(1+\varepsilon) \cdot R_k$.
  epsilon-beyond's F is on $(k/(k-1)) \cdot R_k$ (larger), so a third
  `J_i_beyond` (or unclamped `J_i_eps`) def is needed. PR-A1b-ii deferred
  for this reason.
- **`opaque` vs `axiom` distinction** — PR #36 reverted `selberg_nu` from
  `axiom` back to `opaque` after an in-session push toward "axioms at
  leaves" flipped it incorrectly. Use `opaque` when there's a real
  underlying def (Polymath8b §3 `nuform`); use `axiom` for citing external
  truths. See feedback memory `feedback_lean_opaque_vs_axiom.md`.
- **`Prerequisites.{geh_implies_eh, eh_implies_mpz}` are NOT 15-min wins**.
  `EH`/`GEH` are opaque `Props`; implications can't be proven without
  concrete models. Both need a substantial design pass first.
- **`twin_primes_or_near_miss_Goldbach`** — Polymath8b §8, multi-week
  BLUEPRINT. Don't touch until everything else lands.
- **`change` not `show`** — Lean 4.29.1's `linter.style.show` warns on `show`
  that changes the goal. Use `change` for goal-rewrites.

## Recommended next-session plan

Trevor's guidance: **read papers, decompose knarly bits into smaller pieces,
fine to increase sorry count as long as each piece is easier.** Verify
against the paper at every threshold.

Suggested order:

1. **Warm-up** (~10 min): re-derive sorry count + locations; read
   `ROADMAP.md` to align on Bucket A/B/C/D and tier framework.
2. **PR-A1b-iii: discharge `maynard_trunc` + `epsilon_beyond` bodies**
   (~1-3h) — both blocked on the same `selberg_sieve_data_*_from_F` sister
   pattern. Two sub-options:
   - **PR-A1b-iii-a (truncated)**: build `selberg_sieve_data_truncated_from_F`
     using `Mk_truncated` infrastructure. Polymath8b §3 prime-asym/
     nonprime-asym case (ii) under MPZ.
   - **PR-A1b-iii-b (beyond)**: build `selberg_sieve_data_beyond_from_F`
     using `J_i_beyond` + `HasVanishingMarginal`. Polymath8b §3 under GEH.
   Both add 2-3 cited axioms each; turn their respective flagship bodies real.
3. **PR-E: `hm_asymp_from_dhl_and_narrowness`** (~1-2h) — substantive
   `IsBigO` + `Real.log` + ceiling arithmetic. Achievable since
   `dhl_implies_liminfGap` is real (PR #30).
4. **Tier 1 — encode the opaques** (~5-8 sessions total per ROADMAP)
   `selberg_nu` → `noncomputable def` via Polymath8b §3 `nuform` (3.6)-(3.7);
   then `alphaBound` and `betaBound` via `Asymptotics.IsLittleO`. Real
   structural milestone; "depth into sieve" 0/8 → 3/8.
5. **Small structural discharges** (each ~0.5-1 session):
   - `Mk_le_one_of_k_le_one` k=1 case via L²-Cauchy-Schwarz on $[0,1]$
     (sketch in Sieve.lean docstring).
   - `MkSet_eps_nonempty` via shared F witness from `MkSet_nonempty`
     (needs `Continuous.integrable_of_hasCompactSupport` chain, attempted
     and backed out in PR #42).
   - `MkSet_eps_bddAbove`: separate (1+ε)/(1-ε) factor argument.
6. **Tier 3 — `wtrick_data` discharge** (~5-15 sessions) — Mertens
   products + CRT density. The first sieve-core axiom discharge would
   be the first "Lean has touched the sieve" milestone — outside
   audiences would care.

## Pointers outside the repo

- **In-repo strategy doc**: `~/src/bounded_gaps/ROADMAP.md` — bucket
  classification + tier framework + 2026-06-26 measurement checkpoint.
  Read this before deciding what to work on.
- Knowledge base: `~/personal/claude/knowledge/core/projects/lean-journey/side-quests/`
  - `bounded-gaps.md` — project arc.
  - `bounded-gaps-threads.md` — thread tracker (current through PR #37,
    stale w.r.t. PRs #38-#44).
- Memory: `~/personal/claude/memory/` (also linked from MEMORY.md):
  - `feedback_axioms_at_leaves.md` — the operating principle.
  - `feedback_verify_against_paper.md` — the threshold-bug lesson.
  - `feedback_lean_opaque_vs_axiom.md` — `opaque` vs `axiom`
    distinction; don't auto-convert.
  - `reference_formalization_metrics.md` — better-than-sorry-count metrics.
  - `reference_lean_tactics_gotchas.md` — Lean v4.29.1 / mathlib landmines.
- Papers: `papers/src/polymath8b-1407.4897/newergap-submitted.tex` is the
  canonical Polymath8b source. `papers/README.md` has a "Why Polymath8b is
  the formalization target" strategy section.

---

🪷 Last commit on `master` when this file was written: `3507f0e` (merge of
PR #43 *SieveTheoreticArgument removal*). 6 PRs since the prior HANDOFF
(#39 epsilon_beyond, #40 ROADMAP, #41 reclassification, #42
MkSet_truncated_bddAbove + Mk_zero_le_one, #43 SieveTheoreticArgument
removal, #44 this refresh).
