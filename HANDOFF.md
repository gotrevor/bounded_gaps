# HANDOFF.md — Bounded Gaps Lean project

Written 2026-05-26 (evening), superseding the 2026-05-26 afternoon version.
Reflects state at `master` commit `b3157db` (PR #37 merged), 4 PRs after
the previous handoff (#34, #35, #36, #37).

This document is self-contained: a fresh session can read it and start
working without scrolling history.

> ⚠️ **Caveat**: file-line numbers below were correct at the time of writing
> but drift with each PR. Re-derive with the build commands in *Build / dev*
> before acting on a specific location.

## TL;DR

- **Sorries: 15.** **Axioms: 45.** **Opaques: 3** (`alphaBound`, `betaBound`,
  `selberg_nu` — all real-but-unencoded defs, by project convention).
- **Front A analytic cores are now real** (PR-A5 #34 + PR-A6 #35):
  both `selberg_sieve_data_from_F` and `selberg_sieve_data_eps_from_F` are
  decomposed into 4 cited axioms each (Selberg `nuform` opaque + W-trick +
  `nonprime-asym` + `prime-asym`-under-EH) plus a real algebra step. ε
  sister reuses `selberg_nu` and `wtrick_data` so its decomposition adds
  only 2 new cited axioms.
- **`maynard_trunc` is paper-faithful** (PR-A1b-i #37): now uses
  `Mk_truncated k (δ/(1/4+ϖ)) > m/(1/4+ϖ)` on the truncated simplex
  $\{t \in [0,\alpha]^k : \sum t_i \le 1\}$, matching Polymath8b §5
  `maynard-trunc` (line 957-966). The 4 `mk_*_witness` axioms (35410,
  1649821, 75845707, 3473955908) were restated to match. Body still a sorry
  pending a `selberg_sieve_data_truncated_from_F` sister.
- **`epsilon_beyond` is still statement-buggy** (PR-A1b-ii blocked, see
  *Open work* below) — needs a 3rd numerator def (paper's $J_{i,1-\varepsilon}$
  uses inner $[0,\infty)$ which only matches my `J_i_eps`'s clamped
  $[0, 1+\varepsilon - \sum]$ when F is supported on $(1+\varepsilon)\cdot R_k$;
  epsilon-beyond's F is on the larger $(k/(k-1))\cdot R_k$).

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

#### **PR-A1b-ii: `epsilon_beyond` statement fix** (~1-2h)

Paper Polymath8b §5 `epsilon-beyond` (line 1028-1037):

> Let $k \ge 2$, $m \ge 1$, $0 < \vartheta < 1$ with $\GEH[\vartheta]$,
> $0 < \varepsilon < 1/(k-1)$. Suppose there is a fixed non-zero
> square-integrable $F: [0,\infty)^k \to \mathbb{R}$ supported in
> $(k/(k-1)) \cdot \mathcal{R}_k$, such that for $i = 1, \ldots, k$ the
> **vanishing marginal condition** $\int_0^\infty F(t_1, \ldots, t_k)\,dt_i
> = 0$ holds whenever $\sum_{j \ne i} t_j > 1 + \varepsilon$. Suppose also
> that $\sum_i J_{i,1-\varepsilon}(F) / I(F) > 2m/\vartheta$. Then
> $\DHL[k, m+1]$ holds.

Current Lean uses `Mk_eps k ε > 2m/ϑ` (sup over F on the smaller
$(1+\varepsilon) \cdot R_k$ polytope) which is the wrong shape entirely.
Fix needs:

1. **`simplex_scaled k r := {t | (∀ i, 0 ≤ t i) ∧ ∑ t_i ≤ r}`** — generic
   r-scaled simplex. Refactor `simplex`/`simplex_eps` to use it if desired.
2. **`HasVanishingMarginal k ε F : Prop`** — the eqn 1029 predicate:
   ```
   ∀ i, ∀ s : Fin (k-1) → ℝ, (∀ j, 0 ≤ s j) → (∑ j, s j > 1 + ε) →
     ∫ ti in Set.Ici 0, F (i.insertNth ti s) = 0
   ```
3. **`J_i_beyond k F i`** or **`J_i_eps_unclamped k ε F i`** — a third
   marginal def with inner integral over $[0, \infty)$ (not clamped to
   $[0, 1+\varepsilon - \sum s_j]$ as `J_i_eps` is). For F supported on
   $(k/(k-1)) \cdot R_k$ with vanishing marginal, this is the paper's
   $J_{i,1-\varepsilon}(F)$. **Critical**: the existing `J_i_eps` cuts off
   the inner integral at $1+\varepsilon - \sum$ which only matches the
   paper for F on $(1+\varepsilon) \cdot R_k$; epsilon-beyond's F is on a
   larger polytope. Without this third def the existing `J_i_eps` would
   *undercount* the inner integral.
4. **`mkF_beyond_denominator k F := ∫ t in simplex_scaled k (k/(k-1)), F² `**
   — or just `∫ t, F²` since F has bounded support.
5. **Restate `epsilon_beyond`** to take `(F, ε, ϑ)` + the conditions
   (smooth, supported, nonzero, vanishing-marginal, denom > 0, threshold).
   Still sorry; same selberg-sieve blocker as `maynard_trunc`.
6. **Restate `mk_eps_3_witness_under_GEH` + `mk_eps_51_witness_under_GEH`**
   to package the F witness.
7. **Update `dhl_3_2_under_GEH` + `dhl_51_3_under_GEH`** consumers (the
   `obtain` shape changes).

Net: +2 axioms (`MkSet_beyond_*`? Or just keep witness-axiom form),
+3 real defs (simplex_scaled, HasVanishingMarginal, J_i_beyond), sorry
count unchanged (still a sorry, just paper-faithful).

#### **PR-A1b-iii: Discharge `maynard_trunc`'s body** (~1-2h)

With `Mk_truncated` infrastructure in place from PR-A1b-i, the natural next
move is a sister analytic-core lemma `selberg_sieve_data_truncated_from_F`
(same template as PR-A5/A6) — pick (b, W, ν), build (s1)/(s2) under MPZ
instead of EH. Polymath8b §3 `prime-asym` case (ii) MPZ + `nonprime-asym`
case (i) trivial. Adds 2-3 cited axioms; turns `maynard_trunc` real.

#### **PR-E: `hm_asymp_from_dhl_and_narrowness`** (~1-2h)

Now achievable since `dhl_implies_liminfGap` is real (PR #30). Substantive
`IsBigO` + `Real.log` + ceiling arithmetic. Future PR can replace.

#### **Cited-axiom dischargements over time**

Turn the structural axioms into real proofs. Each self-contained:

| Axiom | Effort |
|---|---|
| `Mk_le_one_of_k_le_one` | smallish — Cauchy-Schwarz on unit interval |
| `MkSet_nonempty` | medium — smooth-bump construction |
| `MkSet_bddAbove` | medium — Polymath8b Cor `mk-upper` |
| `MkSet_eps_*`, `MkSet_truncated_*` | sisters of above |
| `narrowness_realized` | medium — Hensley-Richards / Erdős |
| `DHL_gives_freq_primeAt_gap` | large — ~200 lines `Finset` bookkeeping |
| `wtrick_data` | medium — Mertens products + CRT |
| `s1_holds_from_nonprime_asym` + sisters | large — divisor-sum expansion |
| `s2_holds_from_prime_asym_under_EH` + sisters | large — divisor-sum |

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

1. **Warm-up** (~10 min): re-derive sorry count + locations; confirm Front A
   selberg cores are real; confirm `maynard_trunc` is paper-faithful.
2. **PR-A1b-ii: `epsilon_beyond` statement fix** (~1-2h, see *Open work*
   above) — add `simplex_scaled`, `HasVanishingMarginal`, `J_i_beyond`,
   `mkF_beyond_denominator`; restate `epsilon_beyond` to take an explicit
   F witness; restate 2 `mk_eps_*_witness_under_GEH` axioms; update 2
   downstream `dhl_*_under_GEH` consumers. Still a sorry but paper-faithful.
3. **PR-A1b-iii: discharge `maynard_trunc`** (~1-2h) — sister
   `selberg_sieve_data_truncated_from_F` lemma using `Mk_truncated`
   infrastructure now in place. Polymath8b §3 prime-asym/nonprime-asym
   case (ii) under MPZ.
4. **PR-E: `hm_asymp_from_dhl_and_narrowness`** (~1-2h) — substantive
   `IsBigO` + `Real.log` + ceiling arithmetic. Now achievable since
   `dhl_implies_liminfGap` is real.
5. **Cited-axiom dischargements over time** — each is a self-contained PR.
   `Mk_le_one_of_k_le_one` is the smallest (Cauchy-Schwarz on unit interval);
   that's the easiest single discharge to land first.

## Pointers outside the repo

- Knowledge base: `~/personal/claude/knowledge/core/projects/lean-journey/side-quests/`
  - `bounded-gaps.md` — project arc.
  - `bounded-gaps-threads.md` — thread tracker (current through PR #37).
- Memory: `~/personal/claude/memory/` (also linked from MEMORY.md):
  - `feedback_axioms_at_leaves.md` — the operating principle.
  - `feedback_verify_against_paper.md` — the threshold-bug lesson.
  - `feedback_lean_opaque_vs_axiom.md` (new) — `opaque` vs `axiom`
    distinction; don't auto-convert.
  - `reference_formalization_metrics.md` — better-than-sorry-count metrics.
  - `reference_lean_tactics_gotchas.md` — Lean v4.29.1 / mathlib landmines.
- Papers: `papers/src/polymath8b-1407.4897/newergap-submitted.tex` is the
  canonical Polymath8b source. `papers/README.md` has a "Why Polymath8b is
  the formalization target" strategy section.

---

🪷 Last commit on `master` when this file was written: `b3157db` (merge of
PR #37 *maynard_trunc paper-faithful*). 4 PRs since the prior HANDOFF
(#34 PR-A5, #35 PR-A6, #36 selberg_nu revert, #37 PR-A1b-i + this file's
PR).
