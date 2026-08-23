# HANDOFF.md — Bounded Gaps Lean project

> 🔀 **2026-08-23: master now IS the expedition.**  The `bump-v4.31.0` branch (which extended
> `path-a-selberg-nu` — 492 commits: the k-D weighted-Riemann build, the μ²/φ engine, the Mertens
> machinery, and the v4.29.1→v4.31.0→v4.33.1 forward-ports, all 5 headlines axiom-gated unchanged)
> was fast-forward merged to `master` and pushed.  No PR was needed and the long-parked "open the
> bounded_gaps PR" todo is retired.  **Everything below reflects the pre-merge 2026-05-28 state**
> (master@0946c81) and is stale in detail — trust the build commands, not the counts or line
> numbers.  Fresher state: `HANDOFF-v431-bump.md` (the port), `ANALYTIC_AXIOM_BURNDOWN.md`.

Written 2026-05-28, superseding the earlier 2026-05-28 version. Reflects
state at `master` commit `0946c81` (PR #62 merged), **5 PRs after the
previous handoff** (#55 selberg_nu_separable, #56 selberg_nu_basis, #59
lambdaTransform algebra, #61 orphan-axiom drop, #62 Mk≤1 k=1 discharge).

This document is self-contained: a fresh session can read it and start
working without scrolling history.

> ⚠️ **Caveat**: file-line numbers below were correct at the time of writing
> but drift with each PR. Re-derive with the build commands in *Build / dev*
> before acting on a specific location.

## TL;DR

- **Sorries: 15.** **Axioms: 37.** **Opaques: 3** (`alphaBound`, `betaBound`,
  `selberg_nu` — all real-but-unencoded defs, by project convention).
- **"Dig" round (PRs #61, #62)**: a systemic sweep produced the first two
  metric moves in a while. **#61**: a consumption audit (uses = grep count −
  decl) found `narrowness_asymptotic_lower` at **uses=0** — declared, never
  consumed — and dropped it (38 → 37 axioms, same class as `parity_barrier`
  in #43). **#62**: discharged the `Mk_le_one_of_k_le_one` **k=1** case
  (16 → 15 sorries) — `M_1(F)` collapses to a 1D Rayleigh ratio via the
  volume-preserving `MeasurableEquiv.funUnique (Fin 1) ℝ` change of
  variables, then Jensen for x↦x² on the probability space `[0,1]`. The
  lemma is consumed by `Targets.H1_le_of_Mk_witness` (load-bearing).
  Audit note: `geh_implies_eh`/`eh_implies_mpz` are *unconsumed sorries*
  but kept — honest visible debt, not orphans (a sorry shows debt; an
  orphan axiom hides risk).
- **Tier 1: the nuform construction ladder + lambda-algebra are now FULLY
  ENCODED** (PRs #52, #55, #56, #59). The chain `lambdaTransform` (1D
  Möbius-divisor operator) → `selberg_nu_separable` (separable case, J=1) →
  `selberg_nu_basis` (the full general nuform, eqn 837, a squared finite
  linear combination over an explicit basis `(J, c, Fs)`) is all real —
  zero axioms, zero sorries. `selberg_nu_basis_single` proves the J=1/c=1
  collapse equals `selberg_nu_separable`. PR #59 adds the algebraic toolkit:
  `lambdaTransform_prime` (λ_g(R,p) = g(0) − g(log p/log R), the
  unconditional identity underlying eqn (lambdan-prime)),
  `lambdaTransform_prime_of_support` (the paper's exact λ_F(p)=F(0)), and
  `_add`/`_smul`/`_neg`/`_linear` (g ↦ λ_g is linear). These are what the
  eventual s1/s2 divisor-sum expansions consume.
- **⚠️ The `selberg_nu` discharge is NOT a one-line `:=`** (key finding,
  2026-05-28). `selberg_nu` takes an arbitrary `F : (Fin k → ℝ) → ℝ`, but a
  *finite* separable decomposition `F = ∑_j c_j ∏_i F_{j,i}` does NOT exist
  for general `F`. So `selberg_nu := selberg_nu_basis` is impossible without
  basis data in scope, and forcing a concrete body (e.g. a rank-1 marginal)
  would make the s1/s2 axioms assert asymptotics about *that* weight —
  possibly **FALSE**, strictly worse than an honest opaque. Two documented
  paths (in the `selberg_nu` docstring + Open-work below): **(A)** a
  deliberate s1/s2 *signature* refactor — carry basis data `(J, c, Fs)`
  through the axiom statements so they only ever speak about
  `selberg_nu_basis`-built weights, then `selberg_nu` becomes real; **(B)**
  a cited "optimal F admits a finite ∑_j c_j ∏_i F_{j,i} representation"
  axiom (opaque stays, no metric move, lower risk). Depth-into-sieve metric:
  still **0/8** *opaques discharged*. NB: under either path,
  `alphaBound`/`betaBound`/`s1`/`s2` stay axioms (the deep analytic NT).
- **`hm_asymp_from_dhl_and_narrowness` is real** (PR #53): the §1 asymptotic
  combinator. Gained a `0 < α` hypothesis (both call sites satisfy it).
- **All 4 Polymath8b §5 flagships now have real composition bodies**:
  `maynard_thm`, `maynard_trunc` (PR #49), `epsilon_trick`,
  `epsilon_beyond` (PR #50). The truncated/beyond cases route through new
  `selberg_sieve_data_truncated_from_F` and `selberg_sieve_data_beyond_from_F`
  sisters of PR-A5/PR-A6, with 3 new cited axioms
  (`s2_holds_from_prime_asym_under_MPZ`, `s1_beyond_holds_from_nonprime_asym`,
  `s2_beyond_holds_from_prime_asym_under_GEH`).
- **The project has a `ROADMAP.md` now** (PR #40). Replaces sorry-count
  with "depth into the sieve" as the strategic metric. 4 axiom-buckets:
  - **A (28)** = forever-cite by design (BV/EH/GEH/MPZ, paper §6 numerical,
    Engelsma, admissibility bounds, asymptotic narrowness)
  - **B & C** = formerly mis-typed; **reclassified as sorries 2026-05-27**
    (PR #41). 9 axioms → 9 sorries; honest-debt unchanged but metric
    stops lying.
  - **D (8 axioms + 3 opaques)** = the actual sieve core (was 5 axioms;
    PRs #46, #49, #50 added s1/s2 sisters for the k=5, truncated, and
    beyond variants). **Tier 1 construction done, opaques not yet
    discharged** — the full nuform is encoded (`selberg_nu_basis` #56) but
    `selberg_nu`/`alphaBound`/`betaBound` are still opaque pending the
    s1/s2 interface decision (see Open work).
- **Mid-session structural wins (PR #42-#47):**
  - `Mk_zero_le_one` extracted as standalone discharged theorem
    ($M_0 \le 1$ via `mkF_numerator | 0, _ => 0`).
  - `MkSet_truncated_bddAbove` discharged via subset of `MkSet`
    (routes through `MkSet_bddAbove`'s sorry; local body is real).
  - `SieveTheoreticArgument` + `parity_barrier` removed as
    documentation-as-axiom (never consumed, pure trust-base shrink).
  - **`MkSet_eps_nonempty`** discharged (PR #45) via shared F witness from
    `MkSet_nonempty` + `setIntegral_mono_set` integrability chain. Added
    reusable `simplex_isClosed` / `simplex_isCompact` private helpers.
  - **`H1_le_12_under_EH`** discharged (PR #46) via new Maynard k=5 chain:
    `tuple_5 := [0, 4, 6, 10, 12]` + `tuple_5_admissible` (real proof via
    `admissible_of_check_small_primes` + `native_decide` on residues mod
    {2, 3, 5}) + `narrowness_5_le_12` (real) + `mk_5_witness_under_EH`
    (Bucket A citation) + `dhl_5_2_under_EH` (real).
  - **`polynomialMaynardNumerator` + `polynomialMaynardDenominator`**
    real def bodies (PR #47) — closed-form rational integrals via
    `monomialIntegral` and new `dirichletIntegralWithSlack` helper.

## Session ledger (since 2026-05-26 evening)

| PR | What | Net effect |
|---|---|---|
| #38 | HANDOFF refresh (covers PRs #34-#37) | doc only |
| #39 | epsilon_beyond paper-faithful (PR-A1b-ii) | restate; axioms unchanged |
| #40 | Add ROADMAP.md (depth-into-sieve reframe) | doc only |
| #41 | Reclassify 9 mis-typed axioms → sorries | axioms 45→36, sorries 15→24 |
| #42 | `MkSet_truncated_bddAbove` discharge + `Mk_zero_le_one` extract | sorries 24→23 |
| #43 | Remove `SieveTheoreticArgument` + `parity_barrier` | axioms 36→34 |
| #44 | HANDOFF + ROADMAP ledger refresh | doc only |
| #45 | `MkSet_eps_nonempty` discharge + `simplex_isCompact` infrastructure | sorries 23→22 |
| #46 | Maynard k=5 chain: `tuple_5`, `narrowness_5_le_12` (real), `mk_5_witness_under_EH` (axiom), `dhl_5_2_under_EH` (real), `H1_le_12_under_EH` discharged | sorries 22→21, axioms 34→35 |
| #47 | `polynomialMaynardNumerator` + `polynomialMaynardDenominator` real def bodies + `dirichletIntegralWithSlack` helper | sorries 21→19 |
| #48 | HANDOFF refresh after PRs #45-#47 | doc only |
| #49 | `maynard_trunc` discharge (PR-A1b-iii-a): new `selberg_sieve_data_truncated_from_F` + `exists_F_truncated_of_Mk_truncated_gt` + `s2_holds_from_prime_asym_under_MPZ` axiom; 4 truncated-Mk witness axioms updated to expose `0 < 1/4 + ϖ ∧ 0 < δ` | sorries 19→18, axioms 35→36 |
| #50 | `epsilon_beyond` discharge (PR-A1b-iii-b): new `selberg_sieve_data_beyond_from_F` + 2 new cited axioms (`s1_beyond_holds_from_nonprime_asym`, `s2_beyond_holds_from_prime_asym_under_GEH`) | sorries 18→17, axioms 36→38 |
| #51 | HANDOFF refresh + whitespace cleanup (`1/4` → `1 / 4`) | doc only |
| #52 | Tier-1 entry: real `lambdaTransform` Möbius-divisor operator + `lambdaTransform_{zero,one}` identities; `selberg_nu` docstring now names the basis-decomposition blocker | sorries/axioms unchanged (additive) |
| #53 | `hm_asymp_from_dhl_and_narrowness` discharged (real Filter/asymptotics proof); added `0 < α` hyp; 2 call sites updated | sorries 17→16 |
| #54 | HANDOFF + ROADMAP refresh | doc only |
| #55 | `selberg_nu_separable` (J=1 separable nuform from `lambdaTransform`) + `_nonneg`/`_zero_dim` | additive, real |
| #56 | `selberg_nu_basis` (full general nuform, eqn 837) + `_nonneg`/`_empty`/`_single` bridge to separable | additive, real |
| #57 | HANDOFF refresh after #55/#56 | doc only |
| #58 | HANDOFF + ROADMAP: finish the #55/#56 refresh (stale-string cleanup) | doc only |
| #59 | lambda-algebra: `lambdaTransform_prime`/`_prime_of_support`/`_add`/`_smul`/`_neg`/`_linear` (6 real lemmas) | additive, real |
| #60 | HANDOFF refresh after #59 + false-axiom finding | doc only |
| #61 | Drop orphan axiom `narrowness_asymptotic_lower` (uses=0) | axioms 38→37 |
| #62 | Discharge `Mk_le_one_of_k_le_one` k=1 via funUnique CoV + Jensen on [0,1] | sorries 16→15 |
| #63 | This HANDOFF + ROADMAP refresh | doc only |

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

### Remaining sorries (17, by file — re-derive with build commands as needed)

```
BoundedGaps/Basic.lean                 narrowness_realized, DHL_gives_freq_primeAt_gap
BoundedGaps/Prerequisites.lean         geh_implies_eh, eh_implies_mpz (both unprovable as stated)
BoundedGaps/Sieve.lean                 witness_eventually_from_sieve_data,
                                       MkSet_nonempty, MkSet_bddAbove,
                                       Mk_le_one_of_k_le_one (k=1 case),
                                       MkSet_truncated_nonempty,
                                       MkSet_eps_bddAbove
BoundedGaps/SievePolynomial.lean       polynomialMkF_eq_MkF, Mk_ge_polynomialMkF
BoundedGaps/Polymath8b.lean            dhl_asymptotic_unconditional,
                                       dhl_asymptotic_under_EH,
                                       hm_asymp_from_dhl_and_narrowness,
                                       twin_primes_or_near_miss_Goldbach
BoundedGaps/Zhang.lean                 H1_le_70M (method-faithful, leave)
```

**`maynard_trunc`, `epsilon_beyond`, `H1_le_12_under_EH`** are now real
composition bodies (PRs #46, #49, #50). No longer in the sorry list.

### Open work — recommended next moves

#### **Tier-1 push: discharge the `selberg_nu` opaque** (construction DONE)

ROADMAP estimated 5-8 sessions for `selberg_nu`, `alphaBound`, `betaBound`
→ real defs. **As of 2026-05-28 the nuform construction + lambda-algebra are
fully encoded** (`lambdaTransform` #52, `selberg_nu_separable` #55,
`selberg_nu_basis` #56, `lambdaTransform_*` algebra #59): the real general
weight `selberg_nu_basis k J c Fs H R n := (∑_j c_j ∏_i lambdaTransform
(Fs j i) R (n + h_i))^2` exists with no axioms/sorries,
`selberg_nu_basis_single` proves the J=1/c=1 collapse = `selberg_nu_separable`,
and the prime-value + linearity lemmas (#59) give the algebraic toolkit for
the s1/s2 expansions.

**The remaining work is the interface decision, not construction.** The
`s1`/`s2` axioms (`s1_holds_from_nonprime_asym`,
`s2_holds_from_prime_asym_under_EH`, and the MPZ/beyond/eps sisters) are
stated as `alphaBound k (selberg_nu k F H b W) ...` / `betaBound k
(selberg_nu k F H b W) ...` — they take the multidimensional `F`, not a
basis. To set `selberg_nu := selberg_nu_basis` you must choose:
- **(A)** Re-type the `s1`/`s2` axioms (and `selberg_sieve_data_*_from_F`
  call sites, ~6) to carry basis data `(J, c, Fs)` alongside/instead of `F`,
  then `selberg_nu` becomes a real `noncomputable def := selberg_nu_basis`.
  Discharges the opaque (0/8 → 1/8). Semantic refactor of the axiom
  signatures — do it deliberately, verify each call site still composes.
  **⚠️ Do NOT shortcut this** by giving `selberg_nu` a concrete body at its
  *current* `(F) → (ℕ → ℝ)` type: a finite separable decomposition does not
  exist for general `F`, so any forced body (e.g. a rank-1 marginal) would
  make the s1/s2 axioms assert asymptotics about a weight they may not hold
  for — a **false axiom**, strictly worse than the honest opaque. The whole
  point of carrying basis data is that the axioms then only ever speak about
  genuinely-`selberg_nu_basis`-built weights.
- **(B)** Keep `selberg_nu` opaque; add a cited axiom that the optimal `F`
  admits a finite `∑_j c_j ∏_i F_{j,i}` representation (Polymath8b
  asymptotics §). Smaller, but does NOT move the depth metric.

**NB:** under either path, `alphaBound`/`betaBound`/`s1`/`s2` themselves
stay axioms (the deep analytic NT). Discharging `selberg_nu` shrinks the
trust base by one opaque and makes those axioms speak about a *concrete*
weight — a prerequisite for ever discharging them — so (A) is foundational,
not cosmetic, but it is a signature refactor.

#### **Structural sorry discharges** (now sorries, not axioms — per PR #41)

All of these were `axiom` until PR #41 reclassified them as
`theorem := sorry`. PR #42 discharged the first two:

| Theorem | Status | Effort |
|---|---|---|
| `Mk_le_one_of_k_le_one` (k = 0 case) | ✅ Done (PR #42 via `Mk_zero_le_one`) | trivial — `mkF_numerator 0 = 0` |
| `Mk_le_one_of_k_le_one` (k = 1 case) | ✅ Done (PR #62) | `MeasurableEquiv.funUnique (Fin 1) ℝ` gives the `simplex 1 ↔ Icc 0 1` measure-iso (via `setIntegral_preimage_emb`); the C-S step is `ConvexOn.map_integral_le` (Jensen for x↦x²) on the probability measure `volume.restrict (Icc 0 1)` — cleaner than the signed-F `Lp_mul_Lq` path. ~1h as estimated. |
| `MkSet_truncated_bddAbove` | ✅ Done (PR #42 via subset) | routes through `MkSet_bddAbove` |
| `MkSet_nonempty` | sorry | medium — smooth-bump construction. Future PR. |
| `MkSet_bddAbove` | sorry | medium — Polymath8b Cor `mk-upper`. Future PR. |
| `MkSet_truncated_nonempty` | sorry | medium — fresh bump inside truncated simplex; CANNOT route through `MkSet_nonempty` because simplex_truncated ⊆ simplex (wrong direction; a witness for MkSet doesn't fit in the truncated polytope) |
| `MkSet_eps_nonempty` | ✅ Done (PR #45 via shared F witness + setIntegral_mono_set) | routes through `MkSet_nonempty` |
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

### Cited axioms in the §3 sieve-core chain (11 total as of PR #50)

| Axiom | Purpose | Added in | Future-PR target |
|---|---|---|---|
| `selberg_nu` (opaque) | Polymath8b §3 `nuform` (3.6)-(3.7) | early | encode as `noncomputable def` |
| `alphaBound` (opaque) | (s1) asymptotic-bound Prop | early | encode as `Asymptotics.IsLittleO` |
| `betaBound` (opaque) | (s2) asymptotic-bound Prop | early | sister of `alphaBound` |
| `wtrick_data` | W-trick (b coprime to W, all b+h_i coprime) | PR #34 | Mertens + CRT |
| `s1_holds_from_nonprime_asym` | (s1) asymptotic from §3 line 889 (i) | PR #34 | divisor-sum expansion |
| `s2_holds_from_prime_asym_under_EH` | (s2) asymptotic from §3 line 862 (i) + EH | PR #34 | divisor-sum + EH |
| `s1_eps_holds_from_nonprime_asym` | (s1) ε-flavored, §5 epsilon-trick reduction | PR #35 | sister of s1 |
| `s2_eps_holds_from_prime_asym_under_EH` | (s2) ε-flavored, §5 epsilon-trick + EH | PR #35 | sister of s2 |
| `s2_holds_from_prime_asym_under_MPZ` | (s2) MPZ-flavored, §5 maynard-trunc | **PR #49** | sister + MPZ window |
| `s1_beyond_holds_from_nonprime_asym` | (s1) beyond-flavored, §5 epsilon-beyond | **PR #50** | sister; enlarged polytope k/(k-1) R_k |
| `s2_beyond_holds_from_prime_asym_under_GEH` | (s2) beyond-flavored, §5 epsilon-beyond + GEH | **PR #50** | sister + GEH + vanishing marginal |

Plus 2 polytope-existence axioms for the truncated variant (`MkSet_truncated_nonempty`,
`MkSet_truncated_bddAbove`); these are structural rather than analytic.

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

## Scorecard against ROADMAP predictions (as of 2026-05-28)

ROADMAP was created 2026-05-26 22:34. ~1.5 days wall time, ~3
session-equivalents shipped (PRs #41-#53). Checkpoint date 2026-06-26
still ~29 days out.

| Tier | Estimate | Confidence | Status |
|---|---|---|---|
| Tier 1 (encode 3 opaques) | 5-8 sessions | 75% | **0/3 discharged**, but the entire `selberg_nu` *construction* is now encoded (`lambdaTransform` #52 + `selberg_nu_separable` #55 + `selberg_nu_basis` #56). Remaining for discharge = `s1`/`s2` interface signature decision, not math. |
| Tier 2 (structural sorry discharges) | 3-8 sessions | 85% | **3-4 of ~7 done** (#42, #45). ~40-50% through. On pace. |
| Tier 3 (`wtrick_data`) | 5-15 sessions | 50% | 0. Expected (Tier 1 first). |
| Tier 4 (first s1/s2) | 10-30 sessions | 40% | 0. Expected. |
| Tier 5 (rest of sieve core) | 20-60 sessions | 30% | 0. Expected. |

**Pace matches the model** (~3-4 PRs / session, ~0.3 sessions per
non-trivial PR). **Depth-into-sieve metric: 0/8 Bucket-D discharges** (but
`lambdaTransform` is the first real sieve-core building block).

**Off-roadmap pattern**: most work has been **top-down** (turn flagship
bodies real, push sorries down into more-targeted cited axioms) rather
than the bottom-up plan the ROADMAP sketched (encode opaques first). The
top-down work made all 4 Polymath8b §5 flagships compose through real
analytic cores (#49, #50) and discharged the §1 asymptotic combinator
(#53). Tier 1's construction is now fully built out (#52, #55, #56).

If the 2026-06-26 checkpoint is to validate Tier 1's estimate, **the next
session should discharge the `selberg_nu` opaque** — the construction
ladder is done, so this is the s1/s2 interface decision (path A re-type vs.
path B cited axiom), which moves depth-into-sieve 0/8 → 1/8. See "Open
work" above.

## Recommended next-session plan

Trevor's guidance: **read papers, decompose knarly bits into smaller pieces,
fine to increase sorry count as long as each piece is easier.** Verify
against the paper at every threshold.

Suggested order:

1. **Warm-up** (~10 min): re-derive sorry count + locations; read
   `ROADMAP.md` to align on Bucket A/B/C/D and tier framework; read the
   scorecard above.
2. **Tier 1 — discharge the `selberg_nu` opaque** (~1-2 sessions). The
   construction ladder is done: `lambdaTransform` (#52), `selberg_nu_separable`
   (#55), `selberg_nu_basis` (#56, the full general nuform). Remaining is the
   **s1/s2 interface decision** (see Open work): (A) re-type the `s1`/`s2`
   axioms + ~6 `selberg_sieve_data_*_from_F` call sites to carry basis data,
   then `selberg_nu := selberg_nu_basis` (discharges opaque, 0/8 → 1/8); or
   (B) a cited F→basis representation axiom (smaller, no metric move). Verify
   each call site still composes after a path-A refactor.
3. **Tier 1 — `alphaBound`/`betaBound`** via `Asymptotics.IsLittleO` once
   `selberg_nu` is real. "Depth into sieve" 0/8 → 3/8.
4. **Small structural discharges** (each ~0.5-1 session):
   - `Mk_le_one_of_k_le_one` k=1 case via L²-Cauchy-Schwarz on $[0,1]$
     (~1h, see the Bucket-B effort table above for the probe findings).
   - `MkSet_nonempty` via ContDiffBump (note the EuclideanSpace ↔ Pi
     instance juggle — likely the main friction).
   - `MkSet_eps_bddAbove`: separate (1+ε)/(1-ε) factor argument.
5. **Tier 3 — `wtrick_data` discharge** (~5-15 sessions) — Mertens
   products + CRT density. The first sieve-core axiom discharge would
   be the first "Lean has touched the sieve" milestone — outside
   audiences would care.

**Done this session (2026-05-28)**: PR-A1b-iii-a/b (#49, #50) made all 4
§5 flagships real; #52 landed `lambdaTransform`; #53 discharged the §1
asymptotic combinator `hm_asymp_from_dhl_and_narrowness`.

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
