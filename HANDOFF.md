# HANDOFF.md — Bounded Gaps Lean project

Written 2026-05-26 after a ~22-PR push that took sorries 55 → 25.
This document is self-contained: a fresh session can read it and start
working without scrolling the history.

> ⚠️ **Caveat**: some file-line numbers and per-file sorry counts below are
> from memory and may be off by a few. The numbers were accurate as of
> `master` at `474de6e` (merge of PR #22 *Axiomatize 11 §6 mk_*_witness*).
> Always re-derive the authoritative state with the build commands in
> *Build / dev* below before acting.

## TL;DR

- **Sorries: 25.** **Axioms: ~31** (all cited to specific paper sections).
- **Sieve.lean's variational chain is fully concrete**: `simplex`, `simplex_eps`,
  `simplex_shrunk`, `mkF_(eps_)?numerator`, `mkF_(eps_)?denominator`, `MkF`,
  `MkF_eps`, `Mk`, `Mk_eps`. Zero opaques, zero axioms left in this file.
- **`dhl_criterion` has a real proof body** (PR #17) composed of two named
  sub-lemmas. One of those sub-lemmas (`infinite_witnesses_of_eventual_witness`)
  is also fully real (PR #18); the other (`witness_eventually_from_sieve_data`)
  is the §3 Lemma-crit analytic core, still a sorry.
- **`dhl_two_implies_boundedGap` is fully real** (PR #21) plus its extraction
  helper.
- **Three paper-section milestones DAG-closed:**
  - Engelsma.lean (tuple harvest, modulo MIT primegaps + Clark-Jarvis axioms)
  - Polymath8b §7 parity barrier (informal-axiom leaf)
  - Polymath8b §3 narrowness bounds / `hk-bound` (PR #19, closes the
    asymptotic bounds via Hensley-Richards + Brun-Titchmarsh axioms)
- **Zhang's bound is captured as a corollary** (`H1_le_70M_via_Polymath8b`,
  PR #20) — real proof; method-faithful version (`H1_le_70M`) remains sorry.
- **Every Polymath8b §1 H_m flagship is exactly 2 open leaves away** from
  fully DAG-closed (see *Front A* and *Front B* below).

## Operating principles (locked in this session — please keep)

1. **Axioms at leaves with citations.** External evidence (paper-§
   numerical computations, exhaustive enumerations, MIT primegaps
   constructions, Brun-Titchmarsh, etc.) → `axiom <name> : ... ` with a
   precise paper-§ + numerical-value citation in the docstring. Reserve
   `sorry` for *internal Lean work in progress*. See
   `feedback-axioms-at-leaves` in `~/personal/claude/knowledge/` MEMORY.md.

2. **Twig-splitting decomposition.** If a sorry is large/mega, decompose
   into 2-4 named sub-lemmas (each a sorry with paper-§ citation and
   TRIAGE comment), and turn the original theorem into a real proof body
   that composes them. PR #17 (`dhl_criterion` → 2 sub-lemmas) and PR #21
   (`dhl_two_implies_boundedGap` → extraction helper + foldr lemmas) are
   the template. **Increasing the sorry count by 1-3 is fine if each new
   sorry is independently smaller and citable.**

3. **Verify formulas against the paper, not against a handoff.** A
   previous handoff said `J_k(F) := ∑_i ∫ (∫ ∂_i F dt_i)² dt`. Polymath8b
   §5 actually has `∫ F dt_i` (no derivative). PR #15 fixed it. **Always
   pull `papers/src/polymath8b-1407.4897/newergap-submitted.tex` for the
   precise statement.**

4. **Better metrics than raw sorry count:**
   - *PROVABLE-sorries* — strip out cited-axiom candidates.
   - *DAG-closed depth* — for a flagship theorem, what fraction of the
     dependency DAG is real-or-cited-axiom all the way to leaves?
   - *Honest-debt sum* = `sorries + uncited-opaques + uncited-axioms`.
     You can't reduce one by inflating another.

## Build / dev

```bash
cd ~/src/bounded_gaps

# full build, ~50s warm:
lake build

# incremental:
lake build BoundedGaps.Sieve  # etc.

# authoritative sorry count (build warnings):
lake build 2>&1 | grep -c "declaration uses .sorry."

# axiom inventory (cited leaves):
grep -rn "^axiom\b" BoundedGaps/*.lean

# by-file sorry locations:
lake build 2>&1 | grep "declaration uses .sorry." | awk '{print $2}' | sort

# branch + ship workflow (master is protected, GHA queues 30+ min):
git checkout master && git pull
git checkout -b <feature-name>
# ... edits ...
git add <files> && git commit -m "..."
git push -u origin <feature-name>
gh pr create --title "..." --body "..."
gh pr merge --admin --merge       # fast merge, bypasses GHA queue
```

**Pre-commit hook blocks commits to master.** Feature branches only.

**`cd` doesn't persist across Bash calls** in the Claude harness — `cd ~/src/bounded_gaps && ...` per call.

## Current state of play

### What's DAG-closed (real proofs all the way to cited-axiom leaves)

- **Engelsma.lean** — entire tuple harvest. `tuple_5511_admissible` is now
  an axiom citing MIT primegaps; everything else is real (`native_decide`
  on `length`/`diameter`/`sorted` works through k = 54, axiomatized at
  k = 5511).
- **Polymath8b §7 — parity barrier** — `parity_barrier` is an axiom over
  the informal `SieveTheoreticArgument` predicate. The section has
  exactly one declaration; it's the only honest treatment for an
  informal heuristic claim.
- **Polymath8b §3 narrowness bounds / Theorem `hk-bound`** (this is the
  big milestone from PR #19) — all 14 declarations are real proofs or
  cited axioms. Independent of §3 DHL / §5 variational chain. Leaves:
  Clark-Jarvis 2001 (axioms for $k = 50, 51, 54$ lower bounds),
  Polymath8b §6 + MIT primegaps (axioms for $k = 5511$ admissibility
  and $k \ge 35410$ upper bounds), Hensley-Richards 1973 (asymptotic
  upper, PR #19), classical Brun-Titchmarsh (asymptotic lower, PR #19).
- **Sieve.lean variational scaffolding** — all of `simplex`, `simplex_eps`,
  `simplex_shrunk`, `mkF_(eps_)?numerator`, `mkF_(eps_)?denominator`,
  `MkF`, `MkF_eps`, `Mk`, `Mk_eps` are concrete `noncomputable def`s
  built from `setIntegral` / `intervalIntegral` / `fderiv` / `sSup`.
  No opaques, no axioms remain in this file.
- **`dhl_criterion`** — real proof body composing the two §3 Lemma-crit
  sub-lemmas. Hypothesis was strengthened (PR #17) from a trivially-
  satisfiable form to the paper-faithful `∀ᶠ x in atTop, alphaBound …`
  shape.

### Two open fronts

Every Polymath8b §1 H_m flagship is **exactly 2 open leaves away** from
DAG-closed. The two leaves split into two independent fronts:

#### Front A: §5 → §3 bridges (`Sieve.lean`)

The four theorems that turn an `Mk(_eps)` numerical witness into a
`DHL[k, m+1]` conclusion (under EH / MPZ / GEH):

| Theorem | Hypothesis (key) | Used by |
|---|---|---|
| `maynard_thm`   | `Mk k > 4*m/ϑ`, EH       | `H1_le_12_under_EH` etc. |
| `maynard_trunc` | `Mk k > 4*m/(1/2+2ϖ)`, MPZ | `H2-H5` (the m ≥ 2 chain) |
| `epsilon_trick` | `Mk_eps k ε > 4*m`       | `H1_le_246` |
| `epsilon_beyond`| `Mk_eps k ε > 2*m/ϑ`, GEH | `H1_le_6_under_GEH` |

Each one's proof structure in Polymath8b §5 (Section labelled
`variational-sec` in the TeX): take the witnessing $F$, construct a
Selberg sieve weight $\nu$ from $F$, verify (s1) and (s2) via §3's
`prime-asym` / `nonprime-asym` asymptotics, invoke `dhl_criterion`
(already real). The bulk of the work is the Selberg construction and
the (s1)/(s2) verification — these consume BV/MPZ/EH/GEH respectively.

**Suggested decomposition** (recommended next-session pattern):

```
selberg_sieve_data_from_F   -- the hard one
    F : simplex-supported smooth, MkF(F) > threshold
    →  ∃ ν α β b W, (s1)(s2)(key) hold

maynard_thm                  -- 3-line composition
    invoke selberg_sieve_data_from_F + dhl_criterion
```

Further breakdown of `selberg_sieve_data_from_F`:
- `ν_def_from_F` (definition of ν per Polymath8b eqn `nuform`)
- `s1_holds_from_prime_asym` (consumes Polymath8b §3 Theorem
  `prime-asym` — which itself is currently absent from the project;
  this would be a major new sub-leaf to introduce)
- `s2_holds_from_nonprime_asym` (same flavor)
- `key_from_MkF` (the structural connection from `MkF k F` to `∑β/α`)

Note: `prime-asym` and `nonprime-asym` (Polymath8b §3 Theorems with
those labels in the TeX) are deep analytic theorems requiring BV /
MPZ infrastructure. They could be axiomatized at first (with citations
to Polymath8b §3 and §4) and discharged later.

**Paper pointers** (TeX file: `papers/src/polymath8b-1407.4897/newergap-submitted.tex`):
- `\label{maynard-thm}` ~line 920
- `\label{maynard-trunc}` ~line 959
- `\label{epsilon-trick}` ~line 997 (decoded for PR #16 already)
- `\label{epsilon-beyond}` ~line 1020
- `\label{prime-asym}` ~line 862
- `\label{nonprime-asym}` ~line 889

#### Front B: `Filter.liminf` bridges (`Basic.lean` + `TwinPrimes.lean`)

Three sorries of the same flavor — the bridge from the project's
set-infinite encoding (`BoundedGap`, `Set.Infinite` of prime witnesses)
to `Filter.liminf`-based `liminfGap m` and to the literature
`TwinPrimesConjecture`.

| Theorem | Statement | Status |
|---|---|---|
| `liminfGap_one_le_iff` | `liminfGap 1 ≤ H ↔ BoundedGap H` | sorry (Basic.lean) |
| `dhl_implies_liminfGap` | `DHL k (m+1) → liminfGap m ≤ narrowness k` | sorry (Basic.lean), depends on the previous |
| `twinPrimes_iff_liminfGap_one` | `TwinPrimesConjecture ↔ liminfGap 1 ≤ 2` | sorry (TwinPrimes.lean) |

All three need real `Filter.liminf` + `Nat.nth Nat.Prime` machinery —
TRIAGE'd as **HARD WORLD** in the threads doc. Estimated ~1-3h each;
the three share enough machinery that bundling them is likely the
right call.

Key defs to grok before attacking:
- `Basic.primeAt n := Nat.nth Nat.Prime (n - 1)` (the n-th prime,
  off-by-one for n = 0)
- `Basic.liminfGap m := liminf (fun n => (primeAt (n + m) - primeAt n : ℕ∞)) atTop`

**Suggested decomposition** of `liminfGap_one_le_iff` (untested
sketch):

```
primeAt_strictMono       : StrictMono primeAt  -- via Nat.nth + Pairwise
gap_pos_of_distinct      : 0 < primeAt (n+1) - primeAt n
bounded_gap_iff_freq     : BoundedGap H ↔ ∃ᶠ n in atTop, primeAt (n+1) - primeAt n ≤ H
liminf_le_iff_freq       : (liminf f atTop ≤ c : ℕ∞) ↔ ∃ᶠ n in atTop, f n ≤ c
liminfGap_one_le_iff     : 3-line composition
```

The 4th lemma is a generic mathlib-style fact about `Filter.liminf` in
`ℕ∞`; may already exist in mathlib under a slightly different name —
worth grep-hunting before reinventing.

### Smaller open items (1-2 sorries each)

- **`Polymath8b.hm_asymp_from_dhl_and_narrowness`** (1 sorry, ~50 lines
  of Filter/asymptotics plumbing — BLUEPRINT_LEAF, "bookkeeping
  combinator"). Composes an asymptotic DHL claim + the asymptotic
  narrowness bound (now a cited axiom) → an asymptotic $H_m$ bound.
- **`Polymath8b.dhl_asymptotic_unconditional`** + **`dhl_asymptotic_under_EH`**
  (2 sorries) — the asymptotic version of `dhl_50_2` etc. Depend on
  Front A (§5 bridges) plus k-tuple asymptotic admissibility (already
  axiomatized).
- **`Polymath8b.twin_primes_or_near_miss_Goldbach`** (§8, 1 sorry) —
  BLUEPRINT, multi-week. Depends on full Maynard/`epsilon_beyond` chain
  + Goldbach-pair density. Don't touch until Front A is done.
- **`Zhang.H1_le_70M`** (1 sorry, method-faithful Zhang). The result is
  captured by `H1_le_70M_via_Polymath8b` (real proof, PR #20). Leave
  the method-faithful version as a tracked sorry for whoever wants to
  walk Zhang's actual GPY+MPZ argument.
- **`Targets.H1_le_of_Mk_witness`** (1 sorry — uncertain exact shape;
  scout `BoundedGaps/Targets.lean:50`).
- **`Maynard.H1_le_600`** and similar (5 sorries in `Maynard.lean` —
  uncertain on details). Likely consumers of the Sieve chain like
  `H1_le_600`, `H1_le_12_under_EH`. Largely subsumed by Polymath8b §1
  flagships; consider whether they're worth keeping.
- **`SievePolynomial.lean`** (4 sorries — uncertain). Includes
  `polynomialMaynardNumerator`, `polynomialMaynardDenominator`,
  `Mk_gt_four_of_polynomial_witness` and similar. Now that `MkF` is
  concrete, some of these should be re-examinable.
- **`Prerequisites.lean`** (2 sorries — `geh_implies_eh` and
  `eh_implies_mpz`, both trivial reductions). Could be discharged
  cheaply when someone has 15 minutes.
- **`TwinPrimes.lean`** (1 sorry) — see Front B above.
- **`Sieve.lean:108` (`witness_eventually_from_sieve_data`)** — Front A
  consumes this once §5 bridges are decomposed.

### Mathlib lemmas / patterns that came up

Things this session used that future work will likely also use:

- `Set.infinite_of_forall_exists_gt : (∀ a, ∃ b ∈ s, a < b) → s.Infinite`
- `Set.infinite_of_not_bddAbove : ¬BddAbove s → s.Infinite`
- `Set.Infinite.exists_gt : s.Infinite → ∀ a, ∃ b ∈ s, a < b`
- `Filter.eventually_atTop : (∀ᶠ x in atTop, P x) ↔ ∃ N, ∀ n ≥ N, P n`
- `List.countP_eq_length_filter`
- `List.Pairwise.sublist` + `List.filter_sublist` for sortedness
  inheritance through filter
- `List.pairwise_cons`, `List.mem_filter`, `List.mem_cons_self`,
  `List.mem_cons_of_mem`
- `Fin.insertNth : Fin (n+1) → α → (Fin n → α) → (Fin (n+1) → α)` —
  pattern-match on `k = n + 1` to use it cleanly
- `fderiv ℝ F t (Pi.single i 1)` — partial derivative ∂_i F at t
- `ContDiff ℝ (⊤ : WithTop ℕ∞) F` — F is smooth ($C^\infty$)
- `Function.support F ⊆ S` — F-vanishes-outside-S, useful for the
  admissible-F set in `sSup`-style defs

### Gotchas from this session

- **The handoff bug** (PR #15): the previous session's handoff stated
  `J_k(F) := ∑_i ∫ (∫ ∂_i F dt_i)² dt`. The paper actually has `∫ F dt_i`
  — no derivative. Always cross-check against the TeX before encoding
  a formula.
- **`dhl_criterion`'s original hypothesis was too weak** (PR #17). The
  docstring promised `alphaBound`/`betaBound`; the type signature
  didn't include them, making the theorem trivially-satisfiable yet
  false. Always check that the *type signature* and the *docstring*
  agree.
- **`match`-as-tactic scoping pitfall**: when binding `h₁`, `h₂`, `rest`
  via `match hF : list, hLen with | h₁ :: h₂ :: rest, _ => ...` inside
  an `obtain`, the inner-binder names collide with the outer
  existential's named binders. The clean pattern (PR #21 helper) is to
  write the `match` directly inside the outer `by`-block, not inside
  an `obtain` block.
- **`List.mem_cons_self`, `List.filter_sublist`** in v4.29.1 are
  zero-arg (all implicit). Don't pass explicit args.

## Recommended next-session plan

Trevor's guidance: **read papers, decompose knarly bits into smaller
pieces, fine to increase sorry count as long as each piece is easier.**

Suggested order:

1. **Wrap warm-up** (~30 min): read this file, run the build commands,
   reproduce the sorry inventory, and scout the files this handoff
   marks "uncertain" (`Maynard.lean`, `SievePolynomial.lean`,
   `Targets.lean`, `TwinPrimes.lean`, `Prerequisites.lean`).
2. **Decompose `Sieve.maynard_thm`** (~1-2h): read Polymath8b §5
   Theorem `maynard-thm` proof. Twig-split into `selberg_sieve_data_from_F`
   + a 3-line composition. Likely surfaces `prime-asym` / `nonprime-asym`
   as new axioms (Polymath8b §3 deep theorems). Net: +3 to +6 sorries,
   but each is focused, citable, attackable. This unblocks `H1_le_12_under_EH`.
3. **Then `Sieve.epsilon_trick`** (similar pattern, ~1-2h). This
   unblocks `H1_le_246` (modulo Front B).
4. **OR — Front B `liminfGap_one_le_iff`** (~1-3h, HARD WORLD). Bundle
   with `twinPrimes_iff_liminfGap_one`. If you go this route, the
   reward is unblocking Front B for *every* flagship at once.

Either path lands real DAG-closed depth for the §1 results. Both are
substantive work. Front A is closer to "pattern from this session"
(decompose, cite paper, build); Front B is closer to "novel Lean
infrastructure" (Filter.liminf, Nat.nth Nat.Prime).

## Pointers outside the repo

- Knowledge base: `~/personal/claude/knowledge/core/projects/lean-journey/side-quests/`
  - `bounded-gaps.md` — project shape / overall arc
  - `bounded-gaps-threads.md` — thread tracker (updated through PR #17;
    PR #18-#22 not yet integrated into the Done table)
  - `sieve-mkf-handoff.md` — prior session's handoff, now marked
    COMPLETED at the top
- Memory: `~/personal/claude/memory/` (auto-loaded each session)
  - `feedback_axioms_at_leaves.md` — the operating principle codified
    this session
  - `reference_lean_tactics_gotchas.md` — Lean v4.29.1 / mathlib
    landmines accumulated across sessions
- Papers: `papers/src/polymath8b-1407.4897/newergap-submitted.tex` is
  the canonical Polymath8b source. `papers/pdf/` has rendered PDFs of
  most relevant references (Zhang 2014, Maynard 2015, Polymath8a, etc).

---

🪷 Last commit on `master` when this file was written: `474de6e`
(merge of PR #22 *Axiomatize 11 §6 mk_*_witness*).
