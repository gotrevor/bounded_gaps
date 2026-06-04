# HANDOFF — PR #64/#65 (Tier-1 opaque discharge) — IN FLIGHT

Written 2026-05-30 from inside the **lean-yolo-box** (network-isolated; egress
= Anthropic only, no `gh`/`ssh`, so this work could NOT be pushed from the
box). Supersedes nothing — `HANDOFF.md` still describes master at PR #63.

**Four stacked commits on one branch** (`path-a-selberg-nu`), all local-only:
1. `9ca6120` — selberg_nu path-A discharge (this doc's original subject).
2. `48d2288` — alphaBound/betaBound → real `IsLittleO` defs (Tier 1 complete).
3. `4c57f9c` — MkSet_nonempty discharge (Tier 2) + ⊤=ω→∞ smoothness fix
   (see "Third commit" below).
4. `7aa2b9a` — `integral_insertNth_eq` keystone for MkSet_bddAbove (Tier 2,
   partial; MkSet_bddAbove still sorry). See "Fourth commit" below.

Push the branch once; either open one PR for all four, or split by
cherry-picking — your call.

## State

- **Branch**: `path-a-selberg-nu`, **HEAD `7aa2b9a`** (local only, NOT pushed).
- **Build**: green (`lake build`, 8259 jobs). Transient OOMs in the box on
  parallel olean mmap — just retry `lake build`; it succeeds within 1-2 tries.
- **Counts** (after ALL three commits): sorries **15 → 14** (`MkSet_nonempty`
  discharged in `4c57f9c`), axioms **37 → 40** (+3 cited §6, from `9ca6120`),
  **opaques 3 → 0** (`selberg_nu` in `9ca6120`; `alphaBound`/`betaBound` in
  `48d2288`).
- **Depth-into-sieve**: 0/8 → **3/8** (1/8 from selberg_nu, +2/8 from α/β).
  Tier 2 also now in progress (MkSet_nonempty done).

## Second commit (`48d2288`) — alphaBound/betaBound → real defs (Tier 1)

Replaced the last two `opaque` predicates with honest `noncomputable def`s in
the `Asymptotics.IsLittleO` shape (ROADMAP Tier 1). New primitives in
`Sieve.lean`: `sieveSum`, `primeTheta`, `sieveThetaSum`, `sieveB`,
`alphaMainTerm`, `betaMainTerm`. (s1)/(s2) now read as **one-sided** little-o
of the violation's positive part — `(sieveSum − α·M)⁺ =o[atTop] M` and
`(β·M − sieveThetaSum)⁺ =o[atTop] M` — which keeps the `s1_holds_from_*` /
`s2_holds_from_*` axioms honestly TRUE (a bare `≤ α·M` would be the false
load-bearing-leaf trap). Signatures byte-identical to the opaques → zero
call-site churn; `x` is now vestigial (documented). Verified:
`#print axioms dhl_50_2`/`dhl_3_2_under_GEH` route through the SAME cited
axioms; α/β/selberg_nu gone from the axiom lists (real defs); no new debt.

This is the ROADMAP Tier-1 milestone: **the structural skeleton stops being
self-citing** (all three sieve opaques are real).

## Third commit (`4c57f9c`) — MkSet_nonempty (Tier 2) + ⊤=ω→∞ fix

**Latent bug found + fixed.** A bare `ContDiff ℝ ⊤` means `ω` (ANALYTIC) after
mathlib's `WithTop ℕ∞` migration (Lean prints it as `ω`). The Maynard test
functions are smooth bumps, not analytic, so `MkSet` was requiring an analytic
F with `support ⊆ simplex` — which forces F ≡ 0, i.e. `MkSet` was empty,
`Mk = 0`, and `MkSet_nonempty` was **false as literally typed**. Swept all 26
`ContDiff ℝ ⊤` → `ContDiff ℝ ∞` (C^∞) + `open scoped ContDiff`; every site in
the safe direction. Flagship axiom deps verified unchanged by the sweep.

Then **discharged `MkSet_nonempty`** (sorries 15 → 14) with a product-of-1D-
bumps witness `F t = ∏ᵢ b(tᵢ)` (centers/radii chosen so `supp F ⊆ simplex`,
`∫F² > 0` via `IsOpen.measure_pos` + `setIntegral_pos_iff_support_of_nonneg_ae`).
`#print axioms MkSet_nonempty` = `[propext, Classical.choice, Quot.sound]` only
— a complete honest proof, no sorryAx/project axioms. Also adds reusable
`isCompact_simplex` (feeds the integrability + the pending `MkSet_bddAbove`).

## Fourth commit (`7aa2b9a`) — MkSet_bddAbove keystone (Tier 2, partial)

Landed the reusable fibration lemma `integral_insertNth_eq`:
`∫ t, G t = ∫ s, ∫ ti, G (i.insertNth ti s)` for integrable G — sorry-free,
via `volume_preserving_piFinSuccAbove` + `integral_prod_symm`. This is the
keystone for the `M_k ≤ k` crude bound (enough for `BddAbove`).

`MkSet_bddAbove` stays **sorry**. Remaining work (documented in its
docstring), all leaning on `support F ⊆ simplex` to move between simplex and
full-space integrals:
1. integral Cauchy-Schwarz `(∫_{Icc 0 L} g)² ≤ L · ∫_{Icc 0 L} g²` — NOT a
   single mathlib lemma; prove via L² Hölder / `inner_mul_le_norm_mul_norm`.
2. `I(F) = ∫_{ℝ^{n+1}} F²` and `J_i ≤ ∫_{ℝ^n}∫_ℝ F(insertNth)²` via the
   keystone + `setIntegral` support/monotonicity lemmas.
3. `J_i ≤ I`, sum over i, divide ⟹ `M_k ≤ k`.
Genuine multi-session task (ROADMAP est. 2-3 sessions); the hardest reusable
infra piece is now done.

## What this PR did — path A, done honestly

Discharged the `selberg_nu` opaque. It is now a real
`noncomputable def selberg_nu (k J) (c) (Fs) (H) (R) := selberg_nu_basis …`.
The s1/s2 axioms were re-typed to carry basis data `(J, c, Fs, R)` + an
`hFdecomp` hypothesis, so they speak about the concrete `selberg_nu_basis`
weight, not an opaque.

### The soundness catch (why this wasn't a 20-min mechanical refactor)

The first draft (Sonnet) compiled and discharged the opaque, but introduced
`exists_basis_of_sieve_F`: a **sorry** asserting *every smooth F is
finite-separable*. That statement is **FALSE** (e.g. `exp(t₀·t₁)` has infinite
separation rank — the `[exp(xₐyᵦ)]` node matrix is full-rank) and it was
**load-bearing** for every flagship. A false load-bearing leaf is strictly
worse than the honest opaque it replaced (the exact trap `HANDOFF.md` /
`feedback_lean_opaque_vs_axiom.md` warn against; PR #36 reverted this shape).

### The honest replacement (committed)

- **`Sieve.IsFiniteSeparable F`** predicate = `∃ J c Fs R, ∀ t, F t = ∑ⱼ cⱼ ∏ᵢ Fs[j,i](tᵢ)`.
  Genuine restriction, NOT derivable from smoothness.
- **3 cited axioms** in `Sieve.lean` (Polymath8b §6: the variational optimum
  is realised by polynomial = separable test functions):
  `exists_separable_F_of_Mk_gt`, `_truncated_of_Mk_truncated_gt`,
  `_eps_of_Mk_eps_gt`. They feed `maynard_thm` / `maynard_trunc` /
  `epsilon_trick` (replacing the non-separable `exists_F_*` at those call
  sites; the old `exists_F_*` theorems are kept, just no longer called).
- **`epsilon_beyond`** gained an `IsFiniteSeparable F` hypothesis, supplied by
  the already-cited `mk_eps_3/51_witness_under_GEH` axioms (each gained a
  `Sieve.IsFiniteSeparable F` conjunct) in `Polymath8b.lean`.
- **Provable bridge** `SievePolynomial.polynomialSieveWeight_isSeparable`:
  a polynomial weight's monomial expansion IS a finite basis decomposition
  (`Fs[p,i](x) = x^(eₚᵢ)`). Proves the cited axioms are non-vacuous. Proof =
  `Finset.sum_coe_sort` + `Equiv.sum_comp` over `P.terms.equivFin`.

### Verification done

`#print axioms BoundedGaps.Polymath8b.dhl_50_2` (EH path) and
`dhl_3_2_under_GEH` (GEH path) both route through the new cited axioms; NO
`exists_basis_of_sieve_F` anywhere. Remaining `sorryAx` is pre-existing
structural debt (`witness_eventually_from_sieve_data` in `dhl_criterion`,
`MkSet_nonempty`, `narrowness_realized`, `DHL_gives_freq_primeAt_gap`),
unchanged by this PR.

Files: `BoundedGaps/Sieve.lean` (+179/-…), `Polymath8b.lean`,
`SievePolynomial.lean`. 3 files, 153 insertions / 60 deletions.

## NEXT STEPS

### 1. Push + PR (HOST-side — box cannot reach GitHub)
The branch has FOUR stacked commits (`9ca6120` selberg_nu, `48d2288` α/β,
`4c57f9c` MkSet_nonempty + ⊤→∞, `7aa2b9a` bddAbove keystone). Simplest is one
PR for the whole branch:
```bash
cd ~/src/bounded_gaps
git push -u origin path-a-selberg-nu
gh pr create --title "Tier-1: discharge selberg_nu + alphaBound/betaBound opaques" \
  --body-file HANDOFF-PR64.md
gh pr merge --admin --merge      # master protected; bypass 30-min GHA queue
```
After merge: refresh the main `HANDOFF.md` (opaques 3→**0**, axioms 37→40,
depth-into-sieve **0/8 → 3/8**) and trash this file. Also tick the KB todo
"Push + PR the bounded_gaps path-A discharge" (now covers both commits).

### 2. Tier-1 continuation — ✅ DONE in this session (commit `48d2288`)
`alphaBound`/`betaBound` are now real `IsLittleO` defs. Tier 1 complete:
all three sieve opaques discharged, depth-into-sieve at **3/8**. Next depth
work is Tier 2/3/4 (structural sorries, `wtrick_data`, first s1/s2 family
member) — see `ROADMAP.md`.

### 3. Upgrade the 3 cited `exists_separable_F_*` axioms → real (optional, deeper)
Currently cited (Polymath8b §6 + tensor-product density). To make them real
proofs, the lever is the existing **`SievePolynomial.lean`** sorries:
`polynomialMkF_eq_MkF` and `Mk_ge_polynomialMkF`. Discharging those connects
polynomial witnesses to the abstract `Mk` sup; combined with the now-proved
`polynomialSieveWeight_isSeparable`, the separable-extraction axioms could be
*derived* rather than cited (eliminating 3 axioms). Medium effort; needs
`Mk` to have a real `iSup` body first.

## Box gotchas (lean-yolo-box, 2026-05-30 first run)
- `lake build` OOMs intermittently on the box (16-core parallel olean mmap vs
  15Gi RAM). Plain retry works. No `-j`/`--jobs` flag on this lake.
- No `gh`, no `ssh`, remote is `git@github.com:…` → push/PR is host-only.
- Git identity not set in box; set locally: `git config user.email gotrevor@gmail.com`.
