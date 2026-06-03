# ANALYTIC_AXIOM_BURNDOWN.md — burning down the *cited* analytic-NT axioms

Written 2026-06-03 (branch `path-a-selberg-nu`). Companion to `ROADMAP.md`
and `PENDING_WORK.md`, but with a deliberately different stance.

## The reframe (why this doc exists)

`ROADMAP.md` says, correctly for its purpose:

> Axiom-by-citation is the contract, not the debt. Citing Bombieri-Vinogradov
> ... is normal mathematical practice. These stay axioms by design.

That is the right metric for measuring *depth into the sieve* (the §3
Polymath8b content). But it brackets off the deepest cited theorems as
permanently-out-of-scope, and that bracket is a **hypothesis, not a fact**
(cf. the project value "needs-deep-machinery is an untested hypothesis").

The long-term ambition recorded here: **research the literature and actually
prove the cited analytic-NT axioms in Lean**, so that the headline
`bounded_gap_of_Mk_200` (currently unconditional *modulo* Bombieri-Vinogradov
+ sieve estimates) eventually rests on `[propext, Classical.choice,
Quot.sound]` and nothing else — bounded gaps between primes, machine-checked
from the ground up.

This doc maps the terrain: what mathlib already gives us, which axioms are
genuinely tractable, and which single piece is the multi-month nut worth
cracking.

## Verified mathlib v4.29.1 inventory (grepped in-box, 2026-06-03)

Checked against `.lake/packages/mathlib` directly, not from memory:

| Ingredient | Present? | Notes |
|---|---|---|
| Dirichlet characters, L-functions, analytic continuation, functional-equation framework, non-vanishing on Re(s)=1, Dirichlet's theorem (qualitative primes in AP) | ✅ | rich `Mathlib/NumberTheory/LSeries/` tree |
| Selberg sieve | ⚠️ partial | `Mathlib/NumberTheory/SelbergSieve.lean` — the **abstract Λ² upper-bound framework** (`siftedSum_le_mainSum_errSum_of_upperMoebius`), NOT the multidimensional GPY/Maynard evaluation |
| **Prime Number Theorem** (π(x) ~ x/log x) | ❌ | `PrimeCounting.lean` has only the combinatorial Brun-style bound `primeCounting'_add_le`. The PrimeNumberTheoremAnd project is **not merged**. |
| **Large sieve inequality** | ❌ | (`SiegelsLemma.lean` is Siegel's *lemma*, unrelated) |
| **Siegel-Walfisz theorem** | ❌ | |
| **Vaughan / Heath-Brown identity** | ❌ | |
| **Bombieri-Vinogradov** | ❌ | |

## Axiom census — 38 axioms, classified by burn-down character

(`grep -rc '^axiom ' BoundedGaps/`: Prerequisites 4, Sieve 10, Polymath8b 23,
SymmetricReductionOrbitFree 1. Re-derive before acting; counts drift.)

### Family A — deep analytic NT (the real literature targets)

`Prerequisites.lean`:
- `BombieriVinogradov {ϑ} (0<ϑ<1/2) : EH ϑ` — **the crown jewel.** `EH` now
  carries a *real quantitative body* (`∑ maxDisc(Λ) ≤ C·x/(log x)^A`), so this
  is a fully-stated theorem, not a `Prop` stub.
- `GeneralizedBombieriVinogradov : GEH ϑ` — Motohashi's version (over Dirichlet
  convolutions α⋆β). Strictly harder than BV. NB: `GEH` itself is still an
  opaque `axiom GEH : Prop` (no real body yet), so GBV can't be attacked until
  `GEH` is given a faithful definition.
- `MPZ_polymath8a : MPZ ϖ δ` — Zhang's smooth-moduli estimate (level past 1/2).
  The docstring calls it "the most analytically demanding input we use"
  (Kloosterman sums, Deligne/Weil bounds, type I/II/III sums). **Do not chase
  this** — arguably harder than BV itself.

### Family B — sieve + combinatorial (tractable, "elementary")

`Sieve.lean` (10): the GPY/Maynard sieve-sum evaluations.
- `s1_*_holds_from_nonprime_asym` — main-term (nonprime) asymptotics,
  **unconditional**.
- `s2_*_holds_from_prime_asym_under_{EH,MPZ,GEH}` — prime-sum asymptotics.
  **This is where EH/GEH/MPZ (hence BV) actually gets consumed by the sieve.**
  Even fully proven, the `_under_EH` ones stay conditional on Family A.
- `exists_separable_F_*` — the variational claim that a near-optimal weight
  admits a finite separable representation F = ∑ⱼ cⱼ ∏ᵢ Fⱼᵢ. (Also the gate on
  discharging the `selberg_nu` opaque — see its docstring + ROADMAP Tier 1.)

`SymmetricReductionOrbitFree.lean` / `SievePolynomial.lean`:
- `num_bridge` (visible axiom) and `denom_bridge` (in `Mk_200_gt_4`'s
  `#print axioms` base) — the orbit permanent/rook identities. Pure
  combinatorics, **no analytic NT**. Both base cases proven by hand
  (`*_bridge_nil`); inductive step **in flight with Aristotle**.

### Family C — numerical witness data (discharge by computation)

`Polymath8b.lean` (23): `mk_*_witness` (Mₖ(F) > threshold) and `narrowness_*`
(admissible-tuple diameters), plus two `mk_witness_asymptotic*`. These are
not "literature" axioms — they're certificates that yield to the
`native_decide` route already proven viable by `Mk_200_gt_4` (see
`MkWitness200.lean` + `PENDING_WORK.md §A`). The named flagships (k=50, 54) are
degree-bound-infeasible on-box; larger-k/lower-degree witnesses are the path.

## The Bombieri-Vinogradov dependency tree

```
BombieriVinogradov  (EH ϑ for ϑ < 1/2)
├── Large sieve inequality          ← self-contained · MULTI-MONTH NUT ⭐
├── Vaughan / Heath-Brown identity  ← combinatorial · weeks
└── Siegel-Walfisz (small moduli)   ← the tar pit:
    └── PNT in arithmetic progressions   ← NOT in mathlib
        ├── Prime Number Theorem          ← NOT in mathlib (PNT+ unmerged)
        ├── L-function zero-free regions   (LSeries infra exists, regions don't)
        └── Siegel's theorem (ineffective Siegel zeros)  ← notoriously subtle
```

Standard textbook decomposition (Davenport; Iwaniec-Kowalski). There are
variant proofs, but every unconditional BV proof handles the small-modulus
range via Siegel-Walfisz, and that branch intrinsically drags in the
ineffective Siegel-zero estimate and the PNT. **That is what makes full BV a
multi-year, multi-component campaign, not a multi-month nut** — and it is gated
on PNT not even being in mathlib yet.

## The multi-month nut: the Large Sieve Inequality ⭐

The largest self-contained piece that is genuinely a multi-month effort *and*
actually finishable. It is the right target because:

- **Deep, named, famous** — a cornerstone of analytic number theory.
- **Self-contained**: provable from the duality principle + a
  Montgomery-Vaughan / Selberg argument on exponential sums (or the analytic
  large sieve via Gallagher). It does **not** depend on PNT or the Siegel-zero
  tar pit.
- **On the BV critical path** — it is the "large modulus" half of every BV
  proof.
- **Standalone mathlib value** — a clean PR regardless of whether full BV ever
  lands, and a prerequisite for a lot more than bounded gaps.

## Recommended ordering (leverage, not glamour)

1. **Finish `num_bridge`/`denom_bridge`** (in flight). Kills the only non-std
   axioms on the just-landed `Mk_200_gt_4` chain. Family B, free.
2. **The s1/s2 sieve asymptotics** (`Sieve.lean`). "Elementary" (sieve-sum
   manipulation conditional on EH), and mathlib's `SelbergSieve` gives the
   scaffold. Weeks-to-a-couple-months. **Highest leverage** — this is the real
   "depth into the sieve" and was previously, wrongly, waved off as out of
   scope. *Caveat: estimate is untested; read the axiom bodies + the
   EH-conditional argument and try-to-fail before committing to "weeks."*
3. **The Large Sieve Inequality.** The multi-month nut. Standalone mathlib
   contribution + the biggest down payment on BV.
4. **(Someday) PNT → Siegel-Walfisz → assemble BV.** The multi-year prize.
   Payoff: `bounded_gap_of_Mk_200` becomes fully unconditional, zero
   analytic-NT axioms.

Note the routing fact from Family B: discharging the `s2_*_under_EH` axioms to
*real proofs* still leaves them conditional on `BombieriVinogradov`. So the
sieve burn-down (step 2) and the BV burn-down (steps 3-4) are independent
contributions that only combine into "unconditional, axiom-free" once both are
done.

## Confidence + caveats

- mathlib inventory above: **high confidence** (grepped the actual checkout).
- "Large sieve is the right multi-month nut": **~80%**.
- BV dependency structure (needs Siegel-Walfisz → PNT → Siegel zeros):
  **~85%** on the structure; variant proofs exist but none escapes the
  small-modulus / Siegel-zero branch.
- Step-2 "weeks-to-a-couple-months": **low confidence until tried.** Per the
  project's own rule, treat as a hypothesis to refute, not a plan.

## Provenance

Built 2026-06-03 from: `grep` of axiom declarations across `BoundedGaps/`,
direct inspection of `.lake/packages/mathlib` v4.29.1, and the EH/GEH/BV/MPZ
docstrings in `Prerequisites.lean`. Conversation context: Trevor's directive to
stop treating cited axioms as permanently out of scope and instead map a
literature-burn-down path.
