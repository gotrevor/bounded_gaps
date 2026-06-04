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
2. **The s1/s2 sieve asymptotics** (`Sieve.lean`). The real "depth into the
   sieve." **Estimate corrected from "weeks" to multi-month** by the
   try-to-fail below — these are the full GPY/Maynard multidimensional sieve
   asymptotic, and the analytic core (a Mertens/singular-series summation) is
   unsupported by mathlib. See "Try-to-fail result" below for the
   sub-decomposition and the revised target.
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

## Try-to-fail result (2026-06-03): the s1/s2 "weeks" estimate was wrong

Per the project rule, the step-2 estimate was tested by reading the actual
axiom bodies before committing to it. Result: **it does not survive.** What the
`s1/s2` axioms actually assert (verified, not assumed):

- The weight is the genuine GPY/Maynard squared Möbius-divisor sum:
  `selberg_nu(n) = (∑_j c_j ∏_i λ_{F_{j,i}}(R, n+h_i))²`, with
  `λ_g(R,n) = ∑_{d|n} μ(d) · g(log d / log R)` (a real `noncomputable def` over
  `Nat.divisors` and mathlib's `ArithmeticFunction.moebius`).
- `alphaBound`/`betaBound` are **real** `Asymptotics.IsLittleO` statements (not
  opaque, not trivially-true) of the sieve-sum excess against real main terms
  `B^{-k}·x/W` and `B^{1-k}·x/φ(W)`, with `sieveSum = ∑_{x≤n≤2x, n≡b(W)} ν(n)`
  and the prime-weighted `sieveThetaSum` using `primeTheta(m) = log m · [m prime]`.

So discharging `s1/s2` means **proving the GPY/Maynard sieve asymptotic** — not
shoving work sideways. It decomposes into four sub-steps:

| Sub-step | Content | Estimate | mathlib? |
|---|---|---|---|
| (a) square + expand + swap | `sieveSum(ν) = ∑_{d,e} (μμ coeffs)·#{n∈[x,2x]: n≡b(W), [dᵢ,eᵢ]∣(n+hᵢ)}` | **weeks** | ✅ `divisors`, `moebius`, `Finset.sum_comm` |
| (b) inner lattice count | `#{n} = (x/W)·(density) + O(err)` via CRT (W ⟂ moduli by W-trick + squarefree) | **weeks-month** | ⚠️ elementary, build it |
| (c) singular-series / Mertens summation → integral | `∑_{d,e} (coeffs)·density → I(F)·B^{-k}` (resp. `Jᵢ(F)·B^{1-k}`); the `λ_d ↔ F(log d/log R)` Riemann-sum needs Mertens asymptotics (`∑_{d≤R} μ²(d)/φ(d) ~ log R`, multidim) | **MULTI-MONTH** ⭐ | ❌ no Mertens, no summatory-Λ asymptotic |
| (d) error bound | s1: unconditional (moduli `≤ R² = x^θ < x^{1/2}`, paper says "Trivial"); s2: **this is where EH/BV is consumed** | s1 small / s2 nontrivial | gated on EH |

**Net correction.** The sieve side has its own multi-month nut, mirroring the
Large Sieve on the BV side: **sub-step (c), the Mertens/singular-series-to-integral
asymptotic.** It is arguably the *better first multi-month target* than the
Large Sieve, because:

- The **s1** half (sub-step (c) for `alphaBound`) is **unconditional** — no EH,
  so independently meaningful progress.
- Its prerequisite — **Mertens' theorems** (`∑ 1/p`, `∏(1-1/p)`, `∑ μ²/φ`) — is
  a clean, famous, self-contained mathlib contribution in its own right.
- Sub-steps (a)+(b) are genuine weeks-scale warm-ups that, even alone, reduce
  `s1/s2` to a *sharper, smaller* singular-series axiom (the "isolate the real
  nut" move ROADMAP values).

**Revised ordering of the multi-month targets:** do **Mertens' theorems →
s1 (unconditional) sieve asymptotic** *before* the Large Sieve. Same depth of
nut, but EH-free payoff and a cleaner mathlib-shaped prerequisite.

## Sub-step (a) DONE, (b) advancing (2026-06-04, `BoundedGaps/SieveExpansion.lean`)

The `s1` decomposition is being executed. New file `SieveExpansion.lean`, all
theorems `#print axioms = [propext, Classical.choice, Quot.sound]`:

- **Sub-step (a) — DONE.** `sieveSum_selberg_nu_separable_expand` is the full
  algebraic opening (Polymath8b §3 eqn (sfg-1)): for `0 < x`,
  `sieveSum ν_sep b W x = ∑_{P∈∏ᵢ(sieveDivisors)²} (∏ᵢ μ(dᵢ)Fᵢ μ(eᵢ)Fᵢ) ·
  #{m∈block : ∀i, dᵢ∣(m+hᵢ) ∧ eᵢ∣(m+hᵢ)}` with `P i = (dᵢ,eᵢ)`. Supporting
  bricks: `divisor_pair_expand` (single-coord), `prod_sum_active_expand` (the
  **`Fintype`-indexed swap workhorse**, the real engine), `selberg_nu_separable_
  expand_pointwise`, `lambdaTransform_pair_block`. Key mathlib unlocks:
  `Finset.prod_univ_sum` (product-of-sums → piFinset sum), `Fintype.prod_ite_zero`
  (collapse the indicator product to a single `∀`-condition), `Finset.filter_product`.
- **Sub-step (b) — partly built, partly on mathlib, partly Aristotle.**
  - `lattice_count_lcm`: collapses each coordinate's `dᵢ∣ ∧ eᵢ∣` to the single
    GPY modulus `[dᵢ,eᵢ] = lcm(dᵢ,eᵢ)`.
  - `crt_combine`: for coprime `W,Q`, the joint `m≡b(W) ∧ Q∣(m+h)` is one class
    mod `W·Q` (via `Nat.chineseRemainder` + `Nat.modEq_and_modEq_iff_modEq_mul`).
  - **mathlib HAS the interval AP-count** (`Nat.Ioc_filter_modEq_card` /
    `Nat.Ico_filter_modEq_card`, `Mathlib/Data/Int/CardIntervalMod.lean`): the
    count of an AP mod `M` in an interval is `⌊·⌋−⌊·⌋`, exact. So the
    single-modulus count + O(1) error is mathlib-immediate. The **end-to-end**
    bound `|#{m∈Icc A B : m≡b(W) ∧ Q∣(m+h)} − (B+1−A)/(WQ)| ≤ 1` is on Aristotle
    (`6515817c`, `aristotle-crtcount/`).
  - **Remaining (b) content** = the *multi-coordinate* CRT: combine `m≡b(W)` with
    `∀i, qᵢ∣(m+hᵢ)` (`qᵢ=[dᵢ,eᵢ]`) into one modulus. Clean only on the **coprime
    diagonal** (`W, q₁,…,q_k` pairwise coprime — squarefree + W-trick); the
    off-diagonal (`gcd(qᵢ,qⱼ)>1`) is the genuine error term and the bridge to (c).
    Next: iterated CRT over `Fin k` under pairwise coprimality (mathlib
    `ZMod.chineseRemainder` / iterate `crt_combine`).
- **Sub-step (c)** — its 1-D core `∑μ²/φ = Θ(log N)` is **already done &
  unconditional** (`BoundedGaps.Mertens.mertens_theta_log`, commit `e8b00d7`).
  The remaining (c) content is the *weighted* convergence
  `∑_{d≤R} (μ²(d)/φ(d))·F(log d/log R) ~ (∫₀¹F)·log R` (Abel summation against
  the Mertens asymptotic) and its multidimensional/singular-series lift.

- **s2 (the prime/EH half) — algebraic opening ALSO DONE (2026-06-04).** The
  same chain mirrored for the prime-weighted sum `sieveThetaSum`:
  `prod_sum_active_expand_weighted` (the **weighted** swap workhorse — lattice
  count → weighted sum `∑_{m∈block,lattice} wt m`), `sieveThetaSum_lambdaProd_
  expand` (two-family, theta-weighted), and `sieveThetaSum_selberg_nu_expand`
  (general weight) — so `sieveThetaSum(selberg_nu) = ∑ⱼⱼ' cⱼcⱼ' ∑_P (∏ μF μF)·
  (∑_{m∈block,lattice} primeTheta(m+h_{i₀}))`, the exact object
  `s2_holds_from_prime_asym_under_{EH,MPZ}` must estimate. Same `lattice_count_*`
  / CRT reduction applies to the prime-weighted count; the difference is sub-step
  (d): s2's prime-in-AP count is where **EH/BV is consumed** (s1's is unconditional).

**Net (2026-06-04):** the **algebraic skeleton of BOTH `s1` and `s2`** is
formalized for the genuine multidimensional `selberg_nu` weight (sub-step (a) /
eqns (sfg-1),(theta-oo)), and sub-step (b)'s lattice count is reduced — on the
coprime diagonal — to a single mathlib-computable AP count. (c)'s 1-D keystone
(`∑μ²/φ=Θ(log N)`) is in hand. **Remaining nuts**, in rough order:
1. **Off-diagonal error** (`gcd(qᵢ,qⱼ)>1`): bound the non-coprime lattice terms
   (squarefree support + the W-trick make the diagonal dominate). Elementary but
   real; the bridge into (c).
2. **Sub-step (c) weighted Mertens**: `∑_{d≤R} (μ²(d)/φ(d))·F(log d/log R) ~
   (∫₀¹F)·log R` (Abel summation vs the Mertens asymptotic), then its
   multidim/singular-series lift to `α=I(F)` / `βᵢ=Jᵢ(F)`.
3. **(d) error / `IsLittleO` assembly**: package the main term + error into the
   `alphaBound`/`betaBound` `IsLittleO` shape; s1 unconditional, s2 needs EH/BV.
All in `BoundedGaps/SieveExpansion.lean`; everything axiom-clean.

## Next-level probe (2026-06-03): the 1D Mertens lemma is a weeks-scale on-ramp

Took the test one level deeper — actually attempted the entry lemma in Lean
(`scratch_mertens.lean`, repo root, **typechecks**). Statement attempted:
`log N ≤ ∑_{n≤N} μ²(n)/φ(n)`. What it revealed:

- **Both endpoints are already in mathlib.** `log_le_harmonic_floor`
  (`Real.log y ≤ harmonic ⌊y⌋₊`) gives `log N ≤ harmonic N` in ~2 lines
  (compiles, no sorry). `tsum_geometric_of_lt_one` covers `1/(p-1) = ∑_j p^{-j}`.
- **The whole lemma reduces to ONE real sub-lemma**, `mertens_crux`:
  `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)` (true in aggregate; fails termwise at
  non-squarefree `n`, e.g. `n=4`). Its proof is the radical-fiber /
  Euler-product rearrangement `∑_{q≤N} g(q) = ∑_{rad(m)≤N} 1/m ≥ ∑_{m≤N} 1/m`.
  (The other `sorry`, `harmonic_eq_icc_sum`, is pure range↔Icc plumbing.)
- **mathlib gap**: no `radical : ℕ → ℕ`, no `∑∏ = ∏∑` Euler expansion of a
  multiplicative function over `primeFactors`. So `mertens_crux` must be built —
  but it is ONE bounded, well-posed lemma, not a campaign.

**Refined estimate.** The *1D Mertens lower bound* is a **weeks-scale on-ramp**,
not multi-month: two endpoints free, one rearrangement lemma to build. The
multi-month label belongs to the *full sub-step (c)* — the **two-sided,
multidimensional** asymptotic with the singular series and the
divisor-sum→∫F² Riemann-sum convergence — for which 1D Mertens is the first
brick. The on-ramp is concrete and EH-free: a first target you can start now.

**Aristotle bet**: `mertens_crux` submitted as job
`6c45fd6b-3757-4a2c-87ba-059478d10cff` (2026-06-03). A sorry-free return shrinks
the on-ramp from "weeks" to "verify + port"; grinding out corroborates the weeks
estimate. Poll `aristotle list`; verify in-kernel + `#print axioms` before
trusting (Aristotle pins v4.28; this repo is v4.29.1).

**✅ DONE 2026-06-04 (commit on `path-a-selberg-nu`).** Aristotle `6c45fd6b`
returned a **sorry-free** `mertens_crux` (radical-fiber partition, NOT the naive
termwise bound). Ported + re-verified in v4.29.1 — one `grind` regression in
`radical_factor_split` (the `radical(p^k)=p` step) replaced by an explicit
`radical_pow`/`radical_of_prime` derivation; the plumbing lemma
`harmonic_eq_icc_sum` discharged by induction. The whole **`mertens_lower :
log N ≤ ∑_{n≤N} μ²(n)/φ(n)` now lives in `BoundedGaps/Mertens.lean`** (in the
fleet build, `#print axioms = [propext, Classical.choice, Quot.sound]` — kernel
clean, no `native_decide`). **Correction to the inventory table above**: mathlib
v4.29.1 *does* have `radical` (`UniqueFactorizationMonoid.radical`,
`Mathlib/RingTheory/Radical/Basic.lean`) with `radical_dvd_self`, `radical_pow`,
`radical_of_prime`, `radical_mul`, `squarefree_radical` — the "no `radical`"
claim was wrong; that is what made the 1D bound a days-task, not weeks.

**✅ DONE 2026-06-04 (lap ~19:40Z, commits `a2e4c60`…`422a1f8` on `path-a-selberg-nu`).**
The 1D *upper* ladder advanced several rungs, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `native_decide`):
- `mertensSummand_eq_prod` + `mertens_prod_upper`: `∑_{n≤N} μ²/φ ≤ ∏_{p≤N}(1+1/(p-1))`
  (Euler-product domination of squarefree `n`; `n ↦ primeFactors n` injects squarefree
  `n≤N` into the powerset of primes `≤N`). Proved LOCALLY in v4.29.1.
- `chebyshev_theta_le`: `θ(N)=∑_{p≤N} log p ≤ N·log 4` (from mathlib `primorial_le_four_pow`).
- `abel_div_le` (Aristotle `32baa99f`, summation-by-parts, verified kernel-clean) +
  `mertens_first_le`: **Mertens' first theorem** `∑_{p≤N}(log p)/p ≤ log 4·(1+log N)`.
- Plumbing bricks: `chebyshev_theta_le'`, `mertens_first_le'` (partial-sum/indicator forms),
  `telescope_tail_*`/`prime_tail_le` (`∑_{p≤N}(1/(p-1)−1/p) ≤ 1`).

**Next nut — Mertens' second theorem** `∑_{p≤N} 1/p ≤ log log N + O(1)`. Decomposition:
a *second* Abel step from `mertens_first_le'`, with weight `w_p = 1/log p` (NOT the
`1/n` weight of `abel_div_le`). Needs (i) the **general Abel identity**
`∑ a_n w_n = A_N w_N − ∑ A_n (w_{n+1}−w_n)` — **submitted to Aristotle `431512dd`**
(`aristotle-abelid/AbelId.lean`); and (ii) the analytic estimate
`∑_{2≤n≤N} 1/(n·log n) = O(log log N)` (integral comparison `∫ dt/(t log t)=log log t`;
the genuine remaining analytic content — likely its own brick, may need
`AntitoneOn.sum_le_integral`-style mathlib tooling). With Mertens 2nd:
`∑_{p≤N} log(1+1/(p-1)) ≤ ∑ 1/(p-1) ≤ ∑ 1/p + 1 = log log N + O(1)` ⇒
`∏_{p≤N}(1+1/(p-1)) = O(log N)` ⇒ **`∑μ²/φ = O(log N)`**, pairing with `mertens_lower`
for the two-sided `Θ(log N)`. Then the sharp `= log N + O(1)` (Mertens constant), then
the **multidimensional** singular-series → ∫F² version (the multi-month sub-step (c) nut).

Artifact: `scratch_mertens.lean` — the original standalone probe (two sorries);
superseded by the landed `BoundedGaps/Mertens.lean`. The download/verify scratch
lives in `aristotle-mertens-dl/` and `scratch_mertens_verify.lean` (untracked).

## Confidence + caveats

- mathlib inventory above: **high confidence** (grepped the actual checkout).
- "Large sieve is *a* right multi-month nut": **~80%**.
- BV dependency structure (needs Siegel-Walfisz → PNT → Siegel zeros):
  **~85%** on the structure; variant proofs exist but none escapes the
  small-modulus / Siegel-zero branch.
- Step-2 "weeks": **refuted** (try-to-fail above). s1/s2 is multi-month,
  dominated by the Mertens/singular-series asymptotic.
- GPY decomposition (a)-(d) above: **~80%** on structure; **~75%** that
  sub-step (c) is genuinely multi-month.
- 1D Mertens lower bound is a weeks-scale on-ramp (endpoints free, one crux
  lemma): **~85%** (verified the endpoint compiles + the gap is one lemma).
  Whether `mertens_crux` itself is days or weeks is the open question Aristotle
  job `6c45fd6b` is now testing.

## Provenance

Built 2026-06-03 from: `grep` of axiom declarations across `BoundedGaps/`,
direct inspection of `.lake/packages/mathlib` v4.29.1, and the EH/GEH/BV/MPZ
docstrings in `Prerequisites.lean`. Conversation context: Trevor's directive to
stop treating cited axioms as permanently out of scope and instead map a
literature-burn-down path.
