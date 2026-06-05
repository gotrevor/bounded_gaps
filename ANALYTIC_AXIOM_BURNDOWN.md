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

> **⚠️ Verified per-theorem 2026-06-04 (`#print axioms`).** "How many axioms"
> is *per-theorem*, not a repo-wide count. The flagship `H1_le_246` rests on
> exactly **4 math axioms**: `BombieriVinogradov`, `s1_holds_from_nonprime_asym`,
> `s2_eps_holds_from_prime_asym_at_level`, `mk_eps_50_witness` — plus the trust
> base (`propext, Classical.choice, Quot.sound` + 18 `native_decide` reductions
> from the Engelsma 50-tuple; trust base, **not** debt — never count these as
> "axioms left", see `feedback_axiom_discharge_doctrine`). Zero `sorry`.
>
> **`GeneralizedBombieriVinogradov` and `MPZ_polymath8a` are DEAD axioms** — in
> *no* headline theorem's base. Each is reachable only through a demo wrapper
> (`GEH_one_third`, `MPZ_small`) that nothing downstream consumes. The MPZ/GEH
> dependence of `H2_le_398130`…`H5_*` and the GEH chain is *bundled inside* the
> `mk_*_witness*` axioms (`∃ ϖ δ, … ∧ MPZ ϖ δ ∧ …`) and the `s2_*_under_MPZ` /
> `s2_beyond_*_under_GEH` sieve axioms — not routed through the standalone ones.
> So the "38" census **overcounts** the live dependency surface.

### Family A — deep analytic NT (the real literature targets)

`Prerequisites.lean`:
- `BombieriVinogradov {ϑ} (0<ϑ<1/2) : EH ϑ` — **the crown jewel.** `EH` now
  carries a *real quantitative body* (`∑ maxDisc(Λ) ≤ C·x/(log x)^A`), so this
  is a fully-stated theorem, not a `Prop` stub.
- `GeneralizedBombieriVinogradov : GEH ϑ` — Motohashi's version (over Dirichlet
  convolutions α⋆β). Strictly harder than BV. **DEAD axiom** (see verified note
  above: only the unused `GEH_one_third` wrapper reaches it). NB: `GEH` itself is
  still an opaque `axiom GEH : Prop` (no real body yet), so GBV can't be attacked
  until `GEH` is given a faithful definition like `EH`/`MPZ` have — *and* a live
  consumer would first have to route through it instead of the bundled witnesses.
- `MPZ_polymath8a : MPZ ϖ δ` — Zhang's smooth-moduli estimate (level past 1/2).
  The docstring calls it "the most analytically demanding input we use"
  (Kloosterman sums, Deligne/Weil bounds, type I/II/III sums). **Do not chase
  this** — arguably harder than BV itself. **DEAD axiom** (only the unused
  `MPZ_small` wrapper reaches it; H₂–H₅ get MPZ bundled inside `mk_*_witness`).

### Family B — sieve + combinatorial (tractable, "elementary")

`Sieve.lean` (10): the GPY/Maynard sieve-sum evaluations.
- `s1_*_holds_from_nonprime_asym` — main-term (nonprime) asymptotics,
  **unconditional**.
- `s2_*_holds_from_prime_asym_at_level` (EH-level; **renamed 2026-06-04** from
  `_under_EH`) and `s2_*_under_{MPZ,GEH}` — prime-sum asymptotics.
  **This is where the level-of-distribution input gets consumed by the sieve.**
  The `_at_level` ones take `EH ϑ` at a *generic* ϑ, so for ϑ<1/2 they are
  unconditional via BV — only ϑ≥1/2 callers invoke the EH conjecture. (The old
  `_under_EH` name made the unconditional `H1_le_246` look EH-conditional.)
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

## Sub-step (b) toolkit COMPLETE + singular-series corner (2026-06-04 late)

Second continuation lap. 12 commits, all axiom-clean, full build green (8274 jobs).
**Sub-step (b) now has a complete reusable toolkit** in `SieveExpansion.lean`:
- diagonal main term (`lattice_count_main_term`, `ap_interval_count_bound`) — DONE;
- off-diagonal vanishing: `lattice_count_offdiag_vanish` (a value `p` dividing two
  moduli with `hᵢ ≢ hⱼ [MOD p]` ⟹ count 0), `…_of_lt` (W-trick size form),
  `…_Wtrick` (the **real discharge**: moduli coprime to `W=∏_{p≤D₀}p`, shifts `≤ D₀`
  distinct ⟹ non-coprime moduli give count 0), `lattice_count_pair_offdiag_vanish`
  (the exact expansion form `dᵢ∣∧eᵢ∣`), `sieveTheta_pair_offdiag_vanish` (s2 sister);
- assembly: `sum_restrict_offdiag_vanish` (off-diagonal terms drop, sum restricts to
  the coprime diagonal — general over the diagonal predicate).
So sub-step (b) is reduced to: instantiate the diagonal-restriction at the actual
`sieveSum_selberg_nu_separable_expand` output, discharge `hvanish` via `…_Wtrick`
with the real `W`/`D₀`/admissible-shift data, and apply `lattice_count_main_term`
per surviving (coprime) tuple. That final glue is the next assembly step (needs the
GPY parameter plumbing: `W`, `D₀ ≥ H`, squarefree moduli coprime to `W`).

**Singular-series corner** (`SingularSeries.lean`, new module) — a complete
classical strand: keystone `n/φ(n)=∑_{d∣n}μ²(d)/φ(d)`, `dirichlet_hyperbola`,
`sum_self_div_totient_eq_weighted`, `sum_self_div_totient_main_split`
(`|∑n/φ − N·T(N)| ≤ ∑μ²/φ`), `singularSum_tendsto_of_bounded` (monotone+bounded ⟹
converges), and the capstone `sum_self_div_totient_asymptotic` (**`∑_{n≤N} n/φ(n) ∼ A·N`**,
`A=ζ(2)ζ(3)/ζ(6)`), conditional only on the singular-sum bound `≤3` (Aristotle
`36bb3493`, in flight). NB this corner is *adjacent* infrastructure: GPY's s1/s2 need
`∑μ²/φ` (the sharp Mertens, literature-gated), not `∑n/φ(n)`; but the machinery
(multiplicative `IsMultiplicative.eq_iff_eq_on_prime_powers`, hyperbola, Abel/`o(N)`
error control) is exactly what sub-step (c) reuses.

## Sub-step (b) diagonal CLOSED + singular-series corner opened (2026-06-04 PM)

Continuation lap. All axiom-clean (`[propext, Classical.choice, Quot.sound]`),
full build green (8274 jobs).

- **Sub-step (b) diagonal — DONE (with O(1) error).** Added to
  `SieveExpansion.lean`:
  - `ap_interval_count_bound`: single-AP interval count `|#{m∈(A,B]: m≡v[M]} −
    (B−A)/M| ≤ 1`, from mathlib `Nat.Ioc_filter_modEq_card` (exact `⌊⌋−⌊⌋`) + a
    floor sandwich. Independently cross-checked by Aristotle `6515817c`
    (`crt_interval_count_bound`, the `Icc`/CRT combined form — verified
    kernel-clean, kept as the alt witness).
  - `lattice_count_main_term`: the capstone. Composes `lattice_count_eq_modEq`
    (multi-coord sieve condition → one residue class) with the AP bound:
    `|#{m∈(A,B]: m≡b[W] ∧ ∀i qᵢ∣(m+hᵢ)} − (B−A)/(W·∏q)| ≤ 1` on the coprime
    diagonal. **This is the GPY diagonal lattice count = main term + O(1).**

- **Singular-series corner — NEW module `BoundedGaps/SingularSeries.lean`.**
  - `self_div_totient_eq_sum_moebiusSq_div_totient`: the keystone identity
    `n/φ(n) = ∑_{d∣n} μ²(d)/φ(d)`, proved as the Dirichlet convolution
    `ζ ⋆ (μ²/φ) = id/φ` of two real arithmetic functions, checked on prime powers
    via `IsMultiplicative.eq_iff_eq_on_prime_powers`. (KB gotcha logged: `ζ` needs
    `open scoped ArithmeticFunction.zeta` or it auto-binds as a free variable and
    the coercion `↑zeta` silently diverges.)
  - `dirichlet_hyperbola`: general `∑_{n≤N}∑_{d∣n} g d = ∑_{d≤N} g d·⌊N/d⌋`
    (Aristotle `627d10e3`, verified kernel-clean).
  - `sum_self_div_totient_eq_weighted`: compose the two →
    `∑_{n≤N} n/φ(n) = ∑_{d≤N} (μ²(d)/φ(d))·⌊N/d⌋`.

- **Remaining-nuts update.** Nut #1 (off-diagonal) and #3 (`IsLittleO` assembly)
  unchanged. Nut #2 (sub-step (c) weighted Mertens) has a **sharpened
  understanding of the real blocker**: the GPY constant `α=I(F)` needs `∑μ²/φ ∼
  log x` with **leading coefficient exactly 1**, but `mertens_theta_log` gives only
  the *lossy* `∑μ²/φ ≤ K·log N` (`K≈e^γ` from the `∏(1+1/(p-1))` route). So
  sub-step (c) is gated on the **sharp** `∑_{n≤x} μ²(n)/φ(n) = log x + O(1)`, whose
  exact elementary identity is non-obvious (the `n/φ(n)` hyperbola route gives the
  *different* sum `∑μ²/(φd)`, and the Mobius-inverse route diverges). Requested the
  textbook proof in `ON-LINE-REQUEST.md` (2026-06-04). In-flight Aristotle
  `36bb3493`: the bounded singular sum `∑_{d≤N} μ²(d)/(φ(d)d) ≤ 3` (the main-term
  coefficient is bounded), a brick for the `∑ n/φ(n) ∼ A·N` average.

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

## Sub-step (c) 1-D keystone DONE — sharp Mertens FULLY UNCONDITIONAL (2026-06-04 PM)

`BoundedGaps.SharpMertens.sharp_mertens_unconditional : (∑_{n≤N} μ²/φ)/log N → 1` is now
proved **axiom-clean** (`[propext, Classical.choice, Quot.sound]`), **no Aristotle dependency**.
Both Euler-product partial-sum bounds are proved DIRECTLY on `bAF`:
- `sum_norm_bAF_le : ∑_{e≤N}|bAF e| ≤ exp 2` — KEY TRICK: `bAF e ≠ 0` ⟹ all prime exponents ≤2,
  so any `e≤N` in the support **divides the primorial squared `(N#)²`**; then the bound is the
  DIVISOR-sum Euler product `(ζ⋆|bAF|)((N#)²) = ∏_{p≤N}(1+2/(p(p-1))) ≤ exp 2` (mathlib HAS
  `multiplicative_factorization`/`coe_zeta_mul_apply`/`map_prod`; it only LACKS the *partial-sum*
  Euler product, which the primorial² trick sidesteps).
- `sum_norm_bAF_log_le : ∑_{e≤N}|bAF e|·log e ≤ 4·exp2·∑'4n^{-3/2}` — (A) `log d ≤ 2∑_{p|d}log p`
  (`d|(N#)² ⟹ d|rad(d)²`); (B) swap order (indicator + `Finset.sum_comm`); (C)
  `sum_gabs_divisors_multiples_le` bounds the multiples-of-`p` divisor sum by `(2/(p(p-1)))·exp2`;
  (D) the convergent prime sum `∑_p (log p)/(p(p-1)) < ∞` (`sum_log_div_primes_le`, via
  `Real.log_le_rpow_div` + `summable_one_div_nat_rpow`).

This corrects the prior framing ("multi-month nut", "2 Aristotle leaves"): the 1-D sharp Mertens
was a days-task once the primorial² / divisor-sum-Euler-product route was found. Reusable bricks
left behind in `SharpMertens.lean`: `gabs` (`|bAF|` as a multiplicative ArithmeticFunction),
`gabs_sum_divisors_mul`, `sum_gabs_divisors_primorial_sq_le`, `prod_primes_factorization_le_one`,
`primorial_sq_primeFactors`, `term_log_div_le` + `summable_four_div_rpow`.

**NEXT (the genuine remaining sub-step (c) nut): the WEIGHTED version** `∑_{d≤R}(μ²/φ)·F(log d/log R)
∼ (∫₀¹F)·log R`, via Abel summation (`Mertens.abel_summation_identity`) against
`sharp_mertens_unconditional`. Its analytic heart — the Riemann-sum convergence for the `1/n`
log-weight `(∑_{n≤R}(1/n)F(log n/log R))/log R → ∫₀¹F` — is on Aristotle (`930e468a`,
`aristotle-wmertens/`). Then the multidimensional/singular-series lift to `α=I(F)`, then sub-step
(d) IsLittleO assembly into `alphaBound`/`s1_holds_from_nonprime_asym`.

## Front #4 (weighted Mertens) REDUCED TO ONE AXIOM (2026-06-04 PM)

The 1-D **weighted Mertens** `∑_{1≤n≤N}(μ²/φ)·F(log n/log N)/log N → ∫₀¹F` (GPY/Maynard sub-step
(c), the keystone after sharp Mertens) is now **fully reduced** in `BoundedGaps/WeightedMertens.lean`
to a **single disclosed analytic axiom** `riemann_sum_log_weight` (the pure Riemann-sum model limit
`(∑_{2≤n≤N}F(log n/log N)/n)/log N → ∫₀¹F`, on Aristotle `930e468a`). The whole arithmetic content
is **axiom-clean & machine-checked**:
- `weighted_mertens` / `weighted_mertens_of_contDiff` (capstone; C¹ form for the smooth sieve cutoff)
  → axioms `[propext, Classical.choice, Quot.sound, riemann_sum_log_weight]`.
- `weighted_mertens_of_riemann` (the axiom-free reduction): `g·F = (1/n)·F + (g−1/n)·F`; model part
  is the Riemann axiom (+ bounded `F0/logN→0`), discrepancy part `→0` by Abel summation.
- `discrepancy_weighted_tendsto_zero` ← `abel_summation_identity` ⇒ `Bdisc N·F(1) − Abel-tail`;
  `discrepancy_div_log_tendsto_zero` (`Bdisc=∑μ²/φ−harmonic=o(log)`, sharp Mertens + harmonic∼log)
  + `abel_tail_tendsto_zero` (Lipschitz squeeze vs the weighted-Cesàro majorant average).
- Reusable analytic bricks: `weighted_cesaro_tendsto_zero`, `weighted_avg_majorant_tendsto_zero`,
  `sum_log_mul_log_diff_le_sq` (telescoping `(log N)²` majorant), `harmonic_div_log_tendsto_one`.

**Correction to the prior "sub-step (c) is multi-month" framing:** the 1-D keystone was days-scale
once the integral Abel summation (`Mathlib.NumberTheory.AbelSummation`) + weighted-Cesàro pattern
were used. The genuine multi-month nut is the **multidimensional / singular-series lift**
(k-dim weighted Mertens → `α = I(F) = ∫_{R_k} F²`), then sub-step (d) IsLittleO assembly into
`alphaBound`/`s1_holds_from_nonprime_asym`. Next-lap targets: (a) port/verify the Riemann axiom
when `930e468a` returns (→ front #4 fully axiom-free); (b) state the k-dimensional weighted Mertens.

### UPDATE (2026-06-04, later): front #4 FULLY AXIOM-CLEAN — axiom DISCHARGED
Aristotle `930e468a` proved `riemann_sum_log_weight`; verified `#print axioms` clean in our
v4.29.1 kernel and ported to `BoundedGaps/RiemannSumLogWeight.lean`. `weighted_mertens` /
`weighted_mertens_of_contDiff` now `#print axioms` = `[propext, Classical.choice, Quot.sound]` —
NO cited axioms. The 1-D weighted Mertens keystone is a complete machine-checked theorem.
Next Aristotle job IN FLIGHT: `3e2b6a8d` (`aristotle-wmertens2d/`) = the 2-D simplex-coupled
weighted Riemann model `∑_{mn≤R} F·G/(mn)/(log R)² → ∫₀¹F(x)∫₀^{1-x}G` (the analytic core of the
k-dim lift). When it returns: verify + port, then build the arithmetic (coprimality + singular
series) layer on top toward `s1_holds_from_nonprime_asym`.

## Sub-step (c) DIAGONALIZATION landed — GPY quadratic form bricks (2026-06-04, continuation)

Continuation lap. 3 commits, all axiom-clean (`[propext, Classical.choice, Quot.sound]`), full
build green (8277 jobs). All in `BoundedGaps/SieveExpansion.lean`. These open sub-step (c) on the
**algebra side** — turning the divisor-lattice quadratic form (the diagonal main term of sub-step
(b)) into the diagonal sum whose Mertens/Riemann asymptotic gives `α = I(F)`.

- **`gpy_diagonalize`** — the GPY 1-D diagonalization identity:
  `∑_{d,e∈T} w(d)w(e)/[d,e] = ∑_{r∈R} φ(r)·(∑_{d∈T, r∣d} w(d)/d)²`
  for any finset `R ⊇` all divisors of all `d∈T`. Proof: `1/[d,e]=gcd(d,e)/(de)`
  (`Nat.gcd_mul_lcm`) + `gcd(d,e)=∑_{r∣gcd}φ(r)` (`Nat.sum_totient`) + reindex `r` outermost
  (`Finset.sum_comm`) + factor the `if r∣d∧r∣e` into a product of per-variable indicators.
- **`gpy_diagonalize_moebius`** — the sieve specialization `w(d)=μ(d)·g(d)` (the `lambdaTransform`
  summand): `∑μ(d)μ(e)g(d)g(e)/[d,e] = ∑_r φ(r)(∑_{r∣d}μ(d)g(d)/d)²`. This is *exactly* the
  per-coordinate quadratic form appearing in `sieveSum_selberg_nu_separable_expand`'s diagonal main
  term once `lattice_count_main_term` substitutes the count `(B−A)/(W·∏[dᵢ,eᵢ])` (the `g(d) =
  F(log d/log R)` instance), so the bricks are on the critical path, not orphaned.
- **`gpy_yvar_substitution`** — the GPY change of variable `d=r·s` exposing the multiplicative
  structure of `y_r := ∑_{d∈T,r∣d} μ(d)g(d)/d`:
  `y_r = (μ(r)/r)·∑_{s,(r,s)=1} μ(s)g(r·s)/s`, via `μ(rs)=μ(r)μ(s)·[gcd=1]` (Möbius vanishes off
  squarefree). The diagonal sum is thus `∑_r φ(r)·(μ(r)/r)²·(coprime sum)²`.
- **`gpy_quadform_nonneg`** — `0 ≤ ∑_{d,e}w(d)w(e)/[d,e]` for any `w` (the form is PSD), immediate
  from the diagonalization (sum of `φ(r)·square ≥ 0`). The matrix-positivity `(1/[d,e]) ⪰ 0`
  underlying every Selberg majorant.

**Remaining (c) content** (the genuine analytic nut, still open): evaluate the diagonal sum
`∑_r φ(r)·(μ(r)/r)²·(∑_{(r,s)=1}μ(s)F(log rs/logR)/s)²` asymptotically as `R→∞`. With `g(d)=
F(log d/log R)` this is the GPY/Selberg main-term computation → the integral constant. The
multidimensional (simplex-coupled) version of the underlying smooth Riemann limit is the in-flight
Aristotle job `3e2b6a8d` (`weighted_riemann_2d`). After that: the off-diagonal-main-term
discrepancy (the heuristic count vs the genuine count — where the singular series lives) and the
sub-step (d) `IsLittleO` assembly into `alphaBound`.

### UPDATE (same continuation lap): sub-step (c) ALGEBRA LADDER COMPLETE + (s1) reduction
8 axiom-clean commits total this lap; full build green (8277). Added beyond the 4 bricks above:
- **`gpy_diagonalize_moebius_squarefree`** + **`gpy_yvar_eq_zero_of_not_squarefree`** — the diagonal
  sum is supported on squarefree `r` (`y_r = 0` off the squarefree locus, since every multiple of a
  non-squarefree `r` is non-squarefree ⟹ `μ=0`).
- **`gpy_diagonal_asymptotic_form`** — the CANONICAL capstone:
  `∑_{d,e}μμgg/[d,e] = ∑_{r∈R sf} (φ(r)/r²)·(∑_{(r,s)=1}μ(s)g(rs)/s)²` (combines the squarefree
  restriction + `y_r` substitution + `μ(r)²=1`). The exact object the `R→∞` asymptotic consumes.
- **`piFinset_lattice_main_factor`** + **`heuristic_main_term_diagonalized`** — the heuristic main
  term (count → `M/∏ᵢ[dᵢ,eᵢ]`) factors over coordinates into `M·∏ᵢ(diagonalized 1-D form)`.
- **`sieveSum_separable_eq_heuristic_add_correction`** — the (s1) REDUCTION:
  `sieveSum = heuristic_main + ∑_P coeffₚ(countₚ − M/∏ᵢ[Pᵢ])`, isolating the exact remaining
  analytic obligation (the correction must be `o(main)`).

**Net:** the ENTIRE algebraic content of sub-step (c) (and the (a)→(c) bridge) is machine-checked.
What remains for `s1_holds_from_nonprime_asym` is purely analytic:
1. **Diagonal-sum asymptotic** — `∑_{r sf}(φ(r)/r²)z_r² → (integral const)` as `R→∞`, with
   `z_r=∑μ(s)F(log rs/logR)/s`; its multidimensional smooth core is Aristotle `3e2b6a8d`
   (`weighted_riemann_2d`, in flight).
2. **Correction bound** — `∑_P coeffₚ(countₚ − M/∏[Pᵢ]) = o(main)`: needs the W-trick discharge
   (`lattice_count_offdiag_vanish_Wtrick`: off-diagonal count = 0) + the diagonal `O(1)` error
   (`lattice_count_main_term`) summed against `∑|coeff|`, with `M=(B−A)/W`. This is where the GPY
   parameter plumbing (`W=∏_{p≤D₀}p`, admissible shifts `≤D₀`, squarefree moduli) enters.
3. **Sub-step (d) `IsLittleO` glue** into `alphaBound`.

## Sub-step (c) CROSS-TERM ladder + Cauchy–Schwarz COLLAPSE (2026-06-04, lap N+1)

Continuation. 8 axiom-clean commits (`af0a3e6`…`e8dd497`), full build green (8277 jobs), every new
decl `#print axioms = [propext, Classical.choice, Quot.sound]`. All in `SieveExpansion.lean`. This
lap completed the **general (non-separable, `J`-basis) cross-term** algebra — the prior lap only
covered the single-function `j = j'` diagonal — and, most importantly, proved a **Cauchy–Schwarz
collapse** that reduces the whole main-term asymptotic to the *diagonal* block alone.

**Cross-term diagonalization (the missing `j ≠ j'` piece):**
- `gpy_diagonalize_bilinear` — polarized `gpy_diagonalize` for two weights:
  `∑ w₁(d)w₂(e)/[d,e] = ∑_r φ(r)(∑_{r∣d}w₁/d)(∑_{r∣e}w₂/e)`.
- `gpy_diagonalize_moebius_bilinear`, `gpy_diagonalize_moebius_bilinear_squarefree`,
  `gpy_diagonal_asymptotic_form_bilinear` — the μ-weighted, squarefree-restricted, and canonical
  (coprime-`z`) bilinear forms. The `g₁ = g₂` cases recover the prior diagonal lemmas.
- `sieveDivisors_pos`, `sieveDivisors_dvd_closed` — the concrete sieve lattice is positive +
  divisor-closed (supplies the `1 ≤ d` / `Rset = sieveDivisors` hypotheses).
- `heuristic_main_term_diagonalized_bilinear[_canonical]`, `heuristic_main_selberg_nu_diagonalized`,
  **`heuristic_main_selberg_nu_canonical`** — the FULL `selberg_nu` heuristic main term, at the
  concrete lattice, in canonical form:
  `∑_{j,j'} cⱼcⱼ'·M·∏ᵢ ∑_{r sf}(φ(r)/r²) z₁ᵢᵣ z₂ᵢᵣ`. The entire algebraic reduction of the
  (non-separable, general) GPY main term to its asymptotic-ready form is now machine-checked.

**Correction size reduction (analytic obligation #2):**
- `piFinset_sum_abs_prod_factor`, `correction_weight_factor`, `sum_prod_abs_mul_factor`,
  `correction_weight_factor_split` — the total correction weight `∑_P|coeffₚ|` factors into
  `∏ᵢ (∑_{d∈Dᵢ}|μ(d)Fⱼᵢ|)·(∑_{e∈Dᵢ}|μ(e)Fⱼ'ᵢ|)`, a product of `2k` single-variable Möbius sums.
  ⚠️ This per-`(j,j')`-block factorization is a valid identity but a **loose** bound: the simplex
  support lives on the *joint* `F = ∑ⱼcⱼ∏ᵢFⱼᵢ`, not the individual `Fⱼᵢ`, so the naive product is
  too weak for `k ≥ 2` (the handoff's known warning). Records why the naive path fails.

**★ THE COLLAPSE — `gpy_bilinear_cauchy_schwarz`:** `B(g₁,g₂)² ≤ B(g₁,g₁)·B(g₂,g₂)` for the cross
Selberg form `B(g₁,g₂) = ∑ μ(d)g₁(d)μ(e)g₂(e)/[d,e]`. Proof: diagonalize all three to the
`φ`-weighted inner product `∑_r φ(r)y₁ᵣy₂ᵣ`, then discrete Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`, `f=√φ·y₁`). **Consequence — the main-term obligation is now ONE
scalar limit, not `J²`:** every cross block `B(Fⱼᵢ,Fⱼ'ᵢ)` is bounded by `√(B(Fⱼᵢ,Fⱼᵢ)·B(Fⱼ'ᵢ,Fⱼ'ᵢ))`,
so once the *diagonal* asymptotic `B(Fⱼᵢ,Fⱼᵢ) ~ cⱼᵢ·(main)` is known (sub-step (c)), the cross terms
are automatically controlled and the `IsLittleO` glue needs only the diagonal limit.

**Diagonal `O(1)` error is wired:** `lattice_count_main_term` gives exactly `|count − M/∏[Pᵢ]| ≤ 1`
(with `M=(B−A)/W`, `∏[Pᵢ]=∏ lcm`) on the coprime diagonal — precisely the hypothesis
`diag_error_bound` needs. So the diagonal half of the correction is reduced to the (factored)
`∑_{diag}|coeff|` size bound.

### Net state after this lap — `s1_holds_from_nonprime_asym` reduces to:
1. **Diagonal asymptotic ONLY** (Cauchy–Schwarz killed the cross terms): the single scalar limit
   `B(F,F) = ∑_{r sf}(φ(r)/r²) z_r² → I(F)`-const as `R→∞`. THE genuine GPY nut; smooth core =
   Aristotle `3e2b6a8d` (`weighted_riemann_2d`, still in flight, slow ~22%).
2. **Off-diagonal heuristic main = o(main)** (singular-series discrepancy): `∑_{¬diag}coeffₚ·main_P`,
   restricted to tuples where two coordinates share a prime — needs the W-trick gain.
3. **`∑_{diag}|coeff| = o(main)`** size bound (the simplex-coupled version; the factored 1-D form is
   the substrate but the joint-support coupling must be used).
4. **Sub-step (d) `IsLittleO` glue** into `alphaBound` — now only needs the diagonal limit + (2),(3).

### Obligation #2 (`∑_{diag}|coeff| = o(main)`) — reduction chain (same lap)
Three further axiom-clean bricks reduce the diagonal size bound to ONE divisor count:
- `selberg_nu_basis_diagonal_reassemble` — the `j,j'`-sum of the diagonal coeff collapses to
  `(∏ᵢμ(dᵢ)²)·F(log d/log R)²` (joint `F`, simplex-supported). Resolves the looseness of the
  per-block factorization.
- `support_simplex_prod_le` — `support F ⊆ simplex ∧ F(log d/log R) ≠ 0 ⟹ ∏ᵢdᵢ ≤ R` (the
  hyperbolic constraint confining contributing tuples).
- `support_simplex_bounded` — continuous simplex-supported `F` is globally bounded (`∃C≥0, |F|≤C`),
  via the compact box `[0,1]^k ⊇ simplex`. Supplies `‖F‖∞`.

**Net:** diagonal weight `≤ C²·#{squarefree d-tuples : ∏ᵢdᵢ ≤ R}`. So obligation #2 = the `k`-dim
Dirichlet divisor count `Dₖ(R) = #{d : ∏dᵢ ≤ R} ≍ R(log R)^{k-1}` being `o(main = M·(log R)^k)`,
which holds since `R = x^{θ/2} ≪ x ≈ M·W`. The repo already has the 1-D interchange
`SingularSeries.dirichlet_hyperbola` (`∑_{n≤N}∑_{d∣n}g = ∑_{d≤N}g·⌊N/d⌋`); the `k`-dim count is
its iterate — a good next Aristotle target. **This nearly closes #2 modulo that one count bound.**

## Leaf (2) DISCHARGED in-kernel + Leaf (4) glue COMPLETE (2026-06-04, lap N+2)

Three axiom-clean commits (`691a239`, `3a3dbef`, `e7dc3ae`), full build green (8277), every
new decl `#print axioms = [propext, Classical.choice, Quot.sound]`.

**★ Leaf (2) — the k-dim Dirichlet hyperbola count — is now PROVEN IN-KERNEL** (was queued for
Aristotle; done locally instead, no Aristotle needed). New in `SieveExpansion.lean`:
- `hyperbola_count_le (k) (hk:1≤k) (N) (hN:1≤N) : #{d∈[1,N]^k : ∏dᵢ≤N} ≤ N·(1+log N)^{k-1}`.
  Proof: induction on `k`; partition `(k+1)`-tuples by first coordinate `m∈[1,N]`; the fiber
  bijects (via `Fin.cons`/`Fin.tail`, `Finset.card_bij'`) with the `k`-tuple count at bound
  `⌊N/m⌋`; the harmonic sum `∑_{m≤N}1/m ≤ 1+log N` (`harmonic_le_one_add_log`,
  `harmonic_eq_sum_Icc`) closes the inductive step. ~140 lines, no `sorry`, no new axiom.
- `lattice_count_le_hyperbola (hk) (D) (hD) (R) (hR:1<R)` — bridges the GENERAL diagonal count
  `#{d∈piFinset D : ∏(dᵢ:ℝ)≤R}` (real `R`, arbitrary positive lattice `D`) down to the box
  count at `N=⌊R⌋₊` (the filtered set is a subset; `Finset.card_le_card`), then applies
  `hyperbola_count_le`. RHS `⌊R⌋₊·(1+log⌊R⌋₊)^{k-1}`.
- `diagonal_weight_le_hyperbola` — CAPSTONE: chaining `diagonal_weight_le_count` (weight ≤ C²·count)
  with the bridge gives the diagonal sieve weight an explicit closed-form bound
  `∑_{diag}|coeff| ≤ C²·⌊R⌋₊·(1+log⌊R⌋₊)^{k-1}`. Since `R=x^{θ/2}≪x≈MW`, this is `o(M(log R)^k)`
  — the diagonal half of analytic obligation #2, now reduced to an explicit `≍R(log R)^{k-1}`
  estimate (only the parameter relation `R = o(M log R)` remains, which is GPY plumbing, not analysis).

**Leaf (4) — the `IsLittleO` glue into `alphaBound`/`betaBound` — is now a MACHINE-CHECKED CHAIN.**
New in `Sieve.lean` (right after the `betaBound` def):
- `alphaBound_of_sub_littleO` / `betaBound_of_sub_littleO` — the STRUCTURAL CORE: `alphaBound` is
  `IsLittleO` of the *positive part* `max(sieveSum−α·main,0)`; since `max(f,0) =O f` (pointwise
  `|max(f,0)|≤|f|`, via `IsBigO.trans_isLittleO`+`isBigO_of_le`), the cleaner two-sided difference
  `sieveSum−α·alphaMainTerm = o(alphaMainTerm)` already implies the one-sided obligation.
- `alphaBound_of_heuristic_correction` / `betaBound_of_heuristic_correction` — the MODULAR ASSEMBLY:
  given the exact split `sieveSum = Aheur + Bcorr` (the heuristic main + correction, e.g.
  `sieveSum_separable_eq_heuristic_add_correction`), the heuristic-main limit
  `Aheur−α·main = o(main)` (leaf 1) AND the correction bound `Bcorr = o(main)` (leaves 2,3)
  together yield `alphaBound` (via `IsLittleO.add`/`.sub`). This machine-checks the dependency
  **`leaf 1 ∧ leaves 2,3 ⟹ s1`** — leaf (4) is no longer an open analytic obligation, just the
  composition of the other three.

### Net state — `s1_holds_from_nonprime_asym` now bottoms out in exactly TWO genuine analytic nuts:
1. **Diagonal asymptotic (leaf 1)** — the scalar limit `B(F,F)=∑_{r sf}(φ(r)/r²)z_r² → I(F)·const`
   as `R→∞`. THE deep GPY nut; smooth core = Aristotle `weighted_riemann_2d` (`3e2b6a8d`, in flight,
   slow ~27%). Cauchy–Schwarz (`gpy_bilinear_cauchy_schwarz`) already collapsed all cross terms to
   this single diagonal limit; the 1-D factor `weighted_mertens` is proven & axiom-clean.
2. **Off-diagonal heuristic main = o(main) (leaf 3)** — `∑_{¬diag}coeffₚ·mainₚ`. The W-trick
   vanishing infra is largely built (`lattice_count_offdiag_vanish_Wtrick`,
   `lattice_count_pair_offdiag_vanish`, `sum_restrict_offdiag_vanish`, `correction_abs_bound`); what
   remains is the singular-series discrepancy/prime-gain bound + the GPY parameter plumbing
   (`W=∏_{p≤D₀}p`, `M=(B−A)/W`, `R=x^{θ/2}`) that closes both the off-diag main and the leaf-2
   `R = o(M log R)` tail.
Leaves (2) and (4) are DONE (in-kernel). Everything algebraic + the glue is machine-checked.

## Leaf (1) DECOMPOSED: 2-D simplex limit proven modulo inner uniform convergence (2026-06-04, lap N+2 cont.)

Commit `9206855`, full build green (8278), all decls `#print axioms = [propext, Classical.choice, Quot.sound]`.

New file **`BoundedGaps/WeightedRiemann2D.lean`** reduces leaf (1)'s deep nut — the 2-D
simplex-coupled weighted Riemann limit (= the in-flight Aristotle `weighted_riemann_2d`) — to a
SINGLE clean ingredient, with everything else proven in-kernel:
- `phi_continuousOn` — the simplex partial-integral `Φ_G(x) = ∫₀^{1-x} G` is continuous on `[0,1]`
  (`intervalIntegral.continuousOn_primitive_interval` ∘ continuous `1-x`).
- **`perturbed_riemann`** — THE analytic core: if `a R m → Φ(log m/log R)` *uniformly in `m∈[2,R]`*,
  then `(∑_m F(log m/log R)·a R m/m)/log R → ∫₀¹ F·Φ`. Lifts the 1-D `riemann_sum_log_weight` to an
  `R`-dependent integrand via `MAIN + ERROR` (MAIN = the `Φ`-weighted limit; ERROR squeezed by the
  uniform bound × the bounded `(∑_m|F|/m)/log R → ∫₀¹|F|`).
- `two_d_factor` — the `mn≤R` double sum factors over the outer variable into `perturbed_riemann`'s
  shape (`Finset.mul_sum` to peel `F/m`, `Finset.sum_div` to peel `1/log R`; unconditional).
- **`weighted_riemann_2d_of_inner`** — CAPSTONE: the full 2-D simplex limit GIVEN the inner uniform
  claim `(∑_{n≤R/m} G(log n/log R)/n)/log R → Φ_G(log m/log R)` uniformly in `m`.

**Net for leaf (1):** the deep 2-D nut is now ONLY the *inner uniform convergence* — a 1-D-shaped,
self-contained statement (a far better Aristotle target than the monolithic double sum, and a hedge
if the running `weighted_riemann_2d` job fails). Architected as `aristotle-inner-uniform/Problem.lean`
(statement `inner_uniform`, `riemann_sum_log_weight` provided as usable axiom + a split-at-`R^{1-δ}`
proof sketch). The pointwise scale-change is easy (`G((1-s)u)` substitution); the crux is uniformity
for `m` near `R` (small `R'=⌊R/m⌋`), saved by `1-s` small ⟹ both sum and integral `O(1-s)`.

### s1 leaf scoreboard (after lap N+2)
- Leaf (1) diagonal asymptotic: **DECOMPOSED** — reduced to `inner_uniform` (Aristotle target).
- Leaf (2) `∑_{diag}|coeff|=o(main)`: **DONE in-kernel** (`hyperbola_count_le` + bridge + capstone).
- Leaf (3) off-diagonal heuristic main = o(main): OPEN (singular-series discrepancy, multi-lap).
- Leaf (4) `IsLittleO` glue: **DONE** (`alphaBound_of_sub_littleO` + `_of_heuristic_correction`).

## Leaf (1) FURTHER REDUCED: uniform ⟹ pointwise via Pólya (2026-06-04, lap N+3)

The prior lap reduced leaf (1) to the *inner uniform* convergence (`inner_uniform`). This lap
reduces THAT, in-kernel and axiom-clean, to a single **1-D pointwise** scale-change limit — a
strictly easier and self-contained Aristotle target. Three new modules, all
`#print axioms = [propext, Classical.choice, Quot.sound]`, full build green (8280 jobs).

- **`BoundedGaps/PolyaUniform.lean`** — `polya_uniform`: **Pólya's theorem** (NEW to the project,
  not in mathlib; mathlib only has Dini, monotone-in-*index*). If `Φn R` is monotone *in the
  argument* on `[0,1]`, `Φ` is continuous, and `Φn R t → Φ t` pointwise, then the convergence is
  UNIFORM on `[0,1]`. Finite-grid bracket + monotone sandwich + uniform continuity of `Φ`. No
  continuity of the `Φn R` required (they are step functions here).

- **`BoundedGaps/InnerUniformReduction.lean`** — the reduction chain (`Ψ G R t =
  (∑_{n≤⌊R^t⌋} G(log n/log R)/n)/log R`):
  - `floor_rpow_one_sub`: the exact reparametrisation `⌊R^{1-log m/log R}⌋₊ = R/m` (since
    `m = R^{log m/log R}`), so the inner sum IS `Ψ G R t` at `t = 1 - log m/log R`.
  - `psi_monotoneOn`: for `G ≥ 0`, `Ψ G R ·` is monotone on `[0,1]` (`⌊R^t⌋` grows, nonneg terms;
    `/log R ≥ 0`; `R ≤ 1` gives the constant-0 map).
  - `inner_uniform_of_pointwise_nonneg` (`G ≥ 0`) and `inner_uniform_of_pointwise` (arbitrary
    continuous `G`, via the `G = G⁺ − G⁻` split): the inner-uniform `huni` follows from the
    pointwise limit `Ψ H R t → ∫₀^t H` alone.
  - **`weighted_riemann_2d_of_psi_pointwise`** — composes with `weighted_riemann_2d_of_inner` to
    produce the FULL 2-D simplex limit (verbatim the deep axiom / Aristotle target
    `weighted_riemann_2d`) from just the pointwise limit.

**Net for leaf (1):** the entire 2-D nut is now reduced — axiom-clean, in our kernel — to the single
1-D pointwise limit `psi_tendsto : Ψ G R t → ∫₀^t G` (fixed `t`, continuous `G`). Submitted as
Aristotle job `1f84c4d6` (`aristotle-psi-pointwise/Problem.lean`), strictly easier than the
monolithic uniform target. The classical "fixed-`m` scale change": `N = ⌊R^t⌋`, `c_R = log N/log R
→ t`, rewrite `G(log n/log R) = G(c_R·(log n/log N))`, drift-bound by uniform continuity, apply
`riemann_sum_log_weight` to `G(t·)`, multiply by `c_R` and substitute `y = t·u`.

### s1 leaf scoreboard (after lap N+3)
- Leaf (1) diagonal asymptotic: **REDUCED to 1-D pointwise `psi_tendsto`** (Aristotle `1f84c4d6`);
  `weighted_riemann_2d_of_psi_pointwise` closes the 2-D limit modulo it, in-kernel.
- Leaf (2) `∑_{diag}|coeff|=o(main)`: **DONE in-kernel**.
- Leaf (3) off-diagonal heuristic main = o(main): OPEN (singular-series discrepancy, multi-lap).
- Leaf (4) `IsLittleO` glue: **DONE**.

## Leaf (1) SMOOTH CORE CLOSED: weighted_riemann_2d proven unconditionally (2026-06-04, lap N+3 cont.)

Continuing the same lap, `psi_tendsto` (the 1-D pointwise scale-change limit, the sole remaining
ingredient) was PROVEN in-kernel, and fed through the reduction chain to close the 2-D limit. Commit
`68e9eb0`; `#print axioms` clean; full build green (8280). The three redundant Aristotle leaf-1 jobs
(`3e2b6a8d` monolithic 2-D, `79da4f45` inner_uniform, `1f84c4d6` psi_tendsto) were CANCELLED.

- **`psi_tendsto`** (`InnerUniformReduction.lean`): `Ψ G R t = (∑_{n≤⌊R^t⌋} G(log n/log R)/n)/log R
  → ∫₀^t G` for fixed `t∈[0,1]`, continuous `G`. Proof: with `N=⌊R^t⌋`, `c_R=log N/log R`,
  `Ψ G R t = c_R · B R`. `B R → ∫₀¹ G(t·u)du` because the `c_R`-drifted Riemann sum equals the
  `t`-scaled one (`riemann_sum_log_weight` on `F_t=G(t·)`, composed with `N→∞`) up to an error
  bounded by `(ε/4)·(∑1/n)/log N ≤ ε/2` (uniform continuity of `G` gives the per-term `ε/4`; the
  harmonic ratio `tendsto_harmonic_icc2_div_log` gives the `≤2`). `c_R → t`
  (`tendsto_logFloor_rpow_div`). Substitution `t·∫₀¹G(t·u)du = ∫₀^t G` via
  `intervalIntegral.mul_integral_comp_mul_left`.
- **`weighted_riemann_2d`** (UNCONDITIONAL): `weighted_riemann_2d_of_psi_pointwise … (fun H hH t ht
  => psi_tendsto H hH t ht)`. The 2-D simplex weighted Riemann limit = leaf 1's smooth core, CLOSED.

### s1 leaf scoreboard (after lap N+3 cont.)
- Leaf (1) diagonal asymptotic **SMOOTH CORE CLOSED** (`weighted_riemann_2d` proven). REMAINING:
  the GPY port — connect `gpy_diagonal_asymptotic_form`'s `∑_{r sf}(φ/r²)z_r²` to the
  `weighted_riemann_2d` double-sum shape (Möbius/singular-series manipulation) + `𝔖(H)` Euler product.
- Leaf (2) `∑_{diag}|coeff|=o(main)`: **DONE in-kernel**.
- Leaf (3) off-diagonal heuristic main = o(main): OPEN (singular-series discrepancy, multi-lap).
- Leaf (4) `IsLittleO` glue: **DONE**.
