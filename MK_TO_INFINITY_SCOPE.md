# Scope: strictly formalizing Maynard's variational theorem `M_k → ∞`

**Question**: of the three bounded-gaps papers, which headline result is *strictly*
formalizable (axiom-free `#print axioms`) without a missing-deep-theorem wall?

**Answer**: not any paper's **prime-gap** conclusion — those all bottom out on
Bombieri–Vinogradov (Maynard, Polymath8b) or MPZ/Deligne (Zhang), neither in mathlib.
But the **genuine mathematical innovation of Maynard** — the multidimensional sieve
variational bound `M_k → ∞` — is *pure analysis on the simplex, no primes, no BV*, and is
strictly formalizable. This doc scopes it.

## Why this is the right target

`M_k = sup_F (Σᵢ Jᵢ(F)) / I(F)` over the unit simplex (`I(F)=∫F²`, `Jᵢ(F)=∫(∫F dtᵢ)²`).
GPY were stuck at `M_k ≤ 4` for *decades* using `F = function of ∑tᵢ`. Maynard's 2013
breakthrough was that **genuinely multivariate `F` makes `M_k → ∞`** (`M_k ≳ log k`), which
is what turns "small gaps infinitely often" into "bounded gaps." That theorem is his, it's
the heart of the paper, and it touches no prime.

## 🎁 The leverage already in this repo (this is the big news)

`SievePolynomial.Mk_ge_polynomialMkF` (axiom-clean, cutoff/DCT) gives, for **any** polynomial
sieve weight `P`:
> `Sieve.Mk k ≥ (polynomialMkF P : ℝ)`

and `polynomialMkF_eq_MkF` ties it to the exact rational ratio, where

- `monomialIntegral α = (∏ αᵢ!)/(k+|α|)!`        (`∫_simplex ∏ tᵢ^αᵢ`)
- `dirichletIntegralWithSlack α β = (∏ αᵢ!)·β!/(k+|α|+β)!`  (`∫_simplex ∏tᵢ^αᵢ (1-∑t)^β`)

**both already proven.** So the entire measure-theoretic layer is discharged: proving an
`M_k` lower bound reduces to a **purely algebraic statement about explicit ratios of
factorials** for a chosen polynomial family. No integrals left to evaluate at proof time.

Also in place:
- `SymmetricReduction.lean` — symmetric `F` is WLOG (full Rayleigh permutation-invariance).
- `EpsBridge`/`EpsScaling` — the same machinery for the ε-enlarged variant (not needed here).
- `Mk5Witness.lean` — a **worked strict instance**: `Sieve.Mk 5 > 2` via `native_decide` on
  `polynomialMkF P₅ = 12048682945/6016885374`. Axiom-clean modulo the standard `native_decide`
  trust. **This already is a strictly-formalized data point of Maynard's variational theorem.**

mathlib has the asymptotic toolkit verified present (v4.29.1 pin):
- `tendsto_stirlingSeq_sqrt_pi` — Stirling's formula `n! ~ √(2πn)(n/e)ⁿ`.
- `Real.Gamma`, `Real.betaIntegral`, `MeasureTheory`/`Probability.Distributions.Gamma`.
- `Real.log`, log/exp asymptotics, `Filter.Tendsto … atTop atTop`.

## The two strict targets

### Option A — `∃ k, Sieve.Mk k > c` for an explicit threshold (bounded, mostly mechanical)
Generalize `Mk5Witness` to a larger fixed `k` with the right polynomial, `native_decide` the
exact rational ratio, conclude `Mk k > c`. **Done for `c=2, k=5`.** Pushing to `Mk k > 4`
needs Maynard's optimized degree-`d` polynomial at the smallest such `k` (dozens), and the
`native_decide` rational arithmetic must stay tractable (the real risk — `SymmetricReduction`
helps by collapsing the symmetric sum). Payoff: a clean "the multidimensional sieve clears the
threshold" theorem, strict. Effort: ~1–3 sessions if a good polynomial is in hand; the
polynomial-hunt + compute scaling is the unknown.

### Option B — `Filter.Tendsto (fun k => Sieve.Mk k) atTop atTop`  ← **the headline**
The actual Maynard theorem. Strict, axiom-free, no `native_decide`. Phases:

1. **Pick the family.** `F_k = ∏ᵢ g(tᵢ)` with an explicit polynomial `g` (degree growing with
   `k`). Must be a genuine product (multivariate) — `function-of-∑tᵢ` provably can't exceed 4
   (the GPY wall), so this choice is mathematically forced. As a `PolynomialSieveWeight k`,
   `F_k`'s `polynomialMaynardNumerator/Denominator` are the symmetric factorial sums above.
   *Deliverable*: `def maynardFamily (k : ℕ) : PolynomialSieveWeight k`.

2. **The reduction lemma (the analytic spine).** Evaluate the separable simplex integral
   `∫_simplex ∏ᵢ φ(tᵢ)` in closed/asymptotic form. Two routes:
   - **(b-i) Probabilistic**: `∫_simplex ∏φ(tᵢ) = E[∏φ(Xᵢ) · 1_{∑Xᵢ≤1}]`-style identity via
     the Dirichlet–Gamma connection (iid `Exp(1)`), then concentration `∑Xᵢ ≈ k`. Uses
     mathlib's Gamma distribution. Cleanest conceptually; heaviest in probability API.
   - **(b-ii) Direct factorial asymptotics**: keep the explicit factorial sums, push the
     `k→∞` ratio with Stirling. More elementary, more bare-hands algebra.
   *This phase is the bulk of the work and the genuine mathematical content.*

3. **Optimize / estimate.** Choose `g` (Maynard: `g(t)≈1/(1+A t)`, `A=log k`, truncated to a
   polynomial) and show the ratio `→ ∞`. Even a crude `M_k ≥ c·log k` (no sharp constant)
   suffices for `Tendsto … atTop`. Uses Stirling + `Real.log` monotonicity.

4. **Assemble**: `Mk k ≥ polynomialMkF (maynardFamily k) → ∞ ⟹ Tendsto Mk atTop atTop`.
   (Step 4 is one `Filter.tendsto_atTop_mono` once step 3 lands.)

## Honest effort / risk

- **Option A**: bounded, weeks-not-months, but gated on (a) obtaining a good explicit
  polynomial and (b) `native_decide` compute at `k` in the dozens. Confidence feasible: ~80%.
- **Option B**: the real prize, but a **multi-month real-analysis project** whose spine
  (phase 2, the simplex-integral asymptotics) is substantial even with Stirling + Gamma in
  mathlib. No deep-theorem wall (this is "ordinary" analysis, not Deligne/BV), so it *will*
  go through — it's a matter of grind, not a blocker. Confidence feasible-in-principle: ~75%;
  confidence quick: low.

## Recommendation

If "strictly formalized" means an **axiom-free headline**: target **Option B**, with phase 2
(the Gamma/Stirling simplex-integral reduction) as the make-or-break spine — that's where the
months go and where the math actually lives. If the goal is a **fast strict win to bank**,
do **Option A** to the best `k` `native_decide` allows (a clean `∃k, Mk k > 4`), which is the
same machinery `Mk5Witness` already demonstrates.

Either way the foundational point holds: **the simplex/Rayleigh layer is already done and
axiom-clean**, so this is the one bounded-gaps result that is reachable without formalizing
Bombieri–Vinogradov first.
