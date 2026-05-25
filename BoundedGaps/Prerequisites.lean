/-
# Analytic-NT prerequisites.

The Polymath8b paper (§2) defines a family of parameterized distributional
hypotheses on primes in arithmetic progressions. We model them here as
parameterized `Prop`s; their statements are `axiom`-opaque so we can state
downstream theorems precisely without first formalizing the discrepancy-bound
machinery.

The three unconditional members of this family — **Bombieri-Vinogradov**,
**Generalized Bombieri-Vinogradov**, and **Polymath8a's MPZ estimate** — are
themselves declared as `axiom` rather than `theorem := sorry`. This is an
honest representation of the project's dependency surface: we *consume* these
deep analytic-NT results, we don't reprove them. When mathlib (or PNT+)
eventually ships proofs, the `axiom` lines become `theorem` lines and the
project's `#print axioms` shrinks accordingly.

By contrast, the *trivial* implications between EH, GEH, and MPZ remain
`theorem := sorry` — those are our work to do.

References (local copies):
- [../papers/pdf/polymath8b-2014-variants.pdf](../papers/pdf/polymath8b-2014-variants.pdf), §2
- [../papers/pdf/polymath8a-2014-zhang-type-equidistribution.pdf](../papers/pdf/polymath8a-2014-zhang-type-equidistribution.pdf)
-/
import Mathlib

namespace BoundedGaps.Prerequisites

/-- **Elliott-Halberstam conjecture at level $\vartheta$**, EH[ϑ]
(Polymath8b §2, Claim 2.2).

Schematically: for $Q \le x^\vartheta$ and $A \ge 1$,
  $\sum_{q \le Q} \sup_{a \in (\mathbb{Z}/q\mathbb{Z})^\times}
    |\Delta(\Lambda \mathbf{1}_{[x,2x]}; a\ (q))| \ll x \log^{-A} x$.

Conjectured for all $0 < \vartheta < 1$ in
[Elliott-Halberstam 1970]. Known unconditionally for $\vartheta < 1/2$
(Bombieri-Vinogradov, [BombieriVinogradov] below). -/
axiom EH (ϑ : ℝ) : Prop

/-- **Generalized Elliott-Halberstam at level $\vartheta$**, GEH[ϑ]
(Polymath8b §2, Claim 2.6).

Same kind of bound as EH but applied to Dirichlet convolutions
$\alpha \star \beta$ (with Siegel-Walfisz hypothesis on $\beta$), not just to
$\Lambda$. Strictly stronger than $\EH$:
`GEH ϑ → EH ϑ` is `geh_implies_eh` below. Conjectured for all
$0 < \vartheta < 1$ in [Bombieri-Friedlander-Iwaniec 1986]; known
unconditionally for $\vartheta < 1/2$ (Motohashi's generalized BV). -/
axiom GEH (ϑ : ℝ) : Prop

/-- **Motohashi-Pintz-Zhang estimate**, MPZ[ϖ, δ] (Polymath8b §2, Claim 2.3).

Weakening of EH that restricts to *smooth* moduli with prime factors $\le x^\delta$
but allows level of distribution beyond $1/2$: specifically $Q \le x^{1/2 + 2\varpi}$.

Used in the Zhang/Polymath8a proof path. Bypassed by Maynard's proof. -/
axiom MPZ (ϖ δ : ℝ) : Prop

/-- **Bombieri-Vinogradov theorem** (1965). EH holds unconditionally for
every fixed $0 < \vartheta < 1/2$. Polymath8b Theorem 2.4.

Declared as `axiom`: this project consumes BV as a black-box analytic-NT
input. When PNT+ (or mathlib) ships a proof, this declaration becomes
`theorem BombieriVinogradov ... := PNT.bombieriVinogradov` (or similar). -/
axiom BombieriVinogradov {ϑ : ℝ} (h : 0 < ϑ ∧ ϑ < 1 / 2) : EH ϑ

/-- **Generalized Bombieri-Vinogradov** (Motohashi 1976). GEH holds
unconditionally for every fixed $0 < \vartheta < 1/2$. Polymath8b Theorem 2.8.

Declared as `axiom` for the same reason as `BombieriVinogradov`. -/
axiom GeneralizedBombieriVinogradov {ϑ : ℝ} (h : 0 < ϑ ∧ ϑ < 1 / 2) : GEH ϑ

/-- **Polymath8a Theorem 2.17**: MPZ holds for every fixed $\varpi, \delta \ge 0$
with $600\varpi + 180\delta < 7$. In particular, $\varpi$ can be taken
arbitrarily close to $7/600 \approx 0.01167$.

Declared as `axiom`: Polymath8a's proof is the most analytically demanding
input we use (exponential sums on smooth moduli, far outside mathlib's
current reach). -/
axiom MPZ_polymath8a {ϖ δ : ℝ} (h : 0 ≤ ϖ ∧ 0 ≤ δ ∧ 600 * ϖ + 180 * δ < 7) :
    MPZ ϖ δ

/-- **GEH implies EH** (Polymath8b Proposition 2.7).
Proof sketch uses Vaughan's identity to decompose $\Lambda$. -/
theorem geh_implies_eh (ϑ : ℝ) (_hGEH : GEH ϑ) : EH ϑ := sorry

/-- **EH[1/2 + 2ϖ] implies MPZ[ϖ, δ]** (trivial direction, Polymath8b §2). -/
theorem eh_implies_mpz {ϖ δ : ℝ} (_hϖ : 0 ≤ ϖ) (_hδ : 0 ≤ δ)
    (_hEH : EH (1 / 2 + 2 * ϖ)) : MPZ ϖ δ := sorry

end BoundedGaps.Prerequisites
