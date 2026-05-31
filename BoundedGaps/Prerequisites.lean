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

open ArithmeticFunction Finset
open scoped ArithmeticFunction NNReal

/-! ## The discrepancy foundation (precise, von-Mangoldt-faithful)

We model the Elliott-Halberstam family on a concrete *discrepancy*: how far an
arithmetic function `f`, restricted to the dyadic window `[x, 2x]`, deviates
from equidistribution across the reduced residue classes mod `q`. EH, GEH, MPZ
are then genuine level-of-distribution bounds on `∑_{q ≤ Q} max_a |Δ|`, differing
only in (the function class, the modulus set, the level `Q`).

This replaces the earlier contentless `axiom EH (ϑ : ℝ) : Prop`. With real bodies,
the unconditional inputs (`BombieriVinogradov` etc.) become axioms asserting the
*actual* theorems, and the structural implications between the hypotheses
(`eh_implies_mpz`) become ordinary proofs. -/

/-- The dyadic window `[x, 2x] ∩ ℕ`, as a `Finset ℕ`. -/
noncomputable def window (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊2 * x⌋₊).filter (fun n => x ≤ (n : ℝ))

/-- The reduced residues mod `q`: representatives in `[0, q)` coprime to `q`. -/
def coprimeRes (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- The **discrepancy** of `f` (supported on `[x, 2x]`) in the residue class
`a mod q`: the count `∑_{n ≡ a (q)} f n` minus its expected value
`(1/φ(q)) ∑_{(n,q)=1} f n` over the reduced classes. -/
noncomputable def discrepancy (f : ℕ → ℝ) (x : ℝ) (q a : ℕ) : ℝ :=
  (∑ n ∈ (window x).filter (fun n => n % q = a % q), f n)
    - (1 / (q.totient : ℝ)) * (∑ n ∈ (window x).filter (fun n => Nat.Coprime n q), f n)

/-- The per-modulus term `max_{a : (a,q)=1} |Δ(f; x, q, a)|`, as an `ℝ≥0`.
Taken in `ℝ≥0` (via `Finset.sup`, bottom `0`) so it is total — `0` when there are
no reduced classes — and non-negative for free, which is what the subset
monotonicity in `eh_implies_mpz` needs. -/
noncomputable def maxDisc (f : ℕ → ℝ) (x : ℝ) (q : ℕ) : ℝ≥0 :=
  (coprimeRes q).sup (fun a => Real.nnabs (discrepancy f x q a))

/-- `q` is `δ`-**smooth** (relative to `x`): squarefree with every prime factor
`≤ x^δ`. This is the MPZ modulus restriction (Polymath8b §2, Claim 2.3). -/
def IsSmooth (δ x : ℝ) (q : ℕ) : Prop :=
  Squarefree q ∧ ∀ p ∈ q.primeFactors, (p : ℝ) ≤ x ^ δ

/-- **Elliott-Halberstam conjecture at level $\vartheta$**, EH[ϑ]
(Polymath8b §2, Claim 2.2).

For every $A \ge 0$ there is $C > 0$ with, for all $x \ge 2$,
  $\sum_{q \le x^\vartheta} \max_{(a,q)=1}
    |\Delta(\Lambda; x, q, a)| \le C\, x (\log x)^{-A}$,
the discrepancy taken against the von Mangoldt function $\Lambda$ on $[x, 2x]$.

Conjectured for all $0 < \vartheta < 1$ in [Elliott-Halberstam 1970]. Known
unconditionally for $\vartheta < 1/2$ (Bombieri-Vinogradov, [BombieriVinogradov]
below). -/
def EH (ϑ : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    (↑(∑ q ∈ Finset.Icc 1 ⌊x ^ ϑ⌋₊, maxDisc (fun n => vonMangoldt n) x q) : ℝ)
      ≤ C * x / (Real.log x) ^ A

/-- **Generalized Elliott-Halberstam at level $\vartheta$**, GEH[ϑ]
(Polymath8b §2, Claim 2.6).

Same kind of bound as EH but applied to Dirichlet convolutions
$\alpha \star \beta$ (with Siegel-Walfisz hypothesis on $\beta$), not just to
$\Lambda$. Strictly stronger than $\EH$:
`GEH ϑ → EH ϑ` is `geh_implies_eh` below. Conjectured for all
$0 < \vartheta < 1$ in [Bombieri-Friedlander-Iwaniec 1986]; known
unconditionally for $\vartheta < 1/2$ (Motohashi's generalized BV). -/
axiom GEH (ϑ : ℝ) : Prop

open Classical in
/-- **Motohashi-Pintz-Zhang estimate**, MPZ[ϖ, δ] (Polymath8b §2, Claim 2.3).

Weakening of EH that restricts to *smooth* moduli with prime factors $\le x^\delta$
but allows level of distribution beyond $1/2$: specifically $Q \le x^{1/2 + 2\varpi}$.
Structurally **identical to `EH` except** the modulus set is filtered to the
`δ`-smooth `q` (and the level is `1/2 + 2ϖ`). The per-modulus term is the same
`maxDisc` of $\Lambda$ — which is exactly why `EH[1/2+2ϖ] → MPZ[ϖ,δ]` is a
sub-sum (`eh_implies_mpz`).

`IsSmooth` involves a real comparison `p ≤ x^δ`, so the filter is classical. -/
def MPZ (ϖ δ : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    (↑(∑ q ∈ (Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * ϖ)⌋₊).filter (IsSmooth δ x),
        maxDisc (fun n => vonMangoldt n) x q) : ℝ)
      ≤ C * x / (Real.log x) ^ A

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
-- TRIAGE: PROVABLE (~tens of lines, but only once EH and GEH have real bodies
-- rather than `axiom _ : Prop`). Currently EH/GEH are opaque Props so this
-- implication is unprovable as stated. Defer until the discrepancy-bound
-- machinery is in mathlib or we model EH/GEH concretely.
theorem geh_implies_eh (ϑ : ℝ) (_hGEH : GEH ϑ) : EH ϑ := sorry

/-- **EH[1/2 + 2ϖ] implies MPZ[ϖ, δ]** (trivial direction, Polymath8b §2).

Now a real proof: MPZ's modulus set is `EH`'s filtered to the `δ`-smooth `q`, the
per-modulus term (`maxDisc` of `Λ`) is identical, and every term is `≥ 0` (it is
an `ℝ≥0` sup of absolute discrepancies). So MPZ's sum is a **sub-sum** of EH's;
the EH bound `C x (log x)^{-A}` transfers verbatim. -/
theorem eh_implies_mpz {ϖ δ : ℝ} (_hϖ : 0 ≤ ϖ) (_hδ : 0 ≤ δ)
    (hEH : EH (1 / 2 + 2 * ϖ)) : MPZ ϖ δ := by
  classical
  intro A hA
  obtain ⟨C, hC, hbound⟩ := hEH A hA
  refine ⟨C, hC, fun x hx => ?_⟩
  refine le_trans ?_ (hbound x hx)
  -- sub-sum: smooth moduli ⊆ all moduli at the same level; ℝ≥0 is canonically
  -- ordered so dropping the filter only grows the sum. `apply` lets the goal's
  -- own `DecidablePred` (from MPZ's def) drive instance inference.
  apply NNReal.coe_le_coe.mpr
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset _ _

/-! ## Consuming the axioms — sanity-check demonstrations

These are real proofs that exercise the BV / GBV / MPZ axioms at specific
parameter values. They confirm the axioms are usable as black-box inputs
and serve as the smallest "consumer" examples — once the Sieve.lean chain
is built, downstream theorems will look like these but at scale. -/

/-- BV applied at $\vartheta = 1/3$: yields `EH (1/3)`. -/
theorem EH_one_third : EH (1 / 3 : ℝ) :=
  BombieriVinogradov ⟨by norm_num, by norm_num⟩

/-- BV applied at $\vartheta = 0.49$: a useful pre-1/2 level. -/
theorem EH_at_0_49 : EH (49 / 100 : ℝ) :=
  BombieriVinogradov ⟨by norm_num, by norm_num⟩

/-- GBV applied at $\vartheta = 1/3$: yields `GEH (1/3)`. -/
theorem GEH_one_third : GEH (1 / 3 : ℝ) :=
  GeneralizedBombieriVinogradov ⟨by norm_num, by norm_num⟩

/-- MPZ at small $\varpi, \delta$: $\varpi = \delta = 1/200$ satisfies the
Polymath8a constraint $600\varpi + 180\delta < 7$ (gives $600/200 + 180/200 =
3.9 < 7$). -/
theorem MPZ_small : MPZ (1 / 200 : ℝ) (1 / 200 : ℝ) :=
  MPZ_polymath8a ⟨by norm_num, by norm_num, by norm_num⟩

end BoundedGaps.Prerequisites
