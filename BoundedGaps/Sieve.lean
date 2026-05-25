/-
# Multidimensional Selberg sieves (Polymath8b §4-§6).

The Maynard-Tao sieve replaces GPY's one-dimensional weight by a
multi-dimensional one indexed by the divisors of each shifted prime
separately. The bounded-gap program then reduces to a variational problem:
find a smooth function $F$ on the $k$-simplex maximizing a Rayleigh-like ratio.

Polymath8b's contribution is (a) extending the support of $F$ beyond the
simplex under GEH, and (b) efficient numerical methods for the variational
problem in small/medium dimension.

We capture: the ratio $M_k(F)$, the Maynard quantity $M_k = \sup_F M_k(F)$,
the criterion $M_k > 4m/\delta \Rightarrow \DHL[k, m+1]$ (in the BV regime),
and the pigeonhole "Lemma crit" reduction.

Reference: [../papers/pdf/polymath8b-2014-variants.pdf](../papers/pdf/polymath8b-2014-variants.pdf) §4-§6.
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Prerequisites

namespace BoundedGaps.Sieve

open BoundedGaps

/-! ### Selberg sieve weight (Polymath8b §3, eqns (3.6)-(3.7))

The weights are constructed from divisor sums against a smooth cutoff $F$.
The base-$x$ logarithm scales the cutoff to the natural range for divisors of
$n \in [x, 2x]$: $\log_x d \in [0, 1]$ for $d \le x$, etc. -/

open ArithmeticFunction (moebius)

/-- The divisor sum
$$\lambda_F(n) := \sum_{d \mid n} \mu(d) F(\log_x d)$$
(Polymath8b eqn (3.6)). Real body wired to `ArithmeticFunction.moebius`. -/
noncomputable def lambdaF (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (moebius d : ℝ) * F (Real.log d / Real.log x)

/-- The Maynard-Tao sieve weight $\nu(n)$ for an admissible $k$-tuple
$\mathcal{H} = (h_1, \ldots, h_k)$. The full Polymath8b construction is the
square of a $k$-fold sum over a basis of cutoff functions; this simplified
form takes a *single* multivariate cutoff $F$ and forms the $k$-fold product
of $\lambda$-sums applied to the shifted primes $n + h_i$, then squares it.

For each $i$, the marginal cutoff is $F_i(t) := F(0, \ldots, t, \ldots, 0)$
with $t$ in the $i$-th coordinate. A faithful translation of Polymath8b §3
would replace this with a sum over a tensor-product basis — we use the simpler
form for now since the structural shape is the same. -/
noncomputable def maynardWeight (k : ℕ) (F : (Fin k → ℝ) → ℝ) (H : List ℕ)
    (x : ℝ) (n : ℕ) : ℝ :=
  let marginal (i : Fin k) : ℝ → ℝ :=
    fun t => F (fun j => if j = i then t else 0)
  let shifted (i : Fin k) : ℕ :=
    n + (H[i.val]?).getD 0
  (∏ i, lambdaF (marginal i) x (shifted i)) ^ 2

/-! ### The pigeonhole criterion (Polymath8b Lemma 3.3 — "Lemma crit") -/

/-- Sum bound (Polymath8b eqn (3.4)): the numerator-style upper bound. -/
-- TRIAGE: DEF BODY (~2-3h) — has a precise statement (asymptotic sum of ν
-- against a residue class), should be defined properly when sieve scaffolding
-- lands. Could be `opaque def alphaBound : ... → Prop` short-term to make
-- consumers honest, but a real definition is the right end-state.
def alphaBound (k : ℕ) (ν : ℕ → ℝ) (b W : ℕ) (x : ℝ) (α : ℝ) : Prop := sorry

/-- Sum bound (Polymath8b eqn (3.5)): the per-shift lower bound, $i = 1, \ldots, k$. -/
-- TRIAGE: DEF BODY (~2-3h) — sister of alphaBound. Same `opaque def` vs
-- "define properly" choice. Bundle with alphaBound.
def betaBound (k : ℕ) (ν : ℕ → ℝ) (H : List ℕ) (b W i : ℕ) (x : ℝ) (β : ℝ) : Prop := sorry

/-- **"Lemma crit"** (Polymath8b Lemma 3.3): pigeonhole criterion for DHL.

If for every admissible $k$-tuple $\mathcal{H}$ and every coprime residue
class $b \pmod{W}$ one can find non-negative weights $\nu$ and positive
quantities $\alpha, \beta_1, \ldots, \beta_k$ with the asymptotic bounds
`alphaBound` and `betaBound`, satisfying the **key inequality**
$\frac{\beta_1 + \cdots + \beta_k}{\alpha} > m$, then $\DHL[k, m+1]$ holds. -/
-- TRIAGE: PROVABLE (~3-4h) — Polymath8b's Lemma 3.3 pigeonhole argument.
-- Requires alphaBound/betaBound to be real defs first. This is the heart of
-- the sieve→DHL reduction; once done, all maynard_thm variants below become
-- 30-line follow-ons.
theorem dhl_criterion (k m : ℕ) (_hk : k ≥ 2) (_hm : m ≥ 1)
    (_hWeights : ∀ H : List ℕ, Admissible H → H.length = k →
      ∃ (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
        α > 0 ∧ (∀ i, β i ≥ 0) ∧ (∑ i, β i) / α > m) :
    DHL k (m + 1) := sorry

/-! ### The variational problem (Polymath8b §5-§6) -/

/-- The Maynard simplex: $\{ t \in \mathbb{R}^k : t_i \ge 0,\ \sum_i t_i \le 1 \}$.

Polymath8b §5 defines the Maynard variational problem over smooth functions
$F$ supported on this set. Concrete `Set`-level def — usable in `setIntegral`. -/
noncomputable def simplex (k : ℕ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 }

/-- The Rayleigh-ratio denominator: $\int_{\text{simplex}_k} F^2$.

Polymath8b §5 (eqn defining $M_k(F)$). Concrete measure-theoretic def using
the default Lebesgue volume on $\mathbb{R}^k$. -/
noncomputable def mkF_denominator (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in simplex k, F t ^ 2

/-- The Rayleigh-ratio numerator $J_k(F)$ of Polymath8b §5:
$$J_k(F) := \sum_{i=1}^{k} \int_{R_{k-1}}
  \left(\int_0^{1 - \sum_{j \ne i} t_j} (\partial_i F)(t) \, dt_i\right)^2
  dt_{\setminus i}$$
where $R_{k-1}$ is the $(k-1)$-simplex and $t = \mathtt{insertNth}\, i\, t_i\, s$
embeds the $(k-1)$-coordinate vector $s$ and the singled-out coordinate $t_i$
back into $\mathbb{R}^k$ at position $i$. Partial derivatives are realized as
`fderiv ℝ F t (Pi.single i 1)`.

Pattern-matched on $k$: the $k = 0$ case is vacuous (empty sum), and the
$k = n + 1$ case carries the formula above. -/
noncomputable def mkF_numerator : (k : ℕ) → ((Fin k → ℝ) → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, F =>
      ∑ i : Fin (n + 1),
        ∫ s in simplex n,
          (∫ ti in Set.Icc (0 : ℝ) (1 - ∑ j, s j),
              fderiv ℝ F (i.insertNth ti s) (Pi.single i 1)) ^ 2

/-- The Maynard quantity $M_k(F) := J_k(F) / \int_{\text{simplex}_k} F^2$:
a Rayleigh-style ratio for a smooth $F$ supported on the $k$-simplex.
(Polymath8b §5.) Fully concrete — both numerator and denominator are
real definitions. -/
noncomputable def MkF (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  mkF_numerator k F / mkF_denominator k F

/-- **Polymath8b §5 definition of $M_k(F)$**: the Maynard quantity is the
Rayleigh ratio $J_k(F) / \int_{\text{simplex}_k} F^2$. Now a theorem
discharged by `rfl` — was an axiom while either side was opaque. -/
theorem MkF_eq_rayleigh (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    MkF k F = mkF_numerator k F / mkF_denominator k F := rfl

/-- $M_k := \sup_F M_k(F)$ over admissible $F$ on the simplex.

Concrete `sSup` over the set of `MkF k F` values where $F$ is smooth,
supported on the simplex, and has nonzero Rayleigh denominator (so the
ratio is well-defined). Per `Mathlib`'s `ℝ`-`ConditionallyCompleteLinearOrder`
convention, an empty or unbounded admissible set yields `0`; in the
relevant Polymath8b regime ($k \ge 2$) the set is non-empty and bounded. -/
noncomputable def Mk (k : ℕ) : ℝ :=
  sSup { v | ∃ F : (Fin k → ℝ) → ℝ,
              ContDiff ℝ ⊤ F ∧
              Function.support F ⊆ simplex k ∧
              mkF_denominator k F > 0 ∧
              v = MkF k F }

/-- $M_{k, \varepsilon}$: Polymath8b's enlarged-support variant. Under GEH the
support of $F$ may extend an $\varepsilon$ distance beyond the simplex.

Currently declared `opaque`. Same shape as `Mk` but over the extended
support polytope; needed by `epsilon_trick` / `epsilon_beyond`. -/
-- TRIAGE: DEF BODY (~2h after Mk).
opaque Mk_eps (k : ℕ) (ε : ℝ) : ℝ

/-! ### The variational lower bounds → DHL conversions
(Polymath8b §5: Theorems "maynard-thm", "maynard-trunc", "epsilon-trick",
"epsilon-beyond") -/

/-- **Theorem 5.2 / "maynard-thm"** (under EH): if $M_k > 4m/\vartheta$ for
some $\vartheta < 1$, and EH[ϑ] holds for that $\vartheta$, then $\DHL[k, m+1]$. -/
-- TRIAGE: NEEDS_SIEVE — follows from dhl_criterion once the variational
-- machinery (Mk, MkF) has real bodies. Maynard's original argument, ~1-2h
-- after the prerequisites land.
theorem maynard_thm (k m : ℕ) (ϑ : ℝ) (_hϑ : 0 < ϑ ∧ ϑ < 1)
    (_hEH : Prerequisites.EH ϑ)
    (_hMk : Mk k > 4 * m / ϑ) : DHL k (m + 1) := sorry

/-- **Theorem 5.3 / "maynard-trunc"** (under MPZ): truncated variant suitable
for the Zhang/Polymath8a regime. -/
-- TRIAGE: NEEDS_SIEVE — Polymath8a-flavored variant; truncated weights to
-- handle smooth-moduli regime. Same blocker chain as maynard_thm.
theorem maynard_trunc (k m : ℕ) (ϖ δ : ℝ)
    (_hMPZ : Prerequisites.MPZ ϖ δ) (_hMk : Mk k > 4 * m / (1 / 2 + 2 * ϖ)) :
    DHL k (m + 1) := sorry

/-- **Theorem 5.4 / "epsilon-trick"** (under BV alone, ε refinement). -/
-- TRIAGE: NEEDS_SIEVE — uses Mk_eps. Polymath8b's ε-refinement of Maynard.
theorem epsilon_trick (k m : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (_hMk : Mk_eps k ε > 4 * m) : DHL k (m + 1) := sorry

/-- **Theorem 5.5 / "epsilon-beyond"** (under GEH, the strongest variant). -/
-- TRIAGE: NEEDS_SIEVE — strongest variant, uses GEH + Mk_eps. Yields the
-- parity-tight H_1 ≤ 6 under GEH.
theorem epsilon_beyond (k m : ℕ) (ε : ℝ) (ϑ : ℝ)
    (_hGEH : Prerequisites.GEH ϑ) (_hε : 0 < ε)
    (_hMk : Mk_eps k ε > 2 * m / ϑ) : DHL k (m + 1) := sorry

end BoundedGaps.Sieve
