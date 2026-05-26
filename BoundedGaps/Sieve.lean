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

/-! ### The pigeonhole criterion (Polymath8b §3 — "Lemma crit")

The pigeonhole reduction from sieve weight existence to DHL is split into
two named sub-lemmas mirroring the seams of Polymath8b §3's proof:

1. `witness_eventually_from_sieve_data` — analytic/algebraic core: from
   (s1), (s2), and the key ratio, derive that for arbitrarily large $N$
   there is a witness $n \in [N, 2N]$ with $\ge m + 1$ of $n + h_i$ prime.
2. `infinite_witnesses_of_eventual_witness` — topological wrap-up: per-$N$
   witnesses give `Set.Infinite`.

`dhl_criterion` is a 3-line composition of these two over an arbitrary
admissible $\mathcal{H}$.

Sources: Polymath8b §3 (Lemma `crit`); the original pigeonhole step appears
in Maynard 2015 ("Small gaps between primes") §4. -/

/-- The asymptotic upper bound (Polymath8b §3 eqn (s1)):
$$\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)
   \le (\alpha + o(1)) B^{-k} \frac{x}{W}$$
as $x \to \infty$, where $B := \phi(W)/W \cdot \log x$. Currently declared
`opaque` — a real def needs `Asymptotics.IsLittleO` plus the Mertens
product $W$ as a sieve parameter; out of current scope. -/
opaque alphaBound (k : ℕ) (ν : ℕ → ℝ) (b W : ℕ) (x : ℝ) (α : ℝ) : Prop

/-- The asymptotic lower bound (Polymath8b §3 eqn (s2)):
$$\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)\, \theta(n + h_i)
   \ge (\beta_i - o(1)) B^{1-k} \frac{x}{\phi(W)}$$
as $x \to \infty$, for $i = 1, \ldots, k$. Sister of `alphaBound`. -/
opaque betaBound (k : ℕ) (ν : ℕ → ℝ) (H : List ℕ) (b W i : ℕ) (x : ℝ)
    (β : ℝ) : Prop

/-- **Step 1 of Lemma crit (Polymath8b §3, analytic core)**: from the sieve
bounds (s1) and (s2), and the key ratio $(\beta_1 + \cdots + \beta_k)/\alpha > m$,
one deduces that for arbitrarily large $N$ there exists $n \in [N, 2N]$ with
at least $m + 1$ of $n + h_i$ prime.

Paper proof structure (Polymath8b §3, proof of Lemma crit, paragraphs 1-3):
1. Combine (s1) and (s2) to lower-bound
   $$N(x) := \sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)
              \left( \sum_i \theta(n + h_i) - m \log 3x \right).$$
2. Substituting $B := \phi(W)/W \cdot \log x$ and using the key ratio,
   $N(x) > 0$ for $x$ sufficiently large.
3. The parenthetical $\sum_i \theta(n+h_i) - m \log 3x$ can be positive
   only when at least $m + 1$ of $n + h_i$ are prime, so at least one
   such $n$ exists in $[x, 2x]$. -/
-- TRIAGE: PROVABLE (~2-3h once a project-level Chebyshev-θ def exists). The
-- pigeonhole step also needs a small `(p.Prime → log p ≤ θ p)` type bridge.
-- Polymath8b §3 Lemma crit, paragraphs 1-3.
theorem witness_eventually_from_sieve_data
    {k : ℕ} (H : List ℕ) (_hAdm : Admissible H) (_hLen : H.length = k)
    {m : ℕ} {b W : ℕ} {ν : ℕ → ℝ} {α : ℝ} {β : Fin k → ℝ}
    (_hα : 0 < α) (_hβ : ∀ i, 0 ≤ β i)
    (_hKey : (∑ i, β i) / α > m)
    (_hS1 : ∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α)
    (_hS2 : ∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
              betaBound k ν H b W i.val x (β i)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      H.countP (fun h => (n + h).Prime) ≥ m + 1 := sorry

/-- **Step 2 of Lemma crit (topological wrap-up)**: per-$N$ witnesses in
$[N, 2N]$ give an infinite set of witnesses. Polymath8b §3 final paragraph
of the Lemma crit proof. -/
theorem infinite_witnesses_of_eventual_witness
    {H : List ℕ} {j : ℕ}
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      H.countP (fun h => (n + h).Prime) ≥ j) :
    Set.Infinite { n : ℕ | H.countP (fun h => (n + h).Prime) ≥ j } := by
  -- Unbounded subsets of ℕ are infinite. Given any putative upper bound M,
  -- the eventual-witness hypothesis at N = M + 1 produces an n ≥ M + 1 in
  -- the set, contradicting the bound.
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  rw [Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  obtain ⟨n, hNn, _, hP⟩ := hN₀ (max N₀ (M + 1)) (le_max_left _ _)
  have hMlt : M + 1 ≤ n := (le_max_right N₀ (M + 1)).trans hNn
  have hnLeM : n ≤ M := hM hP
  omega

/-- **"Lemma crit"** (Polymath8b §3 Lemma 3.3): pigeonhole criterion for DHL.

If for every admissible $k$-tuple $\mathcal{H}$ one can find a coprime
residue class $b \pmod{W}$, non-negative weights $\nu$, and positive
quantities $\alpha, \beta_1, \ldots, \beta_k$ with the asymptotic bounds
`alphaBound` (s1) and `betaBound` (s2) holding for arbitrarily large $x$,
satisfying the **key inequality** $\frac{\beta_1 + \cdots + \beta_k}{\alpha} > m$,
then $\DHL[k, m+1]$ holds.

Note: the hypothesis was strengthened in this PR to include the (s1) and
(s2) bounds. Previously the hypothesis was just the key ratio, which made
the theorem trivially false (any constant choice of $\alpha, \beta_i$
satisfies it without implying DHL).

Proof: 3-line composition of `witness_eventually_from_sieve_data` and
`infinite_witnesses_of_eventual_witness`. -/
theorem dhl_criterion (k m : ℕ) (_hk : k ≥ 2) (_hm : m ≥ 1)
    (hSieve : ∀ H : List ℕ, Admissible H → H.length = k →
      ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
        0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
        (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
        (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
            betaBound k ν H b W i.val x (β i))) :
    DHL k (m + 1) := by
  intro H hAdm hLen
  obtain ⟨b, W, ν, α, β, hα, hβ, hKey, hS1, hS2⟩ := hSieve H hAdm hLen
  exact infinite_witnesses_of_eventual_witness
    (witness_eventually_from_sieve_data H hAdm hLen hα hβ hKey hS1 hS2)

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

/-- The Rayleigh-ratio numerator $\sum_i J_i(F)$ of Polymath8b §5, where
$$J_i(F) := \int_{[0,\infty)^{k-1}} \left(\int_0^\infty F(t_1,\dots,t_k)
                                          \, dt_i\right)^2 \, dt_{\setminus i}.$$
Here $t = \mathtt{insertNth}\, i\, t_i\, s$ embeds the $(k-1)$-coordinate
vector $s$ and the singled-out coordinate $t_i$ back into $\mathbb{R}^k$
at position $i$.

Note: the integrand is $F$ itself, *not* a partial derivative — Polymath8b
§5 (Theorem `maynard-thm`, eqns (I), (J_i)). For admissible $F$ supported
on the $k$-simplex, the inner $[0,\infty)$ integral equals the integral
over $[0, 1 - \sum_{j \ne i} t_j]$ (and the outer over $[0,\infty)^{k-1}$
matches the $(k-1)$-simplex), so the simpler simplex-clamped form below is
equivalent in value to the paper formulation.

Pattern-matched on $k$: the $k = 0$ case is vacuous (empty sum); the
$k = n + 1$ case carries the formula above. -/
noncomputable def mkF_numerator : (k : ℕ) → ((Fin k → ℝ) → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, F =>
      ∑ i : Fin (n + 1),
        ∫ s in simplex n,
          (∫ ti in Set.Icc (0 : ℝ) (1 - ∑ j, s j),
              F (i.insertNth ti s)) ^ 2

/-- The individual Maynard marginal $J_i(F)$ from Polymath8b §5 eqn (J_i),
extracted from `mkF_numerator` so it can be referenced as $\beta_i$ in the
sieve-data construction.

For $k = 0$ the type `Fin 0` is empty, so the def is vacuous; for $k = n + 1$
the body matches the $i$-th summand of `mkF_numerator (n+1) F`. -/
noncomputable def J_i : (k : ℕ) → ((Fin k → ℝ) → ℝ) → Fin k → ℝ
  | 0, _, i => i.elim0
  | n + 1, F, i =>
      ∫ s in simplex n,
        (∫ ti in Set.Icc (0 : ℝ) (1 - ∑ j, s j),
            F (i.insertNth ti s)) ^ 2

/-- $J_i(F) \ge 0$: the integrand is a square. -/
theorem J_i_nonneg (k : ℕ) (F : (Fin k → ℝ) → ℝ) (i : Fin k) : 0 ≤ J_i k F i := by
  match k, F, i with
  | 0, _, i => exact i.elim0
  | n + 1, F, i =>
      change 0 ≤ ∫ s in simplex n,
          (∫ ti in Set.Icc (0 : ℝ) (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- The Rayleigh numerator decomposes as $\sum_i J_i(F)$ (Polymath8b §5
between eqns (J_i) and (M_k)). Folds out by `cases k` + `rfl`. -/
theorem mkF_numerator_eq_sum_J_i (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    mkF_numerator k F = ∑ i, J_i k F i := by
  cases k with
  | zero => simp [mkF_numerator]
  | succ n => rfl

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

/-- The admissible set of `MkF k F` values: smooth `F` supported on
the simplex with nonzero Rayleigh denominator. Factored out of `Mk` so
the `sSup` extraction lemma can name it. -/
def MkSet (k : ℕ) : Set ℝ :=
  { v | ∃ F : (Fin k → ℝ) → ℝ,
          ContDiff ℝ ⊤ F ∧
          Function.support F ⊆ simplex k ∧
          mkF_denominator k F > 0 ∧
          v = MkF k F }

/-- $M_k := \sup_F M_k(F)$ over admissible $F$ on the simplex.

Concrete `sSup` over `MkSet k`. Per `Mathlib`'s `ℝ`-`ConditionallyCompleteLinearOrder`
convention, an empty or unbounded admissible set yields `0`; in the
relevant Polymath8b regime ($k \ge 2$) the set is non-empty and bounded —
see axioms `MkSet_nonempty` and `MkSet_bddAbove`. -/
noncomputable def Mk (k : ℕ) : ℝ := sSup (MkSet k)

/-- For $k \ge 2$, the admissible-F set for $M_k$ is non-empty.

Polymath8b §5 implicitly assumes this: any smooth bump supported on the
interior of the simplex with nonzero $\int F^2$ realizes some
$\mathrm{MkF}(k, F) > 0$. Formally proving nonemptiness requires
constructing such an $F$ (smooth-bump construction, several mathlib
imports). Axiomatized at this leaf per the project's "axioms at leaves"
principle; a future PR could replace with a real proof. -/
axiom MkSet_nonempty (k : ℕ) (hk : 2 ≤ k) : (MkSet k).Nonempty

/-- The admissible-F set for $M_k$ is bounded above.

Polymath8b Corollary `mk-upper` (the converse direction to `mlower`):
$M_k \le \frac{k}{k-1} \log k$ for all $k \ge 2$. This implies any
realized value is bounded by $\frac{k}{k-1} \log k$, so the set is
`BddAbove`. Axiomatized; cf. Polymath8b §5 + Hensley-Richards 1973
(which gives the asymptotic). -/
axiom MkSet_bddAbove (k : ℕ) : BddAbove (MkSet k)

/-- $M_k \le 1$ for $k \le 1$. Standard variational bound: for $k = 0$,
$M_0 = 0$ by definition (the numerator `mkF_numerator 0` is identically 0);
for $k = 1$, the Maynard ratio is $(\int F)^2 / \int F^2 \le 1$ by
Cauchy-Schwarz on the unit interval. Axiomatized — the $k = 0$ case is
elementary but the $k = 1$ Cauchy-Schwarz argument requires measure-theoretic
setup not currently in the project. -/
axiom Mk_le_one_of_k_le_one (k : ℕ) (hk : k ≤ 1) : Mk k ≤ 1

/-! ### The ε-enlarged variant (Polymath8b §5, epsilon-trick)

In the GEH-enabled refinement, $F$'s support may extend out to the
$(1+\varepsilon)$-scaled simplex, at the cost of integrating the
numerator's outer integrals only over the $(1-\varepsilon)$-scaled
$(k-1)$-simplex. -/

/-- The $(1+\varepsilon)$-enlarged simplex: $(1+\varepsilon) \cdot R_k$.
Polymath8b §5 (Theorem `epsilon-trick`) support polytope. -/
noncomputable def simplex_eps (k : ℕ) (ε : ℝ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 + ε }

/-- The $(1-\varepsilon)$-shrunken simplex: $(1-\varepsilon) \cdot R_k$.
Used as the outer integration domain in $J_{i, 1-\varepsilon}(F)$. -/
noncomputable def simplex_shrunk (k : ℕ) (ε : ℝ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 - ε }

/-- The Rayleigh-ratio numerator for $M_{k,\varepsilon}$:
$$\sum_i J_{i, 1-\varepsilon}(F) := \sum_i \int_{(1-\varepsilon) R_{k-1}}
  \left(\int_0^\infty F(t)\, dt_i\right)^2 dt_{\setminus i}.$$
(Polymath8b §5 Theorem `epsilon-trick`, eqn just before (J_{i,1-ε}).)

For $F$ supported on $(1+\varepsilon) R_k$, the inner $[0,\infty)$ integral
equals the integral over $[0, 1 + \varepsilon - \sum_{j \ne i} t_j]$; the
clamped form below is equivalent in value to the paper formulation. -/
noncomputable def mkF_eps_numerator : (k : ℕ) → ℝ → ((Fin k → ℝ) → ℝ) → ℝ
  | 0, _, _ => 0
  | n + 1, ε, F =>
      ∑ i : Fin (n + 1),
        ∫ s in simplex_shrunk n ε,
          (∫ ti in Set.Icc (0 : ℝ) (1 + ε - ∑ j, s j),
              F (i.insertNth ti s)) ^ 2

/-- The Rayleigh-ratio denominator $I(F)$ for $M_{k,\varepsilon}$:
$\int_{(1+\varepsilon) R_k} F^2$. -/
noncomputable def mkF_eps_denominator (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in simplex_eps k ε, F t ^ 2

/-- $M_{k,\varepsilon}(F) := \left(\sum_i J_{i,1-\varepsilon}(F)\right) / I(F)$. -/
noncomputable def MkF_eps (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  mkF_eps_numerator k ε F / mkF_eps_denominator k ε F

/-- The admissible set of $\mathrm{MkF}_\varepsilon$ values: smooth $F$
supported on $(1+\varepsilon)\mathcal{R}_k$ with nonzero
$\mathrm{mkF\_eps\_denominator}$. Sister of `MkSet`. -/
def MkSet_eps (k : ℕ) (ε : ℝ) : Set ℝ :=
  { v | ∃ F : (Fin k → ℝ) → ℝ,
          ContDiff ℝ ⊤ F ∧
          Function.support F ⊆ simplex_eps k ε ∧
          mkF_eps_denominator k ε F > 0 ∧
          v = MkF_eps k ε F }

/-- $M_{k, \varepsilon}$: Polymath8b's enlarged-support variant of $M_k$.
Concrete `sSup` over `MkSet_eps k ε`. -/
noncomputable def Mk_eps (k : ℕ) (ε : ℝ) : ℝ := sSup (MkSet_eps k ε)

/-- For $k \ge 2$ and $\varepsilon > 0$, the admissible-F set for
$M_{k,\varepsilon}$ is non-empty. Sister axiom of `MkSet_nonempty`;
the $(1+\varepsilon)$-enlargement only enlarges the admissible support
polytope, so any witness for $M_k$ also witnesses $M_{k,\varepsilon}$. -/
axiom MkSet_eps_nonempty (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    (MkSet_eps k ε).Nonempty

/-- The admissible-F set for $M_{k,\varepsilon}$ is bounded above.
Sister of `MkSet_bddAbove`. Polymath8b §5: $M_{k,\varepsilon}$ admits
the same asymptotic upper bound as $M_k$ up to a factor of
$(1+\varepsilon)/(1-\varepsilon)$. -/
axiom MkSet_eps_bddAbove (k : ℕ) (ε : ℝ) : BddAbove (MkSet_eps k ε)

/-! ### The variational lower bounds → DHL conversions
(Polymath8b §5: Theorems "maynard-thm", "maynard-trunc", "epsilon-trick",
"epsilon-beyond") -/

/-- **sSup extraction**: if $c < M_k$ then there is a specific admissible
$F$ on the simplex realizing $\mathrm{MkF}(k, F) > c$.

Real proof via mathlib's `lt_csSup_iff`, consuming the cited axioms
`MkSet_nonempty` (for $k \ge 2$) and `MkSet_bddAbove` as leaves. -/
theorem exists_F_of_Mk_gt (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : c < Mk k) :
    ∃ F : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ⊤ F ∧ Function.support F ⊆ simplex k ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  have hLt : c < sSup (MkSet k) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_bddAbove k) (MkSet_nonempty k hk)).mp hLt
  obtain ⟨F, hSmooth, hSupp, hDen, hvEq⟩ := hvMem
  exact ⟨F, hSmooth, hSupp, hDen, hvEq ▸ hcv⟩

/-! ### Selberg sieve data sub-lemmas (Polymath8b §3, decomposed)

The analytic core `selberg_sieve_data_from_F` is twig-split into:

1. **`selberg_nu`** — opaque Selberg sieve weight built from $F$, $\mathcal{H}$,
   and a $(b, W)$ residue class (Polymath8b §3 `nuform`, eqn (3.6)–(3.7)).
2. **`wtrick_data`** — cited axiom (Polymath8b §3, standard W-trick): for any
   admissible $\mathcal{H}$ of length $k \ge 1$, there exists a residue class
   $b \pmod{W}$ with $b + h_i$ coprime to $W$ for every $i$.
3. **`s1_holds_from_nonprime_asym`** — cited axiom (Polymath8b §3 Theorem
   `nonprime-asym`, line 889, case (i) "Trivial"): with $\nu$ the Selberg
   weight, the (s1) asymptotic holds with $\alpha = I(F) =
   \int_{\mathcal{R}_k} F^2$ (i.e. `mkF_denominator k F`).
4. **`s2_holds_from_prime_asym_under_EH`** — cited axiom (Polymath8b §3 Theorem
   `prime-asym`, line 862, case (i) EH): same setup, (s2) holds with
   $\beta_i = (\vartheta / 2) \cdot J_i(F)$ for each $i$. The $\vartheta / 2$
   factor encodes the $B^{-k}\,x/W$ vs $B^{1-k}\,x/\phi(W)$ scaling between
   (s1) and (s2) together with the $\vartheta$ from the EH window.

`selberg_sieve_data_from_F` then becomes a real composition: pick $b, W$
from `wtrick_data`, set $\nu := $ `selberg_nu`, set $\alpha := $
`mkF_denominator`, $\beta_i := (\vartheta/2) \cdot J_i(F)$. The key ratio
$\sum_i \beta_i / \alpha = (\vartheta/2) \cdot M_k(F) > (\vartheta/2) \cdot
(2m/\vartheta) = m$ follows by algebra. -/

/-- **Selberg sieve weight from $F$** (Polymath8b §3, eqn (3.6)–(3.7),
`nuform`). The full Polymath8b construction is a finite linear combination of
products of 1D divisor sums against marginals of $F$ — too involved to encode
fully here.

Declared `axiom` (a hidden constant of function type) so the (s1)/(s2) axioms
can reference a fixed $\nu$ choice. A future PR can replace with a real
`noncomputable def`. -/
axiom selberg_nu (k : ℕ) (F : (Fin k → ℝ) → ℝ) (H : List ℕ) (b W : ℕ) :
    ℕ → ℝ

/-- **W-trick** (Polymath8b §3): for any admissible $k$-tuple $\mathcal{H}$
of length $k \ge 1$, there exists a modulus $W \ge 1$ and a residue class
$b \pmod{W}$ with $b + h_i$ coprime to $W$ for each $i$ (the standard
construction takes $W := \prod_{p \le D} p$ for an appropriate threshold $D$
and uses CRT + admissibility to pick $b$).

The conclusion exposes only $W \ge 1$; the coprimality conditions on $(b, W)$
are absorbed into the opaque `selberg_nu` / `alphaBound` / `betaBound`
predicates. Future PR can replace with a real proof using Mertens products
and CRT. -/
axiom wtrick_data {k : ℕ} (_hk : k ≥ 1) {H : List ℕ}
    (_hAdm : Admissible H) (_hLen : H.length = k) :
    ∃ b W : ℕ, 1 ≤ W ∧ b < W

/-- **(s1) from `nonprime-asym` case (i)** (Polymath8b §3 line 889, "Trivial").
For admissible $F$ on the simplex (so $\sum_i S(F_i) + S(G_i) < 1$ is implied
by `Function.support F ⊆ simplex k`), and for any $(b, W)$ from the W-trick,
the (s1) asymptotic holds eventually with $\alpha = I(F) =
\int_{\mathcal{R}_k} F^2$.

Future PR can replace with a real proof from the divisor-sum expansion
(Polymath8b §3 eqns (sfg-1), (lflg)). -/
axiom s1_holds_from_nonprime_asym {k : ℕ} (_hk : k ≥ 2)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex k)
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) :
    ∀ᶠ x : ℝ in Filter.atTop,
      alphaBound k (selberg_nu k F H b W) b W x (mkF_denominator k F)

/-- **(s2) from `prime-asym` case (i)** (Polymath8b §3 line 862, EH version).
Under $\EH[\vartheta]$ with $0 < \vartheta < 1$, and admissible $F$ on the
simplex, the (s2) asymptotic holds eventually with $\beta_i =
(\vartheta/2) \cdot J_i(F)$ for each $i$.

The $\vartheta/2$ factor is the Polymath8b normalization absorbing the ratio
$B^{-k}\,x/W$ vs $B^{1-k}\,x/\phi(W)$ from `nonprime-asym` vs `prime-asym`,
together with the $\vartheta$ from the EH window. Future PR can replace with
a real proof from the divisor-sum expansion (Polymath8b §3 eqn (theta-oo)). -/
axiom s2_holds_from_prime_asym_under_EH {k : ℕ} (_hk : k ≥ 2)
    {ϑ : ℝ} (_hϑ : 0 < ϑ ∧ ϑ < 1) (_hEH : Prerequisites.EH ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex k)
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k F H b W) H b W i.val x (ϑ / 2 * J_i k F i)

/-- **The analytic core of Maynard's theorem** (Polymath8b §3 + §5).
Given an admissible $F$ on the simplex with $\mathrm{MkF}(k, F) > 2m/\vartheta$
under $\EH[\vartheta]$, construct Selberg sieve data $(b, W, \nu,
\alpha, \beta)$ over an admissible $k$-tuple satisfying (s1), (s2),
and the key ratio $\sum_i \beta_i / \alpha > m$.

Real proof — twig-split composition of `wtrick_data`,
`s1_holds_from_nonprime_asym`, `s2_holds_from_prime_asym_under_EH`, plus the
algebraic key step
$(\vartheta/2) \cdot M_k(F) > (\vartheta/2) \cdot (2m/\vartheta) = m$. -/
theorem selberg_sieve_data_from_F {k m : ℕ} (hk : k ≥ 2) (_hm : m ≥ 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ ∧ ϑ < 1) (hEH : Prerequisites.EH ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hF_smooth : ContDiff ℝ ⊤ F)
    (hF_supp : Function.support F ⊆ simplex k)
    (hF_den : mkF_denominator k F > 0)
    (hF_Mk : MkF k F > 2 * m / ϑ)
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hϑ_half_pos : 0 < ϑ / 2 := by linarith
  refine ⟨b, W, selberg_nu k F H b W, mkF_denominator k F,
    fun i => ϑ / 2 * J_i k F i, hF_den, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ β i
    intro i
    exact mul_nonneg hϑ_half_pos.le (J_i_nonneg k F i)
  · -- (∑ i, β i) / α > m
    have hsum : (∑ i, ϑ / 2 * J_i k F i) = ϑ / 2 * mkF_numerator k F := by
      rw [← Finset.mul_sum, ← mkF_numerator_eq_sum_J_i]
    have hratio_eq :
        (∑ i, ϑ / 2 * J_i k F i) / mkF_denominator k F = ϑ / 2 * MkF k F := by
      rw [hsum, mul_div_assoc, ← MkF_eq_rayleigh]
    rw [hratio_eq]
    have step1 : (ϑ / 2) * MkF k F > (ϑ / 2) * (2 * m / ϑ) :=
      mul_lt_mul_of_pos_left hF_Mk hϑ_half_pos
    have step2 : (ϑ / 2) * (2 * (m : ℝ) / ϑ) = m := by
      field_simp
    linarith
  · -- (s1)
    exact s1_holds_from_nonprime_asym hk hF_smooth hF_supp hF_den hAdm hLen b W hW
  · -- (s2)
    intro i
    exact s2_holds_from_prime_asym_under_EH hk hϑ hEH hF_smooth hF_supp hF_den
      hAdm hLen b W hW i

/-- **Theorem 5.2 / "maynard-thm"** (under EH): if $M_k > 2m/\vartheta$ for
some $\vartheta < 1$, and EH[ϑ] holds for that $\vartheta$, then $\DHL[k, m+1]$.

Paper reference: Polymath8b §5 line 935 (`\label{maynard-thm}`).

Proof: 3-step composition. (1) Extract an admissible $F$ with
$\mathrm{MkF}(k, F) > 2m/\vartheta$ via `exists_F_of_Mk_gt`. (2) Apply
`selberg_sieve_data_from_F` to build the per-$H$ sieve data. (3) Feed
into `dhl_criterion`. -/
theorem maynard_thm (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1) (ϑ : ℝ)
    (hϑ : 0 < ϑ ∧ ϑ < 1) (hEH : Prerequisites.EH ϑ)
    (hMk : Mk k > 2 * m / ϑ) : DHL k (m + 1) := by
  apply dhl_criterion k m hk hm
  intro H hAdm hLen
  obtain ⟨F, hSmooth, hSupp, hDen, hMkF⟩ :=
    exists_F_of_Mk_gt k hk (2 * m / ϑ) hMk
  exact selberg_sieve_data_from_F hk hm hϑ hEH hSmooth hSupp hDen hMkF hAdm hLen

/-- **Theorem 5.3 / "maynard-trunc"** (under MPZ): truncated variant suitable
for the Zhang/Polymath8a regime. -/
-- TRIAGE: NEEDS_SIEVE — Polymath8a-flavored variant; truncated weights to
-- handle smooth-moduli regime. Same blocker chain as maynard_thm.
theorem maynard_trunc (k m : ℕ) (ϖ δ : ℝ)
    (_hMPZ : Prerequisites.MPZ ϖ δ) (_hMk : Mk k > 4 * m / (1 / 2 + 2 * ϖ)) :
    DHL k (m + 1) := sorry

/-- **sSup extraction for $M_{k,\varepsilon}$**: if $c < M_{k,\varepsilon}$
then there is a specific admissible $F$ supported on $(1+\varepsilon)
\mathcal{R}_k$ realizing $\mathrm{MkF}_\varepsilon(k, \varepsilon, F) > c$.

Sister of `exists_F_of_Mk_gt`. Same `lt_csSup_iff` discharge, consuming
`MkSet_eps_nonempty` and `MkSet_eps_bddAbove`. -/
theorem exists_F_eps_of_Mk_eps_gt (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : c < Mk_eps k ε) :
    ∃ F : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ⊤ F ∧ Function.support F ⊆ simplex_eps k ε ∧
      mkF_eps_denominator k ε F > 0 ∧ c < MkF_eps k ε F := by
  have hLt : c < sSup (MkSet_eps k ε) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_eps_bddAbove k ε) (MkSet_eps_nonempty k hk ε hε)).mp hLt
  obtain ⟨F, hSmooth, hSupp, hDen, hvEq⟩ := hvMem
  exact ⟨F, hSmooth, hSupp, hDen, hvEq ▸ hcv⟩

/-- **The analytic core of the ε-trick** (Polymath8b §5).

Sister of `selberg_sieve_data_from_F` — same shape, with the
$(1+\varepsilon)$-enlarged support and the $(1-\varepsilon)$-shrunken
$J_{i,1-\varepsilon}$ numerator from `mkF_eps_numerator`.

Paper structure: Polymath8b §5 Theorem `epsilon-trick` (line 997). The
support condition $1 + \varepsilon < 1/\vartheta$ ensures the
$(1+\varepsilon)$-enlargement still fits inside the equidistribution
window $\EH[\vartheta]$ provides; below that line the sieve construction
is the same as `maynard_thm`. -/
-- TRIAGE: HARD_ANALYTIC — Polymath8b §3 + §5. Same level of substance
-- as `selberg_sieve_data_from_F`; consumes `prime-asym` + `nonprime-asym`
-- when further decomposed.
theorem selberg_sieve_data_eps_from_F {k m : ℕ} (_hk : k ≥ 2) (_hm : m ≥ 1)
    {ε ϑ : ℝ} (_hε : 0 < ε) (_hϑ : 0 < ϑ ∧ ϑ < 1)
    (_hEH : Prerequisites.EH ϑ) (_hSupp : 1 + ε < 1 / ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex_eps k ε)
    (_hF_den : mkF_eps_denominator k ε F > 0)
    (_hF_Mk : MkF_eps k ε F > 2 * m / ϑ)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := sorry

/-- **Theorem 5.4 / "epsilon-trick"** (Polymath8b §5 line 997,
`\label{epsilon-trick}`, variant (i) — EH-flavored).

If $0 < \varepsilon$, $0 < \vartheta < 1$, $\EH[\vartheta]$ holds,
$1 + \varepsilon < 1/\vartheta$, and $M_{k,\varepsilon} > 2m/\vartheta$,
then $\DHL[k, m+1]$ holds.

Proof: parallel to `maynard_thm`. (1) Extract an $F$ via
`exists_F_eps_of_Mk_eps_gt`. (2) Build per-$H$ sieve data via
`selberg_sieve_data_eps_from_F`. (3) Feed into `dhl_criterion`.

The GEH-flavored variant (ii) — $\GEH[\vartheta]$ + $\varepsilon < 1/(k-1)$ —
is not encoded here; consumers under GEH go through `epsilon_beyond`. -/
theorem epsilon_trick (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1)
    (ε ϑ : ℝ) (hε : 0 < ε) (hϑ : 0 < ϑ ∧ ϑ < 1)
    (hEH : Prerequisites.EH ϑ) (hSupp : 1 + ε < 1 / ϑ)
    (hMk : Mk_eps k ε > 2 * m / ϑ) : DHL k (m + 1) := by
  apply dhl_criterion k m hk hm
  intro H hAdm hLen
  obtain ⟨F, hSmooth, hSupp', hDen, hMkF⟩ :=
    exists_F_eps_of_Mk_eps_gt k hk ε hε (2 * m / ϑ) hMk
  exact selberg_sieve_data_eps_from_F hk hm hε hϑ hEH hSupp hSmooth hSupp'
    hDen hMkF hAdm hLen

/-- **Theorem 5.5 / "epsilon-beyond"** (under GEH, the strongest variant). -/
-- TRIAGE: NEEDS_SIEVE — strongest variant, uses GEH + Mk_eps. Yields the
-- parity-tight H_1 ≤ 6 under GEH.
theorem epsilon_beyond (k m : ℕ) (ε : ℝ) (ϑ : ℝ)
    (_hGEH : Prerequisites.GEH ϑ) (_hε : 0 < ε)
    (_hMk : Mk_eps k ε > 2 * m / ϑ) : DHL k (m + 1) := sorry

end BoundedGaps.Sieve
