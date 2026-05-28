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
imports).

**Reclassified `axiom → theorem := sorry` 2026-05-26** (ROADMAP Tier 2): a
small-proof-we-haven't-gotten-to is `sorry`'s job. Future PR discharges. -/
theorem MkSet_nonempty (k : ℕ) (hk : 2 ≤ k) : (MkSet k).Nonempty := by
  let _ := hk; sorry

/-- The admissible-F set for $M_k$ is bounded above.

Polymath8b Corollary `mk-upper` (the converse direction to `mlower`):
$M_k \le \frac{k}{k-1} \log k$ for all $k \ge 2$. This implies any
realized value is bounded by $\frac{k}{k-1} \log k$, so the set is
`BddAbove`. cf. Polymath8b §5 + Hensley-Richards 1973 (asymptotic).

**Reclassified `axiom → theorem := sorry` 2026-05-26** (ROADMAP Tier 2). -/
theorem MkSet_bddAbove (k : ℕ) : BddAbove (MkSet k) := by
  let _ := k; sorry

/-- $M_0 = 0$: when $k = 0$, the numerator `mkF_numerator 0 _ = 0` by
pattern-match, so `MkF 0 F = 0 / _ = 0` for every $F$, hence
`MkSet 0 ⊆ {0}` and $M_0 = \sup \mathrm{MkSet}\, 0 = 0$.

(Even if `MkSet 0` is empty in some pathological setup,
`Real.sSup_empty = 0` matches.) -/
theorem Mk_zero_le_one : Mk 0 ≤ 1 := by
  change sSup (MkSet 0) ≤ 1
  have hbd : ∀ v ∈ MkSet 0, v ≤ 1 := by
    rintro v ⟨F, _, _, _, rfl⟩
    change MkF 0 F ≤ 1
    unfold MkF mkF_numerator
    simp
  by_cases hne : (MkSet 0).Nonempty
  · exact csSup_le hne hbd
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]; norm_num

/-- $M_k \le 1$ for $k \le 1$. Standard variational bound: for $k = 0$,
$M_0 = 0$ by definition (the numerator `mkF_numerator 0` is identically 0);
for $k = 1$, the Maynard ratio is $(\int F)^2 / \int F^2 \le 1$ by
Cauchy-Schwarz on $[0, 1]$.

**Discharge status (2026-05-26, ROADMAP Tier 2)**:
- $k = 0$ case: **real** via `Mk_zero_le_one` above (`MkF 0 _ = 0/_ = 0`).
- $k = 1$ case: still `sorry`. The Cauchy-Schwarz step is genuine
  measure-theoretic content. Sketch: for $g(t) := F(\text{fun}\_ => t)$
  supported on $[0,1]$,
  $(\int_0^1 g)^2 \le (\int_0^1 1^2)(\int_0^1 g^2) = \int_0^1 g^2$
  by `MeasureTheory.inner_mul_le_norm_mul_norm` (L²-Cauchy-Schwarz)
  specialised to the indicator of $[0,1]$ against $g$, then unfolding
  the `Fin 0`-volume = 1 simplification on `mkF_numerator 1`. Future PR. -/
theorem Mk_le_one_of_k_le_one (k : ℕ) (hk : k ≤ 1) : Mk k ≤ 1 := by
  interval_cases k
  · exact Mk_zero_le_one
  · -- k = 1: Cauchy-Schwarz on [0,1]. Future PR; see docstring.
    sorry

/-! ### The truncated variant (Polymath8b §5, `maynard-trunc`)

In the MPZ/Polymath8a regime, the Selberg-sieve support is restricted to
each coordinate $t_i \le \alpha$ (in addition to $\sum t_i \le 1$) to handle
the smooth-moduli constraint. The Maynard quantity becomes $M_k^{[\alpha]}$,
the sup of $M_k(F)$ over $F$ supported on the truncated simplex
$\{t \in [0, \alpha]^k : \sum_i t_i \le 1\}$. -/

/-- The truncated simplex: $\{t \in [0, \alpha]^k : \sum_i t_i \le 1\}$.
Polymath8b §5 Theorem `maynard-trunc` support polytope (line 961). -/
noncomputable def simplex_truncated (k : ℕ) (α : ℝ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ (∀ i, t i ≤ α) ∧ ∑ i, t i ≤ 1 }

/-- The admissible set of $\mathrm{MkF}(k, F)$ values for $F$ supported on the
**truncated** simplex. Sister of `MkSet`; same Rayleigh ratio, restricted
support polytope. -/
def MkSet_truncated (k : ℕ) (α : ℝ) : Set ℝ :=
  { v | ∃ F : (Fin k → ℝ) → ℝ,
          ContDiff ℝ ⊤ F ∧
          Function.support F ⊆ simplex_truncated k α ∧
          mkF_denominator k F > 0 ∧
          v = MkF k F }

/-- $M_k^{[\alpha]} := \sup_F M_k(F)$ over admissible $F$ on the truncated
simplex. Polymath8b §5 `maynard-trunc` (line 959). Concrete `sSup` over
`MkSet_truncated k α`; sister of `Mk`. -/
noncomputable def Mk_truncated (k : ℕ) (α : ℝ) : ℝ := sSup (MkSet_truncated k α)

/-- For $k \ge 2$ and $\alpha > 0$, the admissible-F set for $M_k^{[\alpha]}$
is non-empty. Sister of `MkSet_nonempty`; smooth-bump construction inside
the (sufficiently small) truncated simplex provides a witness.

**Reclassified `axiom → theorem := sorry` 2026-05-26** (ROADMAP Tier 2). -/
theorem MkSet_truncated_nonempty (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 0 < α) :
    (MkSet_truncated k α).Nonempty := by
  let _ := hk; let _ := hα; sorry

/-- The admissible-F set for $M_k^{[\alpha]}$ is bounded above. Sister of
`MkSet_bddAbove`; since `simplex_truncated k α ⊆ simplex k`, every witness
$F$ for `MkSet_truncated k α` is also a witness for `MkSet k` with the
same value, so `MkSet_truncated k α ⊆ MkSet k` and the bound is inherited.

**Discharged 2026-05-26** (ROADMAP Tier 2): real local proof routing
through `MkSet_bddAbove` (which is still a sorry — the substantive
Polymath8b Cor `mk-upper` bound — but transitive sorries don't count
against this theorem's body). -/
theorem MkSet_truncated_bddAbove (k : ℕ) (α : ℝ) : BddAbove (MkSet_truncated k α) := by
  refine (MkSet_bddAbove k).mono ?_
  rintro v ⟨F, hSmooth, hSupp, hDen, rfl⟩
  refine ⟨F, hSmooth, ?_, hDen, rfl⟩
  intro t ht
  obtain ⟨h_nonneg, _h_lealpha, h_sumle⟩ := hSupp ht
  exact ⟨h_nonneg, h_sumle⟩

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

/-- The individual Maynard marginal $J_{i,1-\varepsilon}(F)$ from Polymath8b
§5 Theorem `epsilon-trick`, extracted from `mkF_eps_numerator` so it can be
referenced as $\beta_i$ in the $\varepsilon$-flavored sieve-data construction.

Sister of `J_i`; outer integration over `simplex_shrunk n ε`, inner over
$[0, 1 + \varepsilon - \sum_{j \ne i} t_j]$. -/
noncomputable def J_i_eps : (k : ℕ) → ℝ → ((Fin k → ℝ) → ℝ) → Fin k → ℝ
  | 0, _, _, i => i.elim0
  | n + 1, ε, F, i =>
      ∫ s in simplex_shrunk n ε,
        (∫ ti in Set.Icc (0 : ℝ) (1 + ε - ∑ j, s j),
            F (i.insertNth ti s)) ^ 2

/-- $J_{i,1-\varepsilon}(F) \ge 0$: the integrand is a square. -/
theorem J_i_eps_nonneg (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) (i : Fin k) :
    0 ≤ J_i_eps k ε F i := by
  match k, ε, F, i with
  | 0, _, _, i => exact i.elim0
  | n + 1, ε, F, i =>
      change 0 ≤ ∫ s in simplex_shrunk n ε,
          (∫ ti in Set.Icc (0 : ℝ) (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- The ε-flavored Rayleigh numerator decomposes as $\sum_i J_{i,1-\varepsilon}(F)$
(Polymath8b §5 Theorem `epsilon-trick`, between the J_{i,1-ε} defs and M_{k,ε}). -/
theorem mkF_eps_numerator_eq_sum_J_i_eps (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) :
    mkF_eps_numerator k ε F = ∑ i, J_i_eps k ε F i := by
  cases k with
  | zero => simp [mkF_eps_numerator]
  | succ n => rfl

/-- The Rayleigh-ratio denominator $I(F)$ for $M_{k,\varepsilon}$:
$\int_{(1+\varepsilon) R_k} F^2$. -/
noncomputable def mkF_eps_denominator (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in simplex_eps k ε, F t ^ 2

/-- $M_{k,\varepsilon}(F) := \left(\sum_i J_{i,1-\varepsilon}(F)\right) / I(F)$. -/
noncomputable def MkF_eps (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  mkF_eps_numerator k ε F / mkF_eps_denominator k ε F

/-- **Polymath8b §5 definition of $M_{k,\varepsilon}(F)$**: the ε-flavored
Maynard quantity is the Rayleigh ratio $\left(\sum_i J_{i,1-\varepsilon}(F)
\right) / I(F)$. `rfl`-discharged sister of `MkF_eq_rayleigh`. -/
theorem MkF_eps_eq_rayleigh (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) :
    MkF_eps k ε F = mkF_eps_numerator k ε F / mkF_eps_denominator k ε F := rfl

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

/-- The standard simplex is closed in `Fin k → ℝ`. Helper for compactness. -/
private theorem simplex_isClosed (k : ℕ) : IsClosed (simplex k) := by
  have h_eq : simplex k =
      (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ 1} := by
    unfold simplex
    ext t
    simp [Set.mem_iInter]
  rw [h_eq]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
  · have h_cont : Continuous (fun (t : Fin k → ℝ) => ∑ i, t i) :=
      continuous_finset_sum Finset.univ (fun i _ => continuous_apply i)
    exact isClosed_Iic.preimage h_cont

/-- The standard simplex is contained in $[0, 1]^k$, hence bounded.
Combined with `simplex_isClosed`, this gives compactness. -/
private theorem simplex_isCompact (k : ℕ) : IsCompact (simplex k) := by
  apply IsCompact.of_isClosed_subset
    (s := Set.pi Set.univ (fun (_ : Fin k) => Set.Icc (0 : ℝ) 1))
  · exact isCompact_univ_pi (fun _ => isCompact_Icc)
  · exact simplex_isClosed k
  · rintro t ⟨h_nn, h_sum⟩ i _
    refine ⟨h_nn i, ?_⟩
    -- t i ≤ ∑ j, t j ≤ 1
    have h_sum_ge : t i ≤ ∑ j, t j :=
      Finset.single_le_sum (f := t) (s := Finset.univ)
        (fun j _ => h_nn j) (Finset.mem_univ i)
    linarith

/-- For $k \ge 2$ and $\varepsilon > 0$, the admissible-F set for
$M_{k,\varepsilon}$ is non-empty. Sister of `MkSet_nonempty`;
the $(1+\varepsilon)$-enlargement only enlarges the admissible support
polytope, so an `MkSet_nonempty` witness $F$ (supported on `simplex k
⊆ simplex_eps k ε`) is also a valid F for `MkSet_eps`.

**Discharged 2026-05-27** (ROADMAP Tier 2): real local proof routing
through `MkSet_nonempty`. Key step: `mkF_eps_denominator k ε F ≥
mkF_denominator k F > 0` via `setIntegral_mono_set`. Integrability of
$F^2$ comes from $F$ continuous (`ContDiff ⊤ → Continuous`) + $F$ has
compact support (since `support F ⊆ simplex k` and `simplex k` is
compact by `simplex_isCompact`). -/
theorem MkSet_eps_nonempty (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    (MkSet_eps k ε).Nonempty := by
  obtain ⟨_v, F, hSmooth, hSupp, hDen, _hvEq⟩ := MkSet_nonempty k hk
  refine ⟨MkF_eps k ε F, F, hSmooth, ?_, ?_, rfl⟩
  -- (1) support widening: simplex k ⊆ simplex_eps k ε
  · have hSubset : simplex k ⊆ simplex_eps k ε := fun t ⟨h_nn, h_sum⟩ =>
      ⟨h_nn, h_sum.trans (by linarith)⟩
    exact hSupp.trans hSubset
  -- (2) eps-denom positivity via setIntegral_mono_set
  · have hSubset : simplex k ⊆ simplex_eps k ε := fun t ⟨h_nn, h_sum⟩ =>
      ⟨h_nn, h_sum.trans (by linarith)⟩
    have hF_cont : Continuous F := hSmooth.continuous
    have hF2_cont : Continuous (fun t => F t ^ 2) := hF_cont.pow 2
    have hSupp_compact : HasCompactSupport F :=
      HasCompactSupport.of_support_subset_isCompact (simplex_isCompact k) hSupp
    have hSupp2_compact : HasCompactSupport (fun t => F t ^ 2) :=
      hSupp_compact.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    have hF2_int : MeasureTheory.Integrable (fun t => F t ^ 2) MeasureTheory.volume :=
      hF2_cont.integrable_of_hasCompactSupport hSupp2_compact
    have hF2_intOn : MeasureTheory.IntegrableOn (fun t => F t ^ 2) (simplex_eps k ε)
        MeasureTheory.volume := hF2_int.integrableOn
    have hMono : mkF_denominator k F ≤ mkF_eps_denominator k ε F := by
      unfold mkF_denominator mkF_eps_denominator
      exact MeasureTheory.setIntegral_mono_set hF2_intOn
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hSubset)
    linarith

/-- The admissible-F set for $M_{k,\varepsilon}$ is bounded above.
Sister of `MkSet_bddAbove`. Polymath8b §5: $M_{k,\varepsilon}$ admits
the same asymptotic upper bound as $M_k$ up to a factor of
$(1+\varepsilon)/(1-\varepsilon)$.

**Reclassified `axiom → theorem := sorry` 2026-05-26** (ROADMAP Tier 2). -/
theorem MkSet_eps_bddAbove (k : ℕ) (ε : ℝ) : BddAbove (MkSet_eps k ε) := by
  let _ := k; let _ := ε; sorry

/-! ### The epsilon-beyond enlargement (Polymath8b §5, Theorem `epsilon-beyond`)

In the GEH refinement, $F$'s support may extend further to the
$\frac{k}{k-1}$-scaled simplex, provided $F$ satisfies the vanishing
marginal condition (eqn 1029) that kills its $i$-th 1-D integral on the
region where the remaining coordinates exceed $1 + \varepsilon$.

Unlike `epsilon-trick`, there is no Rayleigh-sup `Mk_beyond`; the
theorem takes an explicit $F$ witness with the marginal condition baked in.
Three new pieces vs `epsilon-trick`:

1. `simplex_scaled k r` — the generic $r$-scaled simplex.
2. `HasVanishingMarginal k ε F` — the eqn (1029) predicate.
3. `J_i_beyond k ε F i` — third marginal def: outer over $(1-\varepsilon)
   R_{k-1}$ (same as `J_i_eps`), inner integral over **$[0, \infty)$**
   rather than the clamped $[0, 1+\varepsilon - \sum]$ used in `J_i_eps`.
   For $F$ supported on $\frac{k}{k-1} R_k$ (paper's epsilon-beyond
   polytope), only the unclamped form matches the paper. -/

/-- The generic $r$-scaled simplex $r \cdot \mathcal{R}_k$:
$\{t \in [0, \infty)^k : \sum t_i \le r\}$. Specialises to `simplex`
($r = 1$), `simplex_eps` ($r = 1 + \varepsilon$), and `simplex_shrunk`
($r = 1 - \varepsilon$) but kept distinct to avoid disturbing earlier
defs and to support Polymath8b §5 epsilon-beyond's $r = k/(k-1)$. -/
noncomputable def simplex_scaled (k : ℕ) (r : ℝ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ r }

/-- **Vanishing marginal condition** (Polymath8b §5 eqn `vanishing-marginal`,
1029-1037). For $i = 1, \ldots, k$, the $i$-th 1-D integral of $F$ along
$[0, \infty)$ vanishes whenever the remaining coordinates sum to more than
$1 + \varepsilon$:
$$\int_0^\infty F(t_1, \ldots, t_k)\, dt_i = 0 \quad\text{when}\quad
  \sum_{j \ne i} t_j > 1 + \varepsilon.$$

This is the key hypothesis of `epsilon-beyond`: it lets us enlarge $F$'s
support polytope from $(1 + \varepsilon) R_k$ (used in `epsilon-trick`) to
the larger $\frac{k}{k-1} R_k$, while keeping the Rayleigh ratio's
numerator finite (the marginal-vanishing forces the inner integrand to
zero on the part of the enlarged polytope outside $(1 + \varepsilon) R_k$). -/
def HasVanishingMarginal : (k : ℕ) → ℝ → ((Fin k → ℝ) → ℝ) → Prop
  | 0, _, _ => True
  | n + 1, ε, F =>
      ∀ i : Fin (n + 1), ∀ s : Fin n → ℝ,
        (∀ j, 0 ≤ s j) → (∑ j, s j > 1 + ε) →
        ∫ ti in Set.Ici (0 : ℝ), F (i.insertNth ti s) = 0

/-- The individual Maynard marginal $J_{i, 1-\varepsilon}(F)$ as it
appears in Polymath8b §5 Theorem `epsilon-beyond`: outer integration over
the $(1-\varepsilon)$-shrunk $(k-1)$-simplex, **inner integration over
$[0, \infty)$ (unclamped)**.

Sister of `J_i_eps`. The difference: `J_i_eps` clamps the inner integral
to $[0, 1 + \varepsilon - \sum_{j \ne i} t_j]$, which equals the paper's
$[0, \infty)$ form precisely when $F$ is supported on
$(1 + \varepsilon) \mathcal{R}_k$. For `epsilon-beyond` $F$ is supported
on the larger $\frac{k}{k-1} \mathcal{R}_k$, so the clamped form would
**undercount**; the unclamped form here is the correct one.

When `HasVanishingMarginal k ε F` holds, the inner integrand
$\int_0^\infty F(t_1, \ldots, t_k)\, dt_i$ is automatically zero on the
part of the outer domain where $\sum_{j \ne i} t_j > 1 + \varepsilon$, so
the value depends only on the $(1-\varepsilon)$-shrunk piece even though
the inner domain is the full $[0, \infty)$. -/
noncomputable def J_i_beyond : (k : ℕ) → ℝ → ((Fin k → ℝ) → ℝ) → Fin k → ℝ
  | 0, _, _, i => i.elim0
  | n + 1, ε, F, i =>
      ∫ s in simplex_shrunk n ε,
        (∫ ti in Set.Ici (0 : ℝ), F (i.insertNth ti s)) ^ 2

/-- $J_{i, 1-\varepsilon}(F) \ge 0$ — integrand is a square. -/
theorem J_i_beyond_nonneg (k : ℕ) (ε : ℝ) (F : (Fin k → ℝ) → ℝ) (i : Fin k) :
    0 ≤ J_i_beyond k ε F i := by
  match k, ε, F, i with
  | 0, _, _, i => exact i.elim0
  | n + 1, ε, F, i =>
      change 0 ≤ ∫ s in simplex_shrunk n ε,
          (∫ ti in Set.Ici (0 : ℝ), F (i.insertNth ti s)) ^ 2
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- The Rayleigh-ratio denominator $I(F) = \int F^2$ for `epsilon-beyond`,
restricted to $F$'s support polytope $\frac{k}{k-1} \mathcal{R}_k$.
(Equivalent to $\int_{[0,\infty)^k} F^2$ when $F$ has the stated support.) -/
noncomputable def mkF_beyond_denominator (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)), F t ^ 2

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

/-- **sSup extraction for $M_k^{[\alpha]}$** (truncated variant): if
$c < M_k^{[\alpha]}$ then there is a specific admissible $F$ supported on
the truncated simplex $\{t \in [0,\alpha]^k : \sum_i t_i \le 1\}$ realizing
$\mathrm{MkF}(k, F) > c$.

Sister of `exists_F_of_Mk_gt`, same `lt_csSup_iff` discharge consuming
`MkSet_truncated_nonempty` (for $k \ge 2$, $\alpha > 0$) and
`MkSet_truncated_bddAbove` as leaves. -/
theorem exists_F_truncated_of_Mk_truncated_gt (k : ℕ) (hk : 2 ≤ k)
    (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : c < Mk_truncated k α) :
    ∃ F : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ⊤ F ∧ Function.support F ⊆ simplex_truncated k α ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  have hLt : c < sSup (MkSet_truncated k α) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_truncated_bddAbove k α)
      (MkSet_truncated_nonempty k hk α hα)).mp hLt
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
`nuform`): $\nu(n) = \left(\sum_j c_j \prod_i \lambda_{F_{j,i}}(n + h_i)
\right)^2$ — a finite linear combination of products of 1D divisor sums
against marginals of $F$.

Declared `opaque` (a hidden constant of function type, sister of
`alphaBound`/`betaBound`) because the nuform IS a real construction; the
project just hasn't encoded the full multidimensional Selberg machinery
yet. A future PR can supply a real `noncomputable def` body. Project
convention: `opaque` for leaves with real-but-unencoded definitions,
`axiom` for leaves citing external truths. -/
opaque selberg_nu (k : ℕ) (F : (Fin k → ℝ) → ℝ) (H : List ℕ) (b W : ℕ) :
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

/-- **(s2) from `prime-asym` case (ii)** (Polymath8b §3, MPZ smooth-moduli
window). Under $\MPZ[\varpi, \delta]$ with $0 < 1/4 + \varpi$, and $F$
supported on the truncated simplex $\{t \in [0, \delta/(1/4+\varpi)]^k :
\sum_i t_i \le 1\}$, the (s2) asymptotic holds eventually with
$\beta_i = (1/4 + \varpi) \cdot J_i(F)$ for each $i$.

This is the MPZ analog of `s2_holds_from_prime_asym_under_EH`: the effective
EH level is $\vartheta := 1/2 + 2\varpi$, the $\vartheta/2$ factor becomes
$1/4 + \varpi$, and the smooth-moduli restriction is encoded by F's
per-coordinate truncation at $\delta/(1/4+\varpi)$.

Future PR can replace with a real proof from Polymath8a's smooth-modulus
prime-asym estimate (Polymath8a Theorem 2.17 plus the divisor-sum
expansion of Polymath8b §3 eqn (theta-oo)). -/
axiom s2_holds_from_prime_asym_under_MPZ {k : ℕ} (_hk : k ≥ 2)
    {ϖ δ : ℝ} (_hϖ : 0 < 1/4 + ϖ) (_hMPZ : Prerequisites.MPZ ϖ δ)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex_truncated k (δ / (1/4 + ϖ)))
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k F H b W) H b W i.val x ((1/4 + ϖ) * J_i k F i)

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

/-- **Analytic core of Maynard's truncated theorem** (Polymath8b §3 + §5,
MPZ flavor). Sister of `selberg_sieve_data_from_F`.

Given an admissible $F$ on the **truncated** simplex $\{t \in [0,
\delta/(1/4+\varpi)]^k : \sum_i t_i \le 1\}$ with $\mathrm{MkF}(k, F) >
m/(1/4+\varpi)$, under $\MPZ[\varpi, \delta]$ with $0 < 1/4 + \varpi$,
construct Selberg sieve data $(b, W, \nu, \alpha, \beta)$ over an
admissible $k$-tuple satisfying (s1), (s2), and the key ratio
$\sum_i \beta_i / \alpha > m$.

Real proof — twig-split composition of `wtrick_data`,
`s1_holds_from_nonprime_asym` (reused; truncated-supp ⊂ simplex-supp),
`s2_holds_from_prime_asym_under_MPZ` (new MPZ analog), plus the algebraic
key step $(1/4 + \varpi) \cdot M_k(F) > (1/4 + \varpi) \cdot
(m/(1/4+\varpi)) = m$.

Mirrors PR-A5 / `selberg_sieve_data_from_F` with the substitution
$\vartheta/2 \mapsto 1/4 + \varpi$ (effective theta = $1/2 + 2\varpi$
from the MPZ window). -/
theorem selberg_sieve_data_truncated_from_F {k m : ℕ} (hk : k ≥ 2) (_hm : m ≥ 1)
    {ϖ δ : ℝ} (hϖ : 0 < 1/4 + ϖ) (hMPZ : Prerequisites.MPZ ϖ δ)
    {F : (Fin k → ℝ) → ℝ}
    (hF_smooth : ContDiff ℝ ⊤ F)
    (hF_supp : Function.support F ⊆ simplex_truncated k (δ / (1/4 + ϖ)))
    (hF_den : mkF_denominator k F > 0)
    (hF_Mk : MkF k F > m / (1/4 + ϖ))
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  -- Coerce F's support from truncated simplex into the full simplex; the
  -- per-coordinate constraint t_i ≤ α is stricter than the open simplex.
  have hF_supp_simplex : Function.support F ⊆ simplex k := by
    intro t ht
    obtain ⟨h_nonneg, _h_lealpha, h_sumle⟩ := hF_supp ht
    exact ⟨h_nonneg, h_sumle⟩
  refine ⟨b, W, selberg_nu k F H b W, mkF_denominator k F,
    fun i => (1/4 + ϖ) * J_i k F i, hF_den, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ β i
    intro i
    exact mul_nonneg hϖ.le (J_i_nonneg k F i)
  · -- (∑ i, β i) / α > m
    have hsum : (∑ i, (1/4 + ϖ) * J_i k F i) = (1/4 + ϖ) * mkF_numerator k F := by
      rw [← Finset.mul_sum, ← mkF_numerator_eq_sum_J_i]
    have hratio_eq :
        (∑ i, (1/4 + ϖ) * J_i k F i) / mkF_denominator k F = (1/4 + ϖ) * MkF k F := by
      rw [hsum, mul_div_assoc, ← MkF_eq_rayleigh]
    rw [hratio_eq]
    have step1 : (1/4 + ϖ) * MkF k F > (1/4 + ϖ) * ((m : ℝ) / (1/4 + ϖ)) :=
      mul_lt_mul_of_pos_left hF_Mk hϖ
    have hne : (1/4 + ϖ : ℝ) ≠ 0 := ne_of_gt hϖ
    have step2 : (1/4 + ϖ) * ((m : ℝ) / (1/4 + ϖ)) = m := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
    linarith
  · -- (s1): reuse the non-truncated axiom; truncated F's support sits inside
    -- the full simplex by the coercion above.
    exact s1_holds_from_nonprime_asym hk hF_smooth hF_supp_simplex hF_den hAdm hLen b W hW
  · -- (s2) MPZ version
    intro i
    exact s2_holds_from_prime_asym_under_MPZ hk hϖ hMPZ hF_smooth hF_supp hF_den
      hAdm hLen b W hW i

/-- **Theorem 5.3 / "maynard-trunc"** (under MPZ): truncated variant suitable
for the Zhang/Polymath8a regime.

Paper reference: Polymath8b §5 line 957–966 (`\label{maynard-trunc}`):
$$\text{If } M_k^{[\delta/(1/4+\varpi)]} > \frac{m}{1/4+\varpi} \text{ then } \DHL[k,m+1].$$

Previously stated with `Mk k > 4m/(1/2+2ϖ)` (unrestricted simplex + 2× higher
threshold), which had two distinct paper-faithfulness bugs (fixed in
PR-A1b-i):
- `Mk` not `Mk_truncated` — paper sup is over truncated simplex, not the
  full one. `Mk ≥ Mk_truncated` so the unrestricted-Mk hypothesis is
  *weaker* (can hold without the true paper hypothesis).
- 2× threshold: `4m/(1/2+2ϖ) = 2m/(1/4+ϖ)`, paper has `m/(1/4+ϖ)`.

**Discharged 2026-05-27** (PR-A1b-iii): real composition through
`exists_F_truncated_of_Mk_truncated_gt`, `selberg_sieve_data_truncated_from_F`,
`dhl_criterion`. Mirrors `maynard_thm`'s body modulo the truncated-simplex
extraction and the MPZ flavor.

Signature requires `0 < 1/4 + \varpi` and `0 < \delta` (paper-faithful;
Polymath8b §5 line 957 has $0 < \varpi < 1/4$, $0 < \delta < 1/4 + \varpi$).
The 4 truncated-Mk witness axioms in `Polymath8b.lean` were updated to
expose these positivity components. -/
theorem maynard_trunc (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1) (ϖ δ : ℝ)
    (hϖ : 0 < 1/4 + ϖ) (hδ : 0 < δ) (hMPZ : Prerequisites.MPZ ϖ δ)
    (hMk : Mk_truncated k (δ / (1/4 + ϖ)) > m / (1/4 + ϖ)) :
    DHL k (m + 1) := by
  apply dhl_criterion k m hk hm
  intro H hAdm hLen
  have hα_pos : 0 < δ / (1/4 + ϖ) := div_pos hδ hϖ
  obtain ⟨F, hSmooth, hSupp, hDen, hMkF⟩ :=
    exists_F_truncated_of_Mk_truncated_gt k hk (δ / (1/4 + ϖ)) hα_pos
      (m / (1/4 + ϖ)) hMk
  exact selberg_sieve_data_truncated_from_F hk hm hϖ hMPZ hSmooth hSupp hDen
    hMkF hAdm hLen

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

/-! ### Selberg sieve data sub-lemmas (ε-flavored, Polymath8b §5 `epsilon-trick`)

ε sister of the non-ε decomposition above. Reuses `selberg_nu` and
`wtrick_data` (both ε-agnostic) and adds two ε-specific (s1)/(s2) cited
axioms. -/

/-- **(s1ε) from `nonprime-asym` case (i)** (Polymath8b §3 line 889, applied
through the §5 `epsilon-trick` reduction).

For admissible $F$ on the $(1+\varepsilon)$-enlarged simplex, (s1) holds
eventually with $\alpha = I(F) = \int_{(1+\varepsilon)\mathcal{R}_k} F^2$
(i.e. `mkF_eps_denominator k ε F`).

The constraint $1 + \varepsilon < 1/\vartheta$ does NOT enter here — it is
needed only for (s2) via the prime-asym window. Future PR can replace with
a real proof from the divisor-sum expansion. -/
axiom s1_eps_holds_from_nonprime_asym {k : ℕ} (_hk : k ≥ 2)
    {ε : ℝ} (_hε : 0 < ε)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex_eps k ε)
    (_hF_den : mkF_eps_denominator k ε F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) :
    ∀ᶠ x : ℝ in Filter.atTop,
      alphaBound k (selberg_nu k F H b W) b W x (mkF_eps_denominator k ε F)

/-- **(s2ε) from `prime-asym` case (i) under EH[ϑ]** (Polymath8b §3 line 862
+ §5 `epsilon-trick` reduction).

Under $\EH[\vartheta]$ and the support-fitting condition $1 + \varepsilon <
1/\vartheta$, (s2) holds eventually with $\beta_i = (\vartheta/2) \cdot
J_{i,1-\varepsilon}(F)$. The $(1-\varepsilon)$-shrunken outer integration in
the numerator is what lets prime-asym case (i)'s support bound be satisfied
even with the $(1+\varepsilon)$-enlarged $F$. Future PR can replace with a
real proof. -/
axiom s2_eps_holds_from_prime_asym_under_EH {k : ℕ} (_hk : k ≥ 2)
    {ε ϑ : ℝ} (_hε : 0 < ε) (_hϑ : 0 < ϑ ∧ ϑ < 1)
    (_hEH : Prerequisites.EH ϑ) (_hSupp : 1 + ε < 1 / ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (_hF_smooth : ContDiff ℝ ⊤ F)
    (_hF_supp : Function.support F ⊆ simplex_eps k ε)
    (_hF_den : mkF_eps_denominator k ε F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k F H b W) H b W i.val x
        (ϑ / 2 * J_i_eps k ε F i)

/-- **The analytic core of the ε-trick** (Polymath8b §5).

Sister of `selberg_sieve_data_from_F` — same shape, with the
$(1+\varepsilon)$-enlarged support and the $(1-\varepsilon)$-shrunken
$J_{i,1-\varepsilon}$ numerator from `mkF_eps_numerator`.

Paper structure: Polymath8b §5 Theorem `epsilon-trick` (line 997). The
support condition $1 + \varepsilon < 1/\vartheta$ ensures the
$(1+\varepsilon)$-enlargement still fits inside the equidistribution
window $\EH[\vartheta]$ provides; below that line the sieve construction
is the same as `maynard_thm`.

Real proof — mirror of `selberg_sieve_data_from_F` (PR-A5). Uses
`wtrick_data` + `s1_eps_holds_from_nonprime_asym` + `s2_eps_holds_from_prime_asym_under_EH`
+ the algebraic key step $(\vartheta/2) \cdot M_{k,\varepsilon}(F)
> (\vartheta/2) \cdot (2m/\vartheta) = m$. -/
theorem selberg_sieve_data_eps_from_F {k m : ℕ} (hk : k ≥ 2) (_hm : m ≥ 1)
    {ε ϑ : ℝ} (hε : 0 < ε) (hϑ : 0 < ϑ ∧ ϑ < 1)
    (hEH : Prerequisites.EH ϑ) (hSupp : 1 + ε < 1 / ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hF_smooth : ContDiff ℝ ⊤ F)
    (hF_supp : Function.support F ⊆ simplex_eps k ε)
    (hF_den : mkF_eps_denominator k ε F > 0)
    (hF_Mk : MkF_eps k ε F > 2 * m / ϑ)
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hϑ_half_pos : 0 < ϑ / 2 := by linarith
  refine ⟨b, W, selberg_nu k F H b W, mkF_eps_denominator k ε F,
    fun i => ϑ / 2 * J_i_eps k ε F i, hF_den, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ β i
    intro i
    exact mul_nonneg hϑ_half_pos.le (J_i_eps_nonneg k ε F i)
  · -- (∑ i, β i) / α > m
    have hsum : (∑ i, ϑ / 2 * J_i_eps k ε F i) =
        ϑ / 2 * mkF_eps_numerator k ε F := by
      rw [← Finset.mul_sum, ← mkF_eps_numerator_eq_sum_J_i_eps]
    have hratio_eq :
        (∑ i, ϑ / 2 * J_i_eps k ε F i) / mkF_eps_denominator k ε F
          = ϑ / 2 * MkF_eps k ε F := by
      rw [hsum, mul_div_assoc, ← MkF_eps_eq_rayleigh]
    rw [hratio_eq]
    have step1 : (ϑ / 2) * MkF_eps k ε F > (ϑ / 2) * (2 * m / ϑ) :=
      mul_lt_mul_of_pos_left hF_Mk hϑ_half_pos
    have step2 : (ϑ / 2) * (2 * (m : ℝ) / ϑ) = m := by
      field_simp
    linarith
  · -- (s1ε)
    exact s1_eps_holds_from_nonprime_asym hk hε hF_smooth hF_supp hF_den
      hAdm hLen b W hW
  · -- (s2ε)
    intro i
    exact s2_eps_holds_from_prime_asym_under_EH hk hε hϑ hEH hSupp
      hF_smooth hF_supp hF_den hAdm hLen b W hW i

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

/-- **Theorem 5.5 / "epsilon-beyond"** (Polymath8b §5, line 1028-1037 of
`papers/src/polymath8b-1407.4897/newergap-submitted.tex`,
`\label{epsilon-beyond}`).

Let $k \ge 2$, $m \ge 1$, $0 < \vartheta < 1$ with $\GEH[\vartheta]$, and
$0 < \varepsilon < \frac{1}{k-1}$. Suppose $F : [0,\infty)^k \to \mathbb{R}$
is non-zero square-integrable (here: $C^\infty$ for compatibility with the
sieve scaffolding), supported in $\frac{k}{k-1} \mathcal{R}_k$, and
satisfies the **vanishing marginal condition**:
$\int_0^\infty F(t_1, \ldots, t_k)\, dt_i = 0$ whenever $\sum_{j \ne i}
t_j > 1 + \varepsilon$. If
$\frac{\sum_i J_{i, 1-\varepsilon}(F)}{I(F)} > \frac{2m}{\vartheta}$,
then $\DHL[k, m+1]$ holds.

**Statement-fix history.** PR-A1b-ii (this PR): restated to match the paper
TeX. Previous signature used `Mk_eps k ε > 2m/ϑ` as a Rayleigh-sup
threshold, which is the wrong shape entirely — `epsilon-beyond` has no
Rayleigh-sup (would need a `MkSet_beyond` with vanishing-marginal baked
in). The paper takes an explicit $F$ with the marginal condition. The
inner integral in $J_{i, 1-\varepsilon}$ runs over $[0, \infty)$ (unclamped),
not the $[0, 1+\varepsilon - \sum]$ used in `J_i_eps`'s clamped form,
because `epsilon-beyond` enlarges the support polytope from
$(1 + \varepsilon) \mathcal{R}_k$ to $\frac{k}{k-1} \mathcal{R}_k$
(strictly larger when $\varepsilon < \frac{1}{k-1}$).

**Body still a `sorry`.** Discharge sketch (PR-A1b-iii sister): build a
`selberg_sieve_data_beyond_from_F` analytic-core lemma — same template as
`selberg_sieve_data_from_F` / `_eps_from_F` (PRs #34, #35), but with
$(b, W, \nu)$ tuned for GEH instead of EH and the vanishing-marginal
condition routed through the W-trick. Then feed into `dhl_criterion`. -/
-- TRIAGE: NEEDS_SIEVE — strongest variant, GEH + explicit F + vanishing
-- marginal. Yields the parity-tight $H_1 \le 6$ under GEH.
theorem epsilon_beyond (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1)
    (ε ϑ : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / ((k : ℝ) - 1))
    (hϑ : 0 < ϑ ∧ ϑ < 1) (_hGEH : Prerequisites.GEH ϑ)
    (F : (Fin k → ℝ) → ℝ)
    (_hSmooth : ContDiff ℝ ⊤ F)
    (_hSupp : Function.support F ⊆ simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)))
    (_hVanish : HasVanishingMarginal k ε F)
    (_hDen : mkF_beyond_denominator k F > 0)
    (_hThresh :
      (∑ i, J_i_beyond k ε F i) / mkF_beyond_denominator k F > 2 * m / ϑ) :
    DHL k (m + 1) := by
  -- Silence "unused" linter warnings on inputs that the discharge will use.
  let _ := hk; let _ := hm; let _ := hε_pos; let _ := hε_lt; let _ := hϑ
  sorry

end BoundedGaps.Sieve
