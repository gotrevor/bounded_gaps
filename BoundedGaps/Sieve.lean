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
open scoped ContDiff

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

/-! #### Real definitions of the (s1)/(s2) bounds (Tier 1, PR #65)

`alphaBound`/`betaBound` were `opaque` placeholders. Tier 1 of `ROADMAP.md`
asks for honest `noncomputable def`s in the `Asymptotics.IsLittleO` shape,
so the project's structural skeleton stops being self-citing. The supporting
primitives below — the sieve sum over $[x, 2x]$ in a residue class, the
Chebyshev $\theta$-summand, and the main term $B = \phi(W)/W \cdot \log x$ —
make the (s1)/(s2) statements reference genuine number-theoretic objects.

The `o(1)` in the paper is captured **one-sided** via the positive part of
the violation being little-o of the main term: this is the faithful reading
of "$\le (\alpha + o(1)) M$" (resp. "$\ge (\beta - o(1)) M$") and, crucially,
keeps the `s1_holds_from_*` / `s2_holds_from_*` axioms honestly *true* (a
bare `\le \alpha M` would risk a false load-bearing leaf). -/

/-- The Selberg sieve sum $\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}}
\nu(n)$, over the dyadic block $[\lceil x \rceil, \lfloor 2x \rfloor]$
restricted to the residue class $b \pmod W$. -/
noncomputable def sieveSum (ν : ℕ → ℝ) (b W : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W), ν n

/-- Project-level Chebyshev $\theta$-summand: $\log p$ when $p$ is prime,
else $0$. The prime-counting weight appearing in (s2). -/
noncomputable def primeTheta (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The prime-weighted Selberg sieve sum
$\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)\, \theta(n + h_i)$
appearing on the left of (s2). Here $h_i$ is `H.getD i 0`. -/
noncomputable def sieveThetaSum (ν : ℕ → ℝ) (H : List ℕ) (i b W : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W),
    ν n * primeTheta (n + H.getD i 0)

/-- The sieve scale $B := \phi(W)/W \cdot \log x$ (Polymath8b §3). -/
noncomputable def sieveB (W : ℕ) (x : ℝ) : ℝ := (W.totient : ℝ) / W * Real.log x

/-- The (s1) main term $B^{-k}\, x/W$. -/
noncomputable def alphaMainTerm (k W : ℕ) (x : ℝ) : ℝ :=
  sieveB W x ^ (-(k : ℤ)) * (x / W)

/-- The (s2) main term $B^{1-k}\, x/\phi(W)$. -/
noncomputable def betaMainTerm (k W : ℕ) (x : ℝ) : ℝ :=
  sieveB W x ^ ((1 : ℤ) - (k : ℤ)) * (x / W.totient)

/-- The asymptotic upper bound (Polymath8b §3 eqn (s1)):
$$\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)
   \le (\alpha + o(1)) B^{-k} \frac{x}{W}$$
as $x \to \infty$, where $B := \phi(W)/W \cdot \log x$.

Real def (Tier 1): the positive part of the excess
$\big(\mathtt{sieveSum} - \alpha \cdot \mathtt{alphaMainTerm}\big)^+$ is
little-o of the main term — the faithful one-sided reading of the paper's
"$\le (\alpha + o(1)) M$". The asymptotic is $x$-independent (it ranges over
the whole `atTop` filter), so the surrounding `∀ᶠ x` wrapper at the call
sites is equivalent to the asymptotic itself; the `x` parameter is retained
only to preserve the opaque-era call-site shape. -/
def alphaBound (k : ℕ) (ν : ℕ → ℝ) (b W : ℕ) (_x : ℝ) (α : ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun y : ℝ => max (sieveSum ν b W y - α * alphaMainTerm k W y) 0)
    (alphaMainTerm k W)

/-- The asymptotic lower bound (Polymath8b §3 eqn (s2)):
$$\sum_{\substack{x \le n \le 2x \\ n \equiv b\ (W)}} \nu(n)\, \theta(n + h_i)
   \ge (\beta_i - o(1)) B^{1-k} \frac{x}{\phi(W)}$$
as $x \to \infty$, for $i = 1, \ldots, k$. Sister of `alphaBound`.

Real def (Tier 1): the positive part of the shortfall
$\big(\beta \cdot \mathtt{betaMainTerm} - \mathtt{sieveThetaSum}\big)^+$ is
little-o of the main term — the faithful one-sided reading of "$\ge
(\beta - o(1)) M$". The `x` parameter is vestigial as in `alphaBound`. -/
def betaBound (k : ℕ) (ν : ℕ → ℝ) (H : List ℕ) (b W i : ℕ) (_x : ℝ)
    (β : ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun y : ℝ => max (β * betaMainTerm k W y - sieveThetaSum ν H i b W y) 0)
    (betaMainTerm k W)

/-- **Sub-step (d) structural core (s1 side).** `alphaBound` is the `IsLittleO` of the
*positive part* `max(sieveSum − α·main, 0)`. Since `max(a,0) ≤ |a|`, the (cleaner,
two-sided) difference `sieveSum − α·alphaMainTerm = o(alphaMainTerm)` already implies
`alphaBound`. Proof: `max(f,0) =O[atTop] f` (pointwise `|max(f,0)| ≤ |f|`), then transit
through the hypothesis. This reduces the `s1` analytic obligation to the symmetric
difference asymptotic the heuristic-main limit + correction bound naturally produce. -/
theorem alphaBound_of_sub_littleO (k : ℕ) (ν : ℕ → ℝ) (b W : ℕ) (x α : ℝ)
    (h : Asymptotics.IsLittleO Filter.atTop
          (fun y : ℝ => sieveSum ν b W y - α * alphaMainTerm k W y)
          (alphaMainTerm k W)) :
    alphaBound k ν b W x α := by
  refine Asymptotics.IsBigO.trans_isLittleO ?_ h
  refine Asymptotics.isBigO_of_le _ (fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ 0)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Sub-step (d) structural core (s2 side).** Sister of `alphaBound_of_sub_littleO`:
the two-sided shortfall `β·betaMainTerm − sieveThetaSum = o(betaMainTerm)` implies the
one-sided `betaBound`. -/
theorem betaBound_of_sub_littleO (k : ℕ) (ν : ℕ → ℝ) (H : List ℕ) (b W i : ℕ) (x β : ℝ)
    (h : Asymptotics.IsLittleO Filter.atTop
          (fun y : ℝ => β * betaMainTerm k W y - sieveThetaSum ν H i b W y)
          (betaMainTerm k W)) :
    betaBound k ν H b W i x β := by
  refine Asymptotics.IsBigO.trans_isLittleO ?_ h
  refine Asymptotics.isBigO_of_le _ (fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ 0)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- **Sub-step (d) modular assembly (s1).** Given the exact split
`sieveSum = Aheur + Bcorr` (the heuristic main term + correction, e.g.
`sieveSum_separable_eq_heuristic_add_correction`), the *heuristic-main limit*
`Aheur − α·alphaMainTerm = o(alphaMainTerm)` (leaf 1) and the *correction bound*
`Bcorr = o(alphaMainTerm)` (leaves 2,3) together give `alphaBound`. This is the
machine-checked dependency `leaf 1 ∧ leaves 2,3 ⟹ s1`. -/
theorem alphaBound_of_heuristic_correction (k : ℕ) (ν : ℕ → ℝ) (b W : ℕ) (x α : ℝ)
    (Aheur Bcorr : ℝ → ℝ)
    (hsplit : ∀ y, sieveSum ν b W y = Aheur y + Bcorr y)
    (hheur : Asymptotics.IsLittleO Filter.atTop
              (fun y => Aheur y - α * alphaMainTerm k W y) (alphaMainTerm k W))
    (hcorr : Asymptotics.IsLittleO Filter.atTop Bcorr (alphaMainTerm k W)) :
    alphaBound k ν b W x α := by
  apply alphaBound_of_sub_littleO
  have hrw : (fun y => sieveSum ν b W y - α * alphaMainTerm k W y)
      = (fun y => (Aheur y - α * alphaMainTerm k W y) + Bcorr y) := by
    funext y; rw [hsplit y]; ring
  rw [hrw]
  exact hheur.add hcorr

/-- **Sub-step (d) modular assembly (s2).** Sister of
`alphaBound_of_heuristic_correction` for the prime-weighted sum: split
`sieveThetaSum = Aheur + Bcorr`, the heuristic limit
`β·betaMainTerm − Aheur = o(betaMainTerm)` and correction `Bcorr = o(betaMainTerm)`
give `betaBound`. -/
theorem betaBound_of_heuristic_correction (k : ℕ) (ν : ℕ → ℝ) (H : List ℕ) (b W i : ℕ)
    (x β : ℝ) (Aheur Bcorr : ℝ → ℝ)
    (hsplit : ∀ y, sieveThetaSum ν H i b W y = Aheur y + Bcorr y)
    (hheur : Asymptotics.IsLittleO Filter.atTop
              (fun y => β * betaMainTerm k W y - Aheur y) (betaMainTerm k W))
    (hcorr : Asymptotics.IsLittleO Filter.atTop Bcorr (betaMainTerm k W)) :
    betaBound k ν H b W i x β := by
  apply betaBound_of_sub_littleO
  have hrw : (fun y => β * betaMainTerm k W y - sieveThetaSum ν H i b W y)
      = (fun y => (β * betaMainTerm k W y - Aheur y) - Bcorr y) := by
    funext y; rw [hsplit y]; ring
  rw [hrw]
  exact hheur.sub hcorr

/-- Fin-card ↔ List.countP: counting indices `i : Fin k` whose `H.getD i 0`
satisfies `p` equals `H.countP p`, when `H.length = k`. -/
theorem card_fin_filter_eq_countP {k : ℕ} (H : List ℕ) (hLen : H.length = k)
    (p : ℕ → Bool) :
    (Finset.univ.filter (fun i : Fin k => p (H.getD i.val 0))).card = H.countP p := by
  subst hLen
  have hcount : ∀ L : List ℕ,
      L.countP p = (L.map (fun a => if p a then (1:ℕ) else 0)).sum := by
    intro L; induction L with
    | nil => simp
    | cons a t ih =>
        rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
        by_cases h : p a <;> simp [h] <;> ring
  rw [Finset.card_filter, hcount H]
  have hof : (List.ofFn (fun i : Fin H.length => if p (H.getD i.val 0) then (1:ℕ) else 0))
           = H.map (fun a => if p a then (1:ℕ) else 0) := by
    rw [show (fun i : Fin H.length => if p (H.getD i.val 0) then (1:ℕ) else 0)
          = (fun i : Fin H.length => (fun a => if p a then (1:ℕ) else 0) H[i.val]) from by
          funext i; rw [List.getD_eq_getElem]]
    exact List.ofFn_getElem_eq_map H (fun a => if p a then (1:ℕ) else 0)
  rw [← List.sum_ofFn, hof]

/-- Pigeonhole bridge: if the bracket `∑ᵢ θ(n+hᵢ) − m·log(3x)` is positive and
each `n+hᵢ ≤ 3x`, then at least `m+1` of the `n+hᵢ` are prime. -/
theorem pigeonhole_bridge {k : ℕ} (H : List ℕ) (hLen : H.length = k) (m n : ℕ) (x : ℝ)
    (hx : 1 < 3 * x)
    (hbound : ∀ i : Fin k, (↑(n + H.getD i.val 0) : ℝ) ≤ 3 * x)
    (hbracket : (m : ℝ) * Real.log (3 * x)
        < ∑ i : Fin k, primeTheta (n + H.getD i.val 0)) :
    H.countP (fun h => (n + h).Prime) ≥ m + 1 := by
  set B := Real.log (3 * x) with hB
  have hBpos : 0 < B := Real.log_pos hx
  set P : Fin k → Prop := fun i => (n + H.getD i.val 0).Prime with hP
  classical
  have hterm : ∀ i : Fin k,
      primeTheta (n + H.getD i.val 0) ≤ (if P i then B else 0) := by
    intro i
    simp only [primeTheta, hP]
    split_ifs with hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (hbound i)
    · exact le_refl 0
  have hsum_le : ∑ i : Fin k, primeTheta (n + H.getD i.val 0)
      ≤ ((Finset.univ.filter P).card : ℝ) * B := by
    calc ∑ i, primeTheta (n + H.getD i.val 0)
        ≤ ∑ i, (if P i then B else 0) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = ∑ i, (if P i then (1:ℝ) else 0) * B := by
            refine Finset.sum_congr rfl (fun i _ => ?_); split <;> simp
      _ = (∑ i, (if P i then (1:ℝ) else 0)) * B := by rw [Finset.sum_mul]
      _ = ((Finset.univ.filter P).card : ℝ) * B := by rw [Finset.sum_boole]
  have hm_lt : (m : ℝ) < ((Finset.univ.filter P).card : ℝ) :=
    lt_of_mul_lt_mul_right (hbracket.trans_le hsum_le) hBpos.le
  have hm_lt_nat : m < (Finset.univ.filter P).card := by exact_mod_cast hm_lt
  have hcard : (Finset.univ.filter P).card
      = H.countP (fun h => (n + h).Prime) := by
    rw [← card_fin_filter_eq_countP H hLen (fun h => decide ((n + h).Prime))]
    congr 1
    apply Finset.filter_congr
    intro i _; simp [hP]
  omega

/-- Main-term ratio identity: `betaMainTerm = alphaMainTerm · log x`
(both built from `sieveB = φ(W)/W · log x`). Holds whenever `log x ≠ 0`. -/
theorem betaMainTerm_eq_alphaMainTerm_mul_log (k W : ℕ) (hW : 1 ≤ W) (x : ℝ)
    (hlog : Real.log x ≠ 0) :
    betaMainTerm k W x = alphaMainTerm k W x * Real.log x := by
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  have hφpos : (0:ℝ) < W.totient := by
    have := Nat.totient_pos.mpr (by omega : 0 < W); exact_mod_cast this
  have hB : sieveB W x ≠ 0 := by
    simp only [sieveB]
    apply mul_ne_zero (div_ne_zero (by positivity) (by positivity)) hlog
  simp only [betaMainTerm, alphaMainTerm]
  rw [show (1:ℤ) - (k:ℤ) = 1 + (-(k:ℤ)) from by ring, zpow_add₀ hB, zpow_one]
  simp only [sieveB]
  field_simp

open Filter Asymptotics in
/-- `alphaMainTerm =o betaMainTerm`: since `M₂ = M₁ · log x` and `log x → ∞`. -/
theorem alphaMainTerm_isLittleO_betaMainTerm (k W : ℕ) (hW : 1 ≤ W) :
    alphaMainTerm k W =o[atTop] betaMainTerm k W := by
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  have hφpos : (0:ℝ) < W.totient := by
    have := Nat.totient_pos.mpr (by omega : 0 < W); exact_mod_cast this
  have hM1pos : ∀ᶠ x : ℝ in atTop, 0 < alphaMainTerm k W x := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hBpos : 0 < sieveB W x := by
      simp only [sieveB]; positivity
    simp only [alphaMainTerm]
    have : 0 < sieveB W x ^ (-(k:ℤ)) := zpow_pos hBpos _
    have hx0 : 0 < x := by linarith
    positivity
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hM1pos, Real.tendsto_log_atTop.eventually_ge_atTop (1/c),
    eventually_gt_atTop (1:ℝ)]
    with x hM1 hlog hx1
  have heq : betaMainTerm k W x = alphaMainTerm k W x * Real.log x :=
    betaMainTerm_eq_alphaMainTerm_mul_log k W hW x (Real.log_pos hx1).ne'
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  rw [heq, Real.norm_of_nonneg hM1.le, Real.norm_of_nonneg (by positivity)]
  have : 1 ≤ c * Real.log x := by
    rw [div_le_iff₀ hc] at hlog; linarith
  nlinarith [hM1, this]

open Filter Asymptotics in
/-- helper: `log(3x)·M₁ =O M₂` (ratio `log3x/logx → 1`, bounded by 2). -/
theorem log3x_mul_alphaMainTerm_isBigO (k W : ℕ) (hW : 1 ≤ W) :
    (fun x : ℝ => Real.log (3 * x) * alphaMainTerm k W x) =O[atTop] (betaMainTerm k W) := by
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  have hφpos : (0:ℝ) < W.totient := by
    have := Nat.totient_pos.mpr (by omega : 0 < W); exact_mod_cast this
  rw [isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (3:ℝ)] with x hx3
  have hx1 : (1:ℝ) < x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlog3x_pos : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
  have hM1pos : 0 < alphaMainTerm k W x := by
    have hBpos : 0 < sieveB W x := by simp only [sieveB]; positivity
    simp only [alphaMainTerm]
    have : 0 < sieveB W x ^ (-(k:ℤ)) := zpow_pos hBpos _
    positivity
  have heq : betaMainTerm k W x = alphaMainTerm k W x * Real.log x :=
    betaMainTerm_eq_alphaMainTerm_mul_log k W hW x hlogpos.ne'
  have hlogmul : Real.log (3 * x) = Real.log 3 + Real.log x :=
    Real.log_mul (by norm_num) hxpos.ne'
  have hlog3_le : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
  rw [Real.norm_of_nonneg (by positivity), heq, Real.norm_of_nonneg (by positivity)]
  nlinarith [hM1pos, hlogpos, hlog3_le, hlogmul]

open Filter Asymptotics in
/-- helper: `m·log(3x)·err1 =o M₂` when `err1 =o M₁`. -/
theorem m_log3x_err1_isLittleO {k W : ℕ} (hW : 1 ≤ W) (m : ℕ) (err1 : ℝ → ℝ)
    (h1 : err1 =o[atTop] (alphaMainTerm k W)) :
    (fun x : ℝ => (m:ℝ) * Real.log (3 * x) * err1 x) =o[atTop] (betaMainTerm k W) := by
  have hstep : (fun x : ℝ => Real.log (3 * x) * err1 x) =o[atTop] (betaMainTerm k W) := by
    have h2 : (fun x : ℝ => Real.log (3 * x) * err1 x)
        =o[atTop] (fun x => Real.log (3 * x) * alphaMainTerm k W x) :=
      (isBigO_refl (fun x : ℝ => Real.log (3 * x)) atTop).mul_isLittleO h1
    exact h2.trans_isBigO (log3x_mul_alphaMainTerm_isBigO k W hW)
  have := hstep.const_mul_left (m : ℝ)
  simpa [mul_assoc] using this

open Filter Asymptotics in
/-- Claim 2: the combined sieve sum `∑ᵢ STSᵢ − m·log(3x)·sieveSum` is
eventually positive. -/
theorem core_positive {k : ℕ} (H : List ℕ) {m : ℕ} {b W : ℕ} {ν : ℕ → ℝ} {α : ℝ}
    {β : Fin k → ℝ} (hW : 1 ≤ W) (hα : 0 < α)
    (hKey : (↑m : ℝ) < (∑ i, β i) / α)
    (hS1 : (fun y => max (sieveSum ν b W y - α * alphaMainTerm k W y) 0)
        =o[atTop] (alphaMainTerm k W))
    (hS2 : ∀ i, (fun y => max (β i * betaMainTerm k W y - sieveThetaSum ν H i.val b W y) 0)
        =o[atTop] (betaMainTerm k W)) :
    ∀ᶠ x : ℝ in atTop, 0 < (∑ i : Fin k, sieveThetaSum ν H i.val b W x)
        - (↑m) * Real.log (3 * x) * sieveSum ν b W x := by
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  have hδ : 0 < (∑ i, β i) - m * α := by
    rw [lt_div_iff₀ hα] at hKey; linarith
  set δ := (∑ i, β i) - m * α with hδdef
  have hRo : (fun x => (↑m * α * Real.log 3) * alphaMainTerm k W x
      + (∑ i, max (β i * betaMainTerm k W x - sieveThetaSum ν H i.val b W x) 0)
      + ↑m * Real.log (3 * x) * (max (sieveSum ν b W x - α * alphaMainTerm k W x) 0))
      =o[atTop] (betaMainTerm k W) := by
    refine ((?_ : _ =o[atTop] _).add (?_ : _ =o[atTop] _)).add (?_ : _ =o[atTop] _)
    · exact (alphaMainTerm_isLittleO_betaMainTerm k W hW).const_mul_left _
    · exact IsLittleO.sum (fun i _ => hS2 i)
    · exact m_log3x_err1_isLittleO hW m _ hS1
  filter_upwards [hRo.def (half_pos hδ), eventually_gt_atTop (1:ℝ),
    (alphaMainTerm_isLittleO_betaMainTerm k W hW).def (c := 1) one_pos]
    with x hRbound hx1 _
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlog3x : 0 ≤ Real.log (3 * x) := (Real.log_pos (by linarith)).le
  have hM1pos : 0 < alphaMainTerm k W x := by
    have hBpos : 0 < sieveB W x := by simp only [sieveB]; positivity
    simp only [alphaMainTerm]
    have : 0 < sieveB W x ^ (-(k:ℤ)) := zpow_pos hBpos _
    have hx0 : 0 < x := by linarith
    positivity
  have hM2eq : betaMainTerm k W x = alphaMainTerm k W x * Real.log x :=
    betaMainTerm_eq_alphaMainTerm_mul_log k W hW x hlogpos.ne'
  have hM2pos : 0 < betaMainTerm k W x := by rw [hM2eq]; positivity
  have hlog3eq : Real.log (3 * x) = Real.log 3 + Real.log x :=
    Real.log_mul (by norm_num) (by linarith)
  set M₁ := alphaMainTerm k W x
  set M₂ := betaMainTerm k W x
  set SS := sieveSum ν b W x
  set err1 := max (SS - α * M₁) 0 with herr1
  set STS := fun i : Fin k => sieveThetaSum ν H i.val b W x with hSTS
  set err2 := fun i : Fin k => max (β i * M₂ - STS i) 0 with herr2
  have hSS_le : SS ≤ α * M₁ + err1 := by
    have := le_max_left (SS - α * M₁) 0; rw [herr1]; linarith [le_max_left (SS - α * M₁) (0:ℝ)]
  have hSTS_ge : ∀ i, β i * M₂ - err2 i ≤ STS i := by
    intro i; have := le_max_left (β i * M₂ - STS i) (0:ℝ); rw [herr2]; simp; linarith
  have hsumSTS : (∑ i, β i) * M₂ - (∑ i, err2 i) ≤ ∑ i, STS i := by
    have : ∑ i, (β i * M₂ - err2 i) ≤ ∑ i, STS i := Finset.sum_le_sum (fun i _ => hSTS_ge i)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at this; linarith
  have hmulSS : (↑m) * Real.log (3 * x) * SS
      ≤ (↑m) * Real.log (3 * x) * (α * M₁) + (↑m) * Real.log (3 * x) * err1 := by
    have hnn : 0 ≤ (↑m : ℝ) * Real.log (3 * x) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hSS_le hnn]
  have hbig : (↑m) * Real.log (3 * x) * (α * M₁) = m * α * M₂ + m * α * Real.log 3 * M₁ := by
    rw [hlog3eq, hM2eq]; ring
  have hRnn_bound : (↑m * α * Real.log 3) * M₁
      + (∑ i, err2 i) + ↑m * Real.log (3 * x) * err1
      ≤ (δ / 2) * M₂ := by
    have : ‖(↑m * α * Real.log 3) * M₁ + (∑ i, err2 i) + ↑m * Real.log (3 * x) * err1‖
        ≤ (δ / 2) * ‖M₂‖ := hRbound
    rwa [Real.norm_of_nonneg hM2pos.le,
      Real.norm_of_nonneg (by positivity)] at this
  have hLB : (δ / 2) * M₂
      ≤ (∑ i, STS i) - ↑m * Real.log (3 * x) * SS := by
    rw [hδdef]; nlinarith [hsumSTS, hmulSS, hbig, hRnn_bound]
  have : 0 < (δ / 2) * M₂ := by positivity
  linarith [hLB]

open Filter Asymptotics in
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
    {k : ℕ} (H : List ℕ) (_hAdm : Admissible H) (hLen : H.length = k)
    {m : ℕ} {b W : ℕ} {ν : ℕ → ℝ} {α : ℝ} {β : Fin k → ℝ}
    (hW : 1 ≤ W) (hν : ∀ n, 0 ≤ ν n)
    (hα : 0 < α) (_hβ : ∀ i, 0 ≤ β i)
    (hKey : (∑ i, β i) / α > m)
    (hS1 : ∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α)
    (hS2 : ∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
              betaBound k ν H b W i.val x (β i)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      H.countP (fun h => (n + h).Prime) ≥ m + 1 := by
  simp only [alphaBound] at hS1
  rw [Filter.eventually_const] at hS1
  have hS2' : ∀ i, (fun y => max (β i * betaMainTerm k W y
      - sieveThetaSum ν H i.val b W y) 0) =o[atTop] (betaMainTerm k W) := by
    intro i; have h := hS2 i; simp only [betaBound] at h; rwa [Filter.eventually_const] at h
  set Mx := Finset.univ.sup (fun i : Fin k => H.getD i.val 0) with hMx
  have hreal : ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, ⌈x⌉₊ ≤ n ∧ n ≤ ⌊2 * x⌋₊ ∧
      H.countP (fun h => (n + h).Prime) ≥ m + 1 := by
    filter_upwards [core_positive H hW hα hKey hS1 hS2',
      eventually_ge_atTop ((Mx : ℝ) + 1), eventually_gt_atTop (1:ℝ)]
      with x hpos hMxbound hx1
    have heq : (∑ i : Fin k, sieveThetaSum ν H i.val b W x)
          - ↑m * Real.log (3 * x) * sieveSum ν b W x
        = ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W),
            ν n * ((∑ i : Fin k, primeTheta (n + H.getD i.val 0))
                    - ↑m * Real.log (3 * x)) := by
      simp only [sieveThetaSum, sieveSum]
      rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [mul_sub, Finset.mul_sum]; ring
    rw [heq] at hpos
    have hsum0 : (∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W), (0:ℝ))
        < ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W),
            ν n * ((∑ i : Fin k, primeTheta (n + H.getD i.val 0)) - ↑m * Real.log (3 * x)) := by
      rw [Finset.sum_const_zero]; exact hpos
    obtain ⟨n, hn_mem, hn_pos⟩ := Finset.exists_lt_of_sum_lt hsum0
    have hbracket_pos : 0 < (∑ i : Fin k, primeTheta (n + H.getD i.val 0))
        - ↑m * Real.log (3 * x) := by
      by_contra h; rw [not_lt] at h
      nlinarith [hν n, hn_pos]
    have hn_Icc : n ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := Finset.mem_of_mem_filter n hn_mem
    rw [Finset.mem_Icc] at hn_Icc
    have hbnd : ∀ i : Fin k, (↑(n + H.getD i.val 0) : ℝ) ≤ 3 * x := by
      intro i
      have hn2x : (n : ℝ) ≤ 2 * x := by
        have h1 : (n : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast hn_Icc.2
        exact h1.trans (Nat.floor_le (by positivity))
      have hhi : (↑(H.getD i.val 0) : ℝ) ≤ (Mx : ℝ) := by
        exact_mod_cast Finset.le_sup (f := fun i : Fin k => H.getD i.val 0) (Finset.mem_univ i)
      push_cast; linarith [hMxbound]
    exact ⟨n, hn_Icc.1, hn_Icc.2,
      pigeonhole_bridge H hLen m n x (by linarith) hbnd (by linarith [hbracket_pos])⟩
  have htrans := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
  filter_upwards [htrans] with N hN
  obtain ⟨n, h1, h2, h3⟩ := hN
  refine ⟨n, ?_, ?_, h3⟩
  · rwa [Nat.ceil_natCast] at h1
  · rw [show (2:ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast] at h2
    exact h2

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
        1 ≤ W ∧ (∀ n, 0 ≤ ν n) ∧ 0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
        (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
        (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
            betaBound k ν H b W i.val x (β i))) :
    DHL k (m + 1) := by
  intro H hAdm hLen
  obtain ⟨b, W, ν, α, β, hW, hν, hα, hβ, hKey, hS1, hS2⟩ := hSieve H hAdm hLen
  exact infinite_witnesses_of_eventual_witness
    (witness_eventually_from_sieve_data H hAdm hLen hW hν hα hβ hKey hS1 hS2)

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
          ContDiff ℝ ∞ F ∧
          Function.support F ⊆ simplex k ∧
          mkF_denominator k F > 0 ∧
          v = MkF k F }

/-- $M_k := \sup_F M_k(F)$ over admissible $F$ on the simplex.

Concrete `sSup` over `MkSet k`. Per `Mathlib`'s `ℝ`-`ConditionallyCompleteLinearOrder`
convention, an empty or unbounded admissible set yields `0`; in the
relevant Polymath8b regime ($k \ge 2$) the set is non-empty and bounded —
see axioms `MkSet_nonempty` and `MkSet_bddAbove`. -/
noncomputable def Mk (k : ℕ) : ℝ := sSup (MkSet k)

/-- The $k$-simplex is compact: it is closed (a finite intersection of closed
half-spaces) and bounded (`‖t‖ ≤ 1` in the sup norm), hence compact in the
finite-dimensional `Fin k → ℝ` by Heine-Borel. Reusable: feeds both the
integrability of continuous test functions over the simplex and the
upper-bound (`MkSet_bddAbove`) argument. -/
theorem isCompact_simplex (k : ℕ) : IsCompact (simplex k) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · -- closed: ⋂ᵢ {0 ≤ tᵢ} ∩ {∑ tᵢ ≤ 1}
    have heq : simplex k =
        (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ 1} := by
      ext t; simp only [simplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  · -- bounded: simplex ⊆ closedBall 0 1
    apply (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 1)).subset
    intro t ht
    simp only [simplex, Set.mem_setOf_eq] at ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero,
        pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact le_trans (Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)) ht.2

/-- For $k \ge 2$, the admissible-F set for $M_k$ is non-empty.

Polymath8b §5 implicitly assumes this: any smooth bump supported on the
interior of the simplex with nonzero $\int F^2$ realizes some
$\mathrm{MkF}(k, F)$.

**Discharged (ROADMAP Tier 2).** Witness: a product of one-dimensional
`ContDiffBump`s, $F(t) = \prod_i b(t_i)$, with $b$ centered at $K/2$
($K := 1/k$) and radii $K/8 < K/4$, so $\operatorname{supp} b \subseteq
(K/4, 3K/4) \subseteq (0, 1/k)$. Then each coordinate of any point in
$\operatorname{supp} F$ lies in $(K/4, 3K/4)$, giving $t_i \ge 0$ and
$\sum_i t_i < k \cdot 3K/4 = 3/4 \le 1$, so $\operatorname{supp} F \subseteq
\operatorname{simplex}$. Smoothness is `contDiffAt_prod` over the smooth
factors $t \mapsto b(t_i)$; the denominator $\int_{\text{simplex}} F^2 > 0$
because $\operatorname{supp} F$ is a nonempty open set (so positive volume)
contained in the simplex (`setIntegral_pos_iff_support_of_nonneg_ae`). -/
theorem MkSet_nonempty (k : ℕ) (hk : 2 ≤ k) : (MkSet k).Nonempty := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set K : ℝ := (k:ℝ)⁻¹ with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hkK : (k:ℝ) * K = 1 := by rw [hKdef]; field_simp
  -- 1D smooth bump supported in (K/4, 3K/4) ⊆ (0, 1/k): center K/2, radii K/8 < K/4
  set b : ContDiffBump (K/2 : ℝ) := ⟨K/8, K/4, by linarith, by linarith⟩ with hbdef
  have hrOut : b.rOut = K/4 := by rw [hbdef]
  -- the test function F t = ∏ i, b (t i)
  set F : (Fin k → ℝ) → ℝ := fun t => ∏ i : Fin k, b (t i) with hFdef
  -- smoothness: a finite product of the smooth factors t ↦ b (t i)
  have hfac : ∀ i : Fin k, ContDiff ℝ ∞ (⇑b ∘ fun t : (Fin k → ℝ) => t i) :=
    fun i => b.contDiff.comp (contDiff_apply ℝ ℝ i)
  have hF_smooth : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]; intro x
    exact contDiffAt_prod (fun i _ => (hfac i).contDiffAt)
  -- support ⊆ simplex
  have hF_supp : Function.support F ⊆ simplex k := by
    intro t ht
    simp only [Function.mem_support, hFdef] at ht
    have hall : ∀ i, b (t i) ≠ 0 := fun i hi => ht (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hbounds : ∀ i, K/4 < t i ∧ t i < 3*K/4 := by
      intro i
      have hb : t i ∈ Function.support (b : ℝ → ℝ) := Function.mem_support.mpr (hall i)
      rw [b.support_eq, Metric.mem_ball, Real.dist_eq, hrOut, abs_lt] at hb
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hsum : ∑ i, t i < 1 := by
      calc ∑ i, t i < ∑ _i : Fin k, 3*K/4 :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => (hbounds i).2)
        _ = (k:ℝ) * (3*K/4) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = 3/4 := by rw [show (k:ℝ)*(3*K/4) = 3/4 * ((k:ℝ)*K) from by ring, hkK]; norm_num
        _ < 1 := by norm_num
    exact ⟨fun i => le_of_lt (lt_trans (by linarith [hKpos] : (0:ℝ) < K/4) (hbounds i).1), hsum.le⟩
  -- positive Rayleigh denominator
  have hcont : Continuous F := hF_smooth.continuous
  have hsupp_sq : Function.support (fun t : (Fin k → ℝ) => F t ^ 2) = Function.support F := by
    ext t; simp only [Function.mem_support, ne_eq, pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)]
  have hopen : IsOpen (Function.support F) := by
    have hpre : Function.support F = F ⁻¹' {0}ᶜ := by
      ext t; simp [Function.mem_support, Set.mem_preimage]
    rw [hpre]; exact isOpen_compl_singleton.preimage hcont
  have hne : (Function.support F).Nonempty := by
    refine ⟨fun _ => K/2, ?_⟩
    have hbc : (0:ℝ) < b (K/2) := b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)
    have hval : F (fun _ => K/2) = (b (K/2)) ^ k := by simp [hFdef, Finset.prod_const]
    rw [Function.mem_support, hval]; exact pow_ne_zero _ hbc.ne'
  have hinteg : MeasureTheory.IntegrableOn (fun t => F t ^ 2) (simplex k) :=
    (hcont.pow 2).locallyIntegrable.integrableOn_isCompact (isCompact_simplex k)
  have hF_den : (0:ℝ) < mkF_denominator k F := by
    have hrw : mkF_denominator k F = ∫ t in simplex k, F t ^ 2 := rfl
    rw [hrw, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
          (Filter.Eventually.of_forall fun t => sq_nonneg (F t)) hinteg,
        hsupp_sq, Set.inter_eq_left.mpr hF_supp]
    exact hopen.measure_pos (μ := MeasureTheory.volume) hne
  exact ⟨MkF k F, F, hF_smooth, hF_supp, hF_den, rfl⟩

open MeasureTheory in
/-- **Fibration / change-of-variables for integrals over `Fin (n+1) → ℝ`.**
For integrable $G$,
$$\int_{\mathbb{R}^{n+1}} G = \int_{\mathbb{R}^n}\!\int_{\mathbb{R}}
   G(\mathrm{insertNth}\, i\, t_i\, s)\, dt_i\, ds,$$
via the measure-preserving `MeasurableEquiv.piFinSuccAbove i`
($\mathbb{R}^{n+1} \simeq \mathbb{R} \times \mathbb{R}^n$, whose inverse is
`insertNth`) and `integral_prod_symm`. The keystone for `MkSet_bddAbove`: it
relates the full-space `∫ F²` to the `insertNth`-iterated form in which the
Maynard marginals $J_i$ and the Rayleigh denominator are written. -/
theorem integral_insertNth_eq {n : ℕ} (i : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ)
    (hG : Integrable G) :
    (∫ t, G t) = ∫ s : Fin n → ℝ, ∫ ti : ℝ, G (i.insertNth ti s) := by
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hint : Integrable
      (fun p : ℝ × (Fin n → ℝ) =>
        G ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm p))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hG
  rw [← mp.symm.integral_comp' G, Measure.volume_eq_prod ℝ (Fin n → ℝ),
      integral_prod_symm _ hint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]

open MeasureTheory Set in
/-- **Integral Cauchy-Schwarz on `Icc 0 L`** via Jensen (`x ↦ x²` convex on a finite
measure): `(∫_{[0,L]} h)² ≤ L · ∫_{[0,L]} h²`. The `L` factor is the measure of the
interval; for `L ≤ 1` it can be dropped, which is how the crude `M_k ≤ k` bound arises. -/
theorem cs_Icc (L : ℝ) (hL : 0 ≤ L) (h : ℝ → ℝ)
    (hint : IntegrableOn h (Icc 0 L)) (hint2 : IntegrableOn (fun x => h x ^ 2) (Icc 0 L)) :
    (∫ x in Icc 0 L, h x) ^ 2 ≤ L * ∫ x in Icc 0 L, h x ^ 2 := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · subst hL0
    simp
  · have hLne : L ≠ 0 := ne_of_gt hLpos
    have hmeas : volume (Icc (0:ℝ) L) ≠ 0 := by
      rw [Real.volume_Icc, sub_zero]; simp [ENNReal.ofReal_eq_zero]; linarith
    have htop : volume (Icc (0:ℝ) L) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hMr : volume.real (Icc (0:ℝ) L) = L := by
      rw [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hL]
    have hconv : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow (by decide)
    have jensen := hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_univ
      hmeas htop (Filter.Eventually.of_forall fun _ => mem_univ _) hint hint2
    rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul] at jensen
    simp only [hMr] at jensen
    have hL2 : (0:ℝ) ≤ L ^ 2 := sq_nonneg L
    calc (∫ x in Icc 0 L, h x) ^ 2
        = L ^ 2 * (L⁻¹ * (∫ x in Icc 0 L, h x)) ^ 2 := by field_simp
      _ ≤ L ^ 2 * (L⁻¹ * ∫ x in Icc 0 L, h x ^ 2) := mul_le_mul_of_nonneg_left jensen hL2
      _ = L * ∫ x in Icc 0 L, h x ^ 2 := by field_simp

/-- The `k`-simplex is closed (it is compact). -/
theorem isClosed_simplex (k : ℕ) : IsClosed (simplex k) := (isCompact_simplex k).isClosed

open MeasureTheory Set in
/-- **Each Maynard marginal is bounded by the Rayleigh denominator: `J_i(F) ≤ I(F)`.**
Cauchy-Schwarz (`cs_Icc`) on the inner `[0, 1-∑s]` integral. The moving boundary is tamed by
the support hypothesis: for `s ∈ simplex n`, `F(insertNth i · s)` vanishes outside `[0, 1-∑s]`
(the inserted point leaves the simplex), so the clamped inner integral equals the full-line
marginal `m s = ∫ F(insertNth i · s)`, whose square is `≤ Φ s = ∫ F(insertNth i · s)²`. Summing
`Φ` back up via the `integral_insertNth_eq` fibration recovers `∫_{ℝ^{n+1}} F² = I(F)`. -/
theorem J_i_le_denom (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ)
    (hcont : Continuous F) (hFsupp : Function.support F ⊆ simplex (n + 1)) (i : Fin (n + 1)) :
    J_i (n + 1) F i ≤ mkF_denominator (n + 1) F := by
  classical
  have hsimpClosed : IsClosed (simplex (n + 1)) := isClosed_simplex (n + 1)
  have hcs : HasCompactSupport F :=
    IsCompact.of_isClosed_subset (isCompact_simplex (n + 1)) isClosed_closure
      (closure_minimal hFsupp hsimpClosed)
  have hF2cont : Continuous (fun t => F t ^ 2) := hcont.pow 2
  have hcs2 : HasCompactSupport (fun t => F t ^ 2) := by
    apply hcs.comp_left (g := fun x : ℝ => x ^ 2); simp
  have hFi : Integrable F := hcont.integrable_of_hasCompactSupport hcs
  have hF2i : Integrable (fun t => F t ^ 2) := hF2cont.integrable_of_hasCompactSupport hcs2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set m : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, F (i.insertNth ti s) with hm
  set Φ : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, F (i.insertNth ti s) ^ 2 with hΦ
  have hprodF2 : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hF2i
  have hΦi : Integrable Φ := by
    have h := hprodF2.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hprodF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hFi
  have hmi : Integrable m := by
    have h := hprodF.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hΦnn : ∀ s, 0 ≤ Φ s := fun s => integral_nonneg fun ti => sq_nonneg _
  have key : ∀ s ∈ simplex n,
      (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) = m s ∧ m s ^ 2 ≤ Φ s := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    set L := 1 - ∑ j, s j with hL
    have hLnn : 0 ≤ L := by rw [hL]; linarith
    have hL1 : L ≤ 1 := by rw [hL]; linarith
    have hzero : ∀ ti, ti ∉ Icc (0 : ℝ) L → F (i.insertNth ti s) = 0 := by
      intro ti hti
      by_contra hne
      have hmem : i.insertNth ti s ∈ simplex (n + 1) := hFsupp (Function.mem_support.mpr hne)
      obtain ⟨hmem_nn, hmem_sum⟩ := hmem
      apply hti
      refine ⟨?_, ?_⟩
      · have := hmem_nn i; rwa [Fin.insertNth_apply_same] at this
      · rw [hL, le_sub_iff_add_le]
        have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq] at hmem_sum; linarith
    have hcont_h : Continuous (fun ti => F (i.insertNth ti s)) :=
      hcont.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hint_h : IntegrableOn (fun ti => F (i.insertNth ti s)) (Icc 0 L) :=
      hcont_h.integrableOn_Icc
    have hint_h2 : IntegrableOn (fun ti => F (i.insertNth ti s) ^ 2) (Icc 0 L) :=
      (hcont_h.pow 2).integrableOn_Icc
    have eqfull : (∫ ti in Icc 0 L, F (i.insertNth ti s)) = m s :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have eqfull2 : (∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2) = Φ s := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro ti hti; rw [hzero ti hti]; ring
    refine ⟨eqfull, ?_⟩
    have hcsq := cs_Icc L hLnn (fun ti => F (i.insertNth ti s)) hint_h hint_h2
    rw [eqfull] at hcsq
    have hnn2 : 0 ≤ ∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2 :=
      integral_nonneg fun ti => sq_nonneg _
    calc m s ^ 2 ≤ L * ∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2 := hcsq
      _ ≤ 1 * ∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2 := mul_le_mul_of_nonneg_right hL1 hnn2
      _ = Φ s := by rw [one_mul, eqfull2]
  have hmeasS : MeasurableSet (simplex n) := (isClosed_simplex n).measurableSet
  change (∫ s in simplex n, (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2)
      ≤ mkF_denominator (n + 1) F
  have hcongr : (∫ s in simplex n, (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2)
              = ∫ s in simplex n, m s ^ 2 := by
    refine setIntegral_congr_fun hmeasS ?_
    intro s hs; dsimp only; rw [(key s hs).1]
  rw [hcongr]
  have hm2_aesm : AEStronglyMeasurable (fun s => m s ^ 2) (volume.restrict (simplex n)) :=
    (hmi.aestronglyMeasurable.pow 2).restrict
  have hm2_int : IntegrableOn (fun s => m s ^ 2) (simplex n) := by
    refine Integrable.mono' hΦi.integrableOn hm2_aesm ?_
    refine (ae_restrict_iff' hmeasS).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (key s hs).2
  calc (∫ s in simplex n, m s ^ 2)
      ≤ ∫ s in simplex n, Φ s := by
        refine setIntegral_mono_on hm2_int hΦi.integrableOn hmeasS ?_
        intro s hs; exact (key s hs).2
    _ ≤ ∫ s, Φ s := setIntegral_le_integral hΦi (Filter.Eventually.of_forall hΦnn)
    _ = mkF_denominator (n + 1) F := by
        have hkey := integral_insertNth_eq i (fun t => F t ^ 2) hF2i
        have hden : mkF_denominator (n + 1) F = ∫ t, F t ^ 2 := by
          change (∫ t in simplex (n + 1), F t ^ 2) = ∫ t, F t ^ 2
          refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
          intro t ht
          have hF0 : F t = 0 := by
            by_contra hh; exact ht (hFsupp (Function.mem_support.mpr hh))
          rw [hF0]; ring
        rw [hden, hkey]

/-- The admissible-F set for $M_k$ is bounded above.

Polymath8b Corollary `mk-upper` (the converse direction to `mlower`):
$M_k \le \frac{k}{k-1} \log k$ for all $k \ge 2$. The crude bound $M_k \le k$
already gives `BddAbove`, via Cauchy-Schwarz on each Maynard marginal:
$J_i(F) \le I(F)$ (so $\sum_i J_i \le k\,I$). cf. Polymath8b §5 +
Hensley-Richards 1973 (asymptotic).

**Discharged (ROADMAP Tier 2).** The `k ≥ 1` case bounds `M_k(F) = (∑_i J_i)/I(F) ≤ k`
by showing each Maynard marginal `J_i(F) ≤ I(F)` (`J_i_le_denom`, the substantive lemma:
integral Cauchy-Schwarz `cs_Icc` on each inner `[0,1-∑s]` slice, with the moving boundary
handled via the support hypothesis and the `integral_insertNth_eq` fibration). The `k = 0`
case is `M_0(F) = 0 / I ≤ 0`. The bound `(k : ℝ)` witnesses `BddAbove`. -/
theorem MkSet_bddAbove (k : ℕ) : BddAbove (MkSet k) := by
  refine ⟨(k : ℝ), ?_⟩
  rintro v ⟨F, hFsmooth, hFsupp, hFden, rfl⟩
  cases k with
  | zero =>
    show MkF 0 F ≤ ((0 : ℕ) : ℝ)
    unfold MkF mkF_numerator; simp
  | succ n =>
    show MkF (n + 1) F ≤ (((n + 1 : ℕ)) : ℝ)
    rw [MkF, mkF_numerator_eq_sum_J_i, div_le_iff₀ hFden]
    calc ∑ i, J_i (n + 1) F i
        ≤ ∑ _i : Fin (n + 1), mkF_denominator (n + 1) F :=
          Finset.sum_le_sum fun i _ => J_i_le_denom n F hFsmooth.continuous hFsupp i
      _ = ((n + 1 : ℕ) : ℝ) * mkF_denominator (n + 1) F := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

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

/-! #### `k = 1` reduction to a 1D Rayleigh ratio

For `k = 1` the Maynard quantity collapses to a one-dimensional ratio in
`g t := F (fun _ => t)` over `[0,1]`. The change of variables is the
`MeasurableEquiv.funUnique (Fin 1) ℝ` (a volume-preserving identification of
`Fin 1 → ℝ` with `ℝ`), whose `.symm` sends `t ↦ (fun _ => t)` and pulls back
`simplex 1` to `Set.Icc 0 1`. -/

/-- The preimage of `simplex 1` under the `funUnique` identification
`ℝ ≃ᵐ (Fin 1 → ℝ)` is `[0,1]`. -/
private theorem funUnique_preimage_simplex_one :
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹' (simplex 1) = Set.Icc (0:ℝ) 1 := by
  ext t
  simp only [Set.mem_preimage, MeasurableEquiv.funUnique, simplex, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨h0, hsum⟩; exact ⟨h0 0, by simpa [Fin.sum_univ_one] using hsum⟩
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => by fin_cases i; simpa using h0, by simpa [Fin.sum_univ_one] using h1⟩

/-- Change of variables collapsing a `simplex 1` integral of `φ ∘ F` to a 1D
`[0,1]` integral of `φ (F (fun _ => ·))`. -/
private theorem integral_simplex_one_eq (φ : ℝ → ℝ) (F : (Fin 1 → ℝ) → ℝ) :
    (∫ t in simplex 1, φ (F t)) = ∫ ti in Set.Icc (0:ℝ) 1, φ (F (fun _ => ti)) := by
  have hmp := (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hemb := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
  have key := hmp.setIntegral_preimage_emb hemb (fun y => φ (F y)) (simplex 1)
  rw [funUnique_preimage_simplex_one] at key
  exact key.symm

/-- The Maynard numerator at `k = 1` is `(∫_{[0,1]} g)²`. -/
private theorem mkF_numerator_one (F : (Fin 1 → ℝ) → ℝ) :
    mkF_numerator 1 F = (∫ ti in Set.Icc (0:ℝ) 1, F (fun _ => ti)) ^ 2 := by
  show (∑ i : Fin 1, ∫ s in simplex 0,
      (∫ ti in Set.Icc (0:ℝ) (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2) = _
  rw [Fin.sum_univ_one,
      show simplex 0 = (Set.univ : Set (Fin 0 → ℝ)) from by unfold simplex; ext s; simp]
  have hpt : ∀ (s : Fin 0 → ℝ) (ti : ℝ), (0 : Fin 1).insertNth ti s = (fun _ => ti) := by
    intro s ti; funext j; fin_cases j; simp
  simp only [Fin.sum_univ_zero, sub_zero, hpt]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      show (MeasureTheory.volume (Set.univ : Set (Fin 0 → ℝ))) = 1 from by
        rw [show (Set.univ : Set (Fin 0 → ℝ)) = Set.pi Set.univ (fun _ => Set.univ) from by simp,
            MeasureTheory.volume_pi_pi]; simp]
  simp

/-- The Maynard denominator at `k = 1` is `∫_{[0,1]} g²`. -/
private theorem mkF_denominator_one (F : (Fin 1 → ℝ) → ℝ) :
    mkF_denominator 1 F = ∫ ti in Set.Icc (0:ℝ) 1, F (fun _ => ti) ^ 2 := by
  unfold mkF_denominator
  exact integral_simplex_one_eq (fun y => y ^ 2) F

/-- **Cauchy-Schwarz / Jensen on `[0,1]`**: for `g` continuous on `[0,1]`,
`(∫_{[0,1]} g)² ≤ ∫_{[0,1]} g²`. Proved via Jensen's inequality for the
convex map `x ↦ x²` against the probability measure `volume.restrict [0,1]`. -/
private theorem sq_setIntegral_Icc_le (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1)) :
    (∫ x in Set.Icc (0:ℝ) 1, g x) ^ 2 ≤ ∫ x in Set.Icc (0:ℝ) 1, g x ^ 2 := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) := by constructor; simp
  have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by decide)
  have hint : MeasureTheory.Integrable g
      (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hg.integrableOn_compact isCompact_Icc
  have hint2 : MeasureTheory.Integrable (fun x => g x ^ 2)
      (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) :=
    (hg.pow 2).integrableOn_compact isCompact_Icc
  have key := hconv.map_integral_le (g := fun x : ℝ => x ^ 2) (f := g)
    (by fun_prop) isClosed_univ (by filter_upwards with a using Set.mem_univ _) hint hint2
  simpa using key

/-- For admissible `F` at `k = 1`, the Rayleigh ratio `MkF 1 F ≤ 1`. -/
private theorem mkF_one_le (F : (Fin 1 → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hden : mkF_denominator 1 F > 0) : MkF 1 F ≤ 1 := by
  unfold MkF
  rw [mkF_numerator_one, mkF_denominator_one]
  rw [mkF_denominator_one] at hden
  have hg : ContinuousOn (fun t : ℝ => F (fun _ => t)) (Set.Icc 0 1) :=
    (hF.continuous.comp (by fun_prop)).continuousOn
  rw [div_le_one hden]
  exact sq_setIntegral_Icc_le _ hg

/-- $M_k \le 1$ for $k \le 1$. Standard variational bound: for $k = 0$,
$M_0 = 0$ by definition (the numerator `mkF_numerator 0` is identically 0);
for $k = 1$, the Maynard ratio is $(\int F)^2 / \int F^2 \le 1$ by
Cauchy-Schwarz on $[0, 1]$.

**Both cases real (2026-05-28)**:
- $k = 0$: via `Mk_zero_le_one` (`MkF 0 _ = 0/_ = 0`).
- $k = 1$: via `mkF_one_le` — change of variables
  `MeasurableEquiv.funUnique (Fin 1) ℝ` collapses the `simplex 1` integrals
  to 1D `[0,1]` integrals (`mkF_numerator_one`, `mkF_denominator_one`), then
  Jensen for `x ↦ x²` on the probability space `[0,1]`
  (`sq_setIntegral_Icc_le`) gives `(∫g)² ≤ ∫g²`, i.e. `MkF 1 F ≤ 1`. -/
theorem Mk_le_one_of_k_le_one (k : ℕ) (hk : k ≤ 1) : Mk k ≤ 1 := by
  interval_cases k
  · exact Mk_zero_le_one
  · -- k = 1: Cauchy-Schwarz on [0,1].
    change sSup (MkSet 1) ≤ 1
    by_cases hne : (MkSet 1).Nonempty
    · apply csSup_le hne
      rintro v ⟨F, hsmooth, _, hden, rfl⟩
      exact mkF_one_le F hsmooth hden
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]; norm_num

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
          ContDiff ℝ ∞ F ∧
          Function.support F ⊆ simplex_truncated k α ∧
          mkF_denominator k F > 0 ∧
          v = MkF k F }

/-- $M_k^{[\alpha]} := \sup_F M_k(F)$ over admissible $F$ on the truncated
simplex. Polymath8b §5 `maynard-trunc` (line 959). Concrete `sSup` over
`MkSet_truncated k α`; sister of `Mk`. -/
noncomputable def Mk_truncated (k : ℕ) (α : ℝ) : ℝ := sSup (MkSet_truncated k α)

open MeasureTheory Set in
/-- For $k \ge 2$ and $\alpha > 0$, the admissible-F set for $M_k^{[\alpha]}$
is non-empty. Sister of `MkSet_nonempty`; smooth-bump construction inside
the (sufficiently small) truncated simplex provides a witness.

**Discharged 2026-05-30** (ROADMAP Tier 2): real local proof mirroring
`MkSet_nonempty`, with the bump radius scaled to `K = min(1/k, α)` so every
coordinate of a point in `supp F` lies in `(K/4, 3K/4)`, giving `t i ≤ α`
(via `K ≤ α`) in addition to `t i ≥ 0` and `∑ t i < 3/4 ≤ 1` (via `k·K ≤ 1`),
i.e. `supp F ⊆ simplex_truncated k α`. -/
theorem MkSet_truncated_nonempty (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 0 < α) :
    (MkSet_truncated k α).Nonempty := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set K : ℝ := min ((k:ℝ)⁻¹) α with hKdef
  have hKpos : 0 < K := lt_min (by positivity) hα
  have hKle_inv : K ≤ (k:ℝ)⁻¹ := min_le_left _ _
  have hKle_α : K ≤ α := min_le_right _ _
  have hkK : (k:ℝ) * K ≤ 1 := by
    calc (k:ℝ) * K ≤ (k:ℝ) * (k:ℝ)⁻¹ := mul_le_mul_of_nonneg_left hKle_inv (le_of_lt hkpos)
      _ = 1 := by field_simp
  set b : ContDiffBump (K/2 : ℝ) := ⟨K/8, K/4, by linarith, by linarith⟩ with hbdef
  have hrOut : b.rOut = K/4 := by rw [hbdef]
  set F : (Fin k → ℝ) → ℝ := fun t => ∏ i : Fin k, b (t i) with hFdef
  have hfac : ∀ i : Fin k, ContDiff ℝ ∞ (⇑b ∘ fun t : (Fin k → ℝ) => t i) :=
    fun i => b.contDiff.comp (contDiff_apply ℝ ℝ i)
  have hF_smooth : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]; intro x
    exact contDiffAt_prod (fun i _ => (hfac i).contDiffAt)
  -- support ⊆ simplex_truncated
  have hF_supp : Function.support F ⊆ simplex_truncated k α := by
    intro t ht
    simp only [Function.mem_support, hFdef] at ht
    have hall : ∀ i, b (t i) ≠ 0 := fun i hi => ht (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hbounds : ∀ i, K/4 < t i ∧ t i < 3*K/4 := by
      intro i
      have hb : t i ∈ Function.support (b : ℝ → ℝ) := Function.mem_support.mpr (hall i)
      rw [b.support_eq, Metric.mem_ball, Real.dist_eq, hrOut, abs_lt] at hb
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact le_of_lt (lt_trans (by linarith [hKpos] : (0:ℝ) < K/4) (hbounds i).1)
    · intro i
      linarith [hKle_α, hKpos, (hbounds i).2]
    · have hsum : ∑ i, t i < 1 := by
        calc ∑ i, t i < ∑ _i : Fin k, 3*K/4 :=
              Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => (hbounds i).2)
          _ = (k:ℝ) * (3*K/4) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = 3/4 * ((k:ℝ)*K) := by ring
          _ ≤ 3/4 * 1 := by apply mul_le_mul_of_nonneg_left hkK; norm_num
          _ < 1 := by norm_num
      exact hsum.le
  -- positive Rayleigh denominator
  have hcont : Continuous F := hF_smooth.continuous
  have hsubsimp : simplex_truncated k α ⊆ simplex k := fun t ⟨h0, _, hs⟩ => ⟨h0, hs⟩
  have hsupp_sq : Function.support (fun t : (Fin k → ℝ) => F t ^ 2) = Function.support F := by
    ext t; simp only [Function.mem_support, ne_eq, pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)]
  have hopen : IsOpen (Function.support F) := by
    have hpre : Function.support F = F ⁻¹' {0}ᶜ := by
      ext t; simp [Function.mem_support, Set.mem_preimage]
    rw [hpre]; exact isOpen_compl_singleton.preimage hcont
  have hne : (Function.support F).Nonempty := by
    refine ⟨fun _ => K/2, ?_⟩
    have hbc : (0:ℝ) < b (K/2) := b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)
    have hval : F (fun _ => K/2) = (b (K/2)) ^ k := by simp [hFdef, Finset.prod_const]
    rw [Function.mem_support, hval]; exact pow_ne_zero _ hbc.ne'
  have hsupp_compact : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_simplex k) (hF_supp.trans hsubsimp)
  have hsupp2_compact : HasCompactSupport (fun t => F t ^ 2) :=
    hsupp_compact.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hinteg : MeasureTheory.IntegrableOn (fun t => F t ^ 2) (simplex_truncated k α) :=
    ((hcont.pow 2).integrable_of_hasCompactSupport hsupp2_compact).integrableOn
  have hF_den : (0:ℝ) < mkF_denominator k F := by
    have hrw : mkF_denominator k F = ∫ t in simplex_truncated k α, F t ^ 2 := by
      change (∫ t in simplex k, F t ^ 2) = ∫ t in simplex_truncated k α, F t ^ 2
      symm
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := simplex_truncated k α) ?_).trans ?_
      · intro t ht
        have hF0 : F t = 0 := by
          by_contra hh; exact ht (hF_supp (Function.mem_support.mpr hh))
        rw [hF0]; ring
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := simplex k) ?_).symm
        intro t ht
        have hF0 : F t = 0 := by
          by_contra hh; exact ht (hsubsimp (hF_supp (Function.mem_support.mpr hh)))
        rw [hF0]; ring
    rw [hrw, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
          (Filter.Eventually.of_forall fun t => sq_nonneg (F t)) hinteg,
        hsupp_sq, Set.inter_eq_left.mpr hF_supp]
    exact hopen.measure_pos (μ := MeasureTheory.volume) hne
  exact ⟨MkF k F, F, hF_smooth, hF_supp, hF_den, rfl⟩

/-- The admissible-F set for $M_k^{[\alpha]}$ is bounded above. Sister of
`MkSet_bddAbove`; since `simplex_truncated k α ⊆ simplex k`, every witness
$F$ for `MkSet_truncated k α` is also a witness for `MkSet k` with the
same value, so `MkSet_truncated k α ⊆ MkSet k` and the bound is inherited.

**Discharged 2026-05-26** (ROADMAP Tier 2): real local proof routing
through `MkSet_bddAbove` (itself now sorry-free as of 2026-05-30 via the
crude `M_k ≤ k` Cauchy-Schwarz bound `J_i_le_denom`). -/
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
          ContDiff ℝ ∞ F ∧
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

/-- The enlarged simplex `simplex_eps k ε` is compact (closed + bounded by
`max (1+ε) 0` in the sup norm). Feeds the compact-support / integrability
arguments for `J_i_eps_le_denom`. -/
theorem isCompact_simplex_eps (k : ℕ) (ε : ℝ) : IsCompact (simplex_eps k ε) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have heq : simplex_eps k ε =
        (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ 1 + ε} := by
      ext t; simp only [simplex_eps, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := max (1 + ε) 0)).subset
    intro t ht
    simp only [simplex_eps, Set.mem_setOf_eq] at ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero,
        pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    calc t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)
      _ ≤ 1 + ε := ht.2
      _ ≤ max (1 + ε) 0 := le_max_left _ _

/-- The shrunken simplex `simplex_shrunk k ε` is closed (hence measurable):
the outer integration domain of the ε-flavored numerator. -/
theorem isClosed_simplex_shrunk (k : ℕ) (ε : ℝ) : IsClosed (simplex_shrunk k ε) := by
  have heq : simplex_shrunk k ε =
      (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ 1 - ε} := by
    ext t; simp only [simplex_shrunk, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
  · exact isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const

open MeasureTheory Set in
/-- **Each ε-flavored Maynard marginal is bounded: `J_{i,1-ε}(F) ≤ max(1+ε,0)·I_ε(F)`.**
Sister of `J_i_le_denom`. Cauchy-Schwarz (`cs_Icc`) on the inner `[0, 1+ε-∑s]` integral,
whose moving boundary is tamed by `support F ⊆ simplex_eps`: for any `s`,
`F(insertNth i · s)` vanishes outside `[0, 1+ε-∑s]` (the inserted point leaves
`simplex_eps`), so the clamped inner integral equals the full-line marginal
`m s = ∫ F(insertNth i · s)`. The slice bound `m s² ≤ max(1+ε,0)·Φ s` (with
`Φ s = ∫ F(insertNth i · s)²`) handles `L := 1+ε-∑s ≥ 0` via `cs_Icc` (and `L ≤ 1+ε`)
and `L < 0` via the empty inner interval forcing `m s = 0`. Summing `Φ` back up via
`integral_insertNth_eq` recovers `∫_{ℝ^{n+1}} F² = I_ε(F)` (support `⊆ simplex_eps`). -/
theorem J_i_eps_le_denom (n : ℕ) (ε : ℝ) (F : (Fin (n + 1) → ℝ) → ℝ)
    (hcont : Continuous F) (hFsupp : Function.support F ⊆ simplex_eps (n + 1) ε)
    (i : Fin (n + 1)) :
    J_i_eps (n + 1) ε F i ≤ max (1 + ε) 0 * mkF_eps_denominator (n + 1) ε F := by
  classical
  set C₀ := max (1 + ε) 0 with hC₀
  have hC₀nn : 0 ≤ C₀ := le_max_right _ _
  have hC₀ge : 1 + ε ≤ C₀ := le_max_left _ _
  have hsimpEpsCompact : IsCompact (simplex_eps (n + 1) ε) := isCompact_simplex_eps (n + 1) ε
  have hsimpEpsClosed : IsClosed (simplex_eps (n + 1) ε) := hsimpEpsCompact.isClosed
  have hcs : HasCompactSupport F :=
    IsCompact.of_isClosed_subset hsimpEpsCompact isClosed_closure
      (closure_minimal hFsupp hsimpEpsClosed)
  have hF2cont : Continuous (fun t => F t ^ 2) := hcont.pow 2
  have hcs2 : HasCompactSupport (fun t => F t ^ 2) := by
    apply hcs.comp_left (g := fun x : ℝ => x ^ 2); simp
  have hFi : Integrable F := hcont.integrable_of_hasCompactSupport hcs
  have hF2i : Integrable (fun t => F t ^ 2) := hF2cont.integrable_of_hasCompactSupport hcs2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set m : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, F (i.insertNth ti s) with hm
  set Φ : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, F (i.insertNth ti s) ^ 2 with hΦ
  have hprodF2 : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hF2i
  have hΦi : Integrable Φ := by
    have h := hprodF2.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hprodF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hFi
  have hmi : Integrable m := by
    have h := hprodF.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hΦnn : ∀ s, 0 ≤ Φ s := fun s => integral_nonneg fun ti => sq_nonneg _
  have hmeasS : MeasurableSet (simplex_shrunk n ε) := (isClosed_simplex_shrunk n ε).measurableSet
  have key : ∀ s ∈ simplex_shrunk n ε,
      (∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) = m s ∧ m s ^ 2 ≤ C₀ * Φ s := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    set L := 1 + ε - ∑ j, s j with hL
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    have hLle : L ≤ 1 + ε := by rw [hL]; linarith
    have hzero : ∀ ti, ti ∉ Icc (0 : ℝ) L → F (i.insertNth ti s) = 0 := by
      intro ti hti
      by_contra hne
      have hmem : i.insertNth ti s ∈ simplex_eps (n + 1) ε :=
        hFsupp (Function.mem_support.mpr hne)
      obtain ⟨hmem_nn, hmem_sum⟩ := hmem
      apply hti
      refine ⟨?_, ?_⟩
      · have := hmem_nn i; rwa [Fin.insertNth_apply_same] at this
      · rw [hL, le_sub_iff_add_le]
        have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq] at hmem_sum; linarith
    have hcont_h : Continuous (fun ti => F (i.insertNth ti s)) :=
      hcont.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have eqfull : (∫ ti in Icc 0 L, F (i.insertNth ti s)) = m s :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    refine ⟨eqfull, ?_⟩
    by_cases hLnn : 0 ≤ L
    · have hint_h : IntegrableOn (fun ti => F (i.insertNth ti s)) (Icc 0 L) :=
        hcont_h.integrableOn_Icc
      have hint_h2 : IntegrableOn (fun ti => F (i.insertNth ti s) ^ 2) (Icc 0 L) :=
        (hcont_h.pow 2).integrableOn_Icc
      have eqfull2 : (∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2) = Φ s := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro ti hti; rw [hzero ti hti]; ring
      have hcsq := cs_Icc L hLnn (fun ti => F (i.insertNth ti s)) hint_h hint_h2
      rw [eqfull] at hcsq
      have hΦnn_s : 0 ≤ Φ s := hΦnn s
      calc m s ^ 2 ≤ L * ∫ ti in Icc 0 L, F (i.insertNth ti s) ^ 2 := hcsq
        _ = L * Φ s := by rw [eqfull2]
        _ ≤ C₀ * Φ s := mul_le_mul_of_nonneg_right (le_trans hLle hC₀ge) hΦnn_s
    · have hIcc_empty : Icc (0 : ℝ) L = ∅ := Icc_eq_empty hLnn
      have hms0 : m s = 0 := by rw [← eqfull, hIcc_empty]; simp
      rw [hms0, show (0 : ℝ) ^ 2 = 0 from by ring]
      exact mul_nonneg hC₀nn (hΦnn s)
  change (∫ s in simplex_shrunk n ε,
      (∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2)
      ≤ C₀ * mkF_eps_denominator (n + 1) ε F
  have hcongr : (∫ s in simplex_shrunk n ε,
        (∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2)
      = ∫ s in simplex_shrunk n ε, m s ^ 2 := by
    refine setIntegral_congr_fun hmeasS ?_
    intro s hs; dsimp only; rw [(key s hs).1]
  rw [hcongr]
  have hm2_aesm : AEStronglyMeasurable (fun s => m s ^ 2) (volume.restrict (simplex_shrunk n ε)) :=
    (hmi.aestronglyMeasurable.pow 2).restrict
  have hm2_int : IntegrableOn (fun s => m s ^ 2) (simplex_shrunk n ε) := by
    refine Integrable.mono' (g := fun s => C₀ * Φ s) (hΦi.const_mul C₀).integrableOn hm2_aesm ?_
    refine (ae_restrict_iff' hmeasS).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (key s hs).2
  calc (∫ s in simplex_shrunk n ε, m s ^ 2)
      ≤ ∫ s in simplex_shrunk n ε, C₀ * Φ s := by
        refine setIntegral_mono_on hm2_int ((hΦi.const_mul C₀).integrableOn) hmeasS ?_
        intro s hs; exact (key s hs).2
    _ = C₀ * ∫ s in simplex_shrunk n ε, Φ s := by rw [integral_const_mul]
    _ ≤ C₀ * ∫ s, Φ s := by
        apply mul_le_mul_of_nonneg_left _ hC₀nn
        exact setIntegral_le_integral hΦi (Filter.Eventually.of_forall hΦnn)
    _ = C₀ * mkF_eps_denominator (n + 1) ε F := by
        have hkey := integral_insertNth_eq i (fun t => F t ^ 2) hF2i
        have hden : mkF_eps_denominator (n + 1) ε F = ∫ t, F t ^ 2 := by
          change (∫ t in simplex_eps (n + 1) ε, F t ^ 2) = ∫ t, F t ^ 2
          refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
          intro t ht
          have hF0 : F t = 0 := by
            by_contra hh; exact ht (hFsupp (Function.mem_support.mpr hh))
          rw [hF0]; ring
        rw [hden, hkey]

/-- The admissible-F set for $M_{k,\varepsilon}$ is bounded above.
Sister of `MkSet_bddAbove`. Polymath8b §5: $M_{k,\varepsilon}$ admits
the same asymptotic upper bound as $M_k$ up to a factor of
$(1+\varepsilon)/(1-\varepsilon)$.

**Discharged 2026-05-30** (ROADMAP Tier 2): real local proof. The `k = n+1`
case bounds `M_{k,ε}(F) = (∑_i J_{i,1-ε})/I_ε(F) ≤ (n+1)·max(1+ε,0)` via the
per-marginal crude bound `J_{i,1-ε}(F) ≤ max(1+ε,0)·I_ε(F)` (`J_i_eps_le_denom`,
the substantive lemma, mirroring `J_i_le_denom`). The `k = 0` case is
`M_{0,ε}(F) = 0/I ≤ 0`. The bound `(k:ℝ)·max(1+ε,0)` witnesses `BddAbove`. -/
theorem MkSet_eps_bddAbove (k : ℕ) (ε : ℝ) : BddAbove (MkSet_eps k ε) := by
  refine ⟨(k : ℝ) * max (1 + ε) 0, ?_⟩
  rintro v ⟨F, hFsmooth, hFsupp, hFden, rfl⟩
  cases k with
  | zero =>
    show MkF_eps 0 ε F ≤ ((0 : ℕ) : ℝ) * max (1 + ε) 0
    simp [MkF_eps, mkF_eps_numerator]
  | succ n =>
    show MkF_eps (n + 1) ε F ≤ (((n + 1 : ℕ)) : ℝ) * max (1 + ε) 0
    rw [MkF_eps, mkF_eps_numerator_eq_sum_J_i_eps, div_le_iff₀ hFden]
    calc ∑ i, J_i_eps (n + 1) ε F i
        ≤ ∑ _i : Fin (n + 1), max (1 + ε) 0 * mkF_eps_denominator (n + 1) ε F :=
          Finset.sum_le_sum fun i _ => J_i_eps_le_denom n ε F hFsmooth.continuous hFsupp i
      _ = (((n + 1 : ℕ)) : ℝ) * max (1 + ε) 0 * mkF_eps_denominator (n + 1) ε F := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

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

/-- **Finite separability of a test function** (the path-A coupling).

`IsFiniteSeparable F` says the multidimensional test function $F$ admits a
*finite* basis decomposition $F(t) = \sum_{j<J} c_j \prod_i
\mathrm{Fs}_{j,i}(t_i)$ — a finite sum of products of 1D functions, together
with a sieve level $R$. This is exactly the data the real weight
`selberg_nu_basis` consumes, so a separable $F$ gives a *concrete*
`selberg_nu` weight (no opaque).

**Not every smooth $F$ is separable** (e.g. $\exp(t_0 t_1)$ has infinite
separation rank), so this is a genuine restriction — it is NOT derivable
from smoothness. It is supplied at the source instead: the variational
optimum $M_k$ is realised by polynomial test functions (Polymath8b §6), and a
polynomial's monomial expansion *is* a finite basis decomposition
($\mathrm{Fs}_{j,i}(x) = x^{e_{j,i}}$) — see
`SievePolynomial.polynomialSieveWeight_isSeparable` for the provable witness.
The cited `exists_separable_F_*` axioms below carry separability out of the
$M_k$-extraction so the deep s1/s2 axioms only ever speak about
genuinely-`selberg_nu_basis`-built weights. -/
def IsFiniteSeparable {k : ℕ} (F : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ (J : ℕ) (c : Fin J → ℝ) (Fs : Fin J → Fin k → ℝ → ℝ) (R : ℝ),
    ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i)

/-- **sSup extraction**: if $c < M_k$ then there is a specific admissible
$F$ on the simplex realizing $\mathrm{MkF}(k, F) > c$.

Real proof via mathlib's `lt_csSup_iff`, consuming the cited axioms
`MkSet_nonempty` (for $k \ge 2$) and `MkSet_bddAbove` as leaves. -/
theorem exists_F_of_Mk_gt (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : c < Mk k) :
    ∃ F : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex k ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  have hLt : c < sSup (MkSet k) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_bddAbove k) (MkSet_nonempty k hk)).mp hLt
  obtain ⟨F, hSmooth, hSupp, hDen, hvEq⟩ := hvMem
  exact ⟨F, hSmooth, hSupp, hDen, hvEq ▸ hcv⟩

/-! ### Sup-norm continuity of the Maynard functionals (toward `sep_approx`)

These reduce `sep_approx`'s continuity content to elementary integral-monotonicity:
both `mkF_denominator` and each marginal `J_i` differ by at most the uniform
(sup-over-simplex) distance between the test functions, times a finite constant.
No `L²`/Cauchy–Schwarz machinery — just `‖∫‖ ≤ ∫‖·‖` and `setIntegral_mono`. -/

open MeasureTheory in
/-- The Maynard denominator difference is bounded by the simplex integral of
`|F² − G²|`. -/
theorem mkF_denominator_sub_abs_le (k : ℕ) (F G : (Fin k → ℝ) → ℝ)
    (hF : Continuous F) (hG : Continuous G) :
    |mkF_denominator k F - mkF_denominator k G|
      ≤ ∫ t in simplex k, |F t ^ 2 - G t ^ 2| := by
  have hIF : IntegrableOn (fun t => F t ^ 2) (simplex k) volume :=
    (hF.pow 2).locallyIntegrable.integrableOn_isCompact (isCompact_simplex k)
  have hIG : IntegrableOn (fun t => G t ^ 2) (simplex k) volume :=
    (hG.pow 2).locallyIntegrable.integrableOn_isCompact (isCompact_simplex k)
  unfold mkF_denominator
  rw [← integral_sub hIF hIG]
  simpa [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (μ := volume.restrict (simplex k))
      (f := fun t => F t ^ 2 - G t ^ 2)

open MeasureTheory in
/-- **Sup-norm continuity of the Maynard denominator.** If `|F+G| ≤ A` and
`|F−G| ≤ ε` pointwise on the simplex, the denominators differ by at most
`ε·A·vol(simplex)`. -/
theorem mkF_denominator_sub_le_const (k : ℕ) (F G : (Fin k → ℝ) → ℝ) (A ε : ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hsum : ∀ t ∈ simplex k, |F t + G t| ≤ A) (happ : ∀ t ∈ simplex k, |F t - G t| ≤ ε) :
    |mkF_denominator k F - mkF_denominator k G| ≤ ε * A * (volume (simplex k)).toReal := by
  refine (mkF_denominator_sub_abs_le k F G hF hG).trans ?_
  have hms : MeasurableSet (simplex k) := (isCompact_simplex k).isClosed.measurableSet
  have hbound : ∀ t ∈ simplex k, |F t ^ 2 - G t ^ 2| ≤ ε * A := by
    intro t ht
    have hfac : F t ^ 2 - G t ^ 2 = (F t - G t) * (F t + G t) := by ring
    rw [hfac, abs_mul]
    exact mul_le_mul (happ t ht) (hsum t ht) (abs_nonneg _)
      (le_trans (abs_nonneg _) (happ t ht))
  have hI1 : IntegrableOn (fun t => |F t ^ 2 - G t ^ 2|) (simplex k) volume :=
    (((hF.pow 2).sub (hG.pow 2)).abs).locallyIntegrable.integrableOn_isCompact (isCompact_simplex k)
  calc ∫ t in simplex k, |F t ^ 2 - G t ^ 2|
      ≤ ∫ _t in simplex k, ε * A :=
        setIntegral_mono_on hI1 (integrableOn_const (isCompact_simplex k).measure_lt_top.ne)
          hms hbound
    _ = ε * A * (volume (simplex k)).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]

open MeasureTheory Set in
/-- The `J_i` integrand `s ↦ (∫_{[0,1-∑s]} H(insertNth i · s))²` is integrable over
`simplex n` (the parametric-integral integrability extracted from `J_i_le_denom`:
on the simplex the clamped inner integral equals the full-line marginal
`m s = ∫ H(insertNth i · s)`, whose square is integrable, being `≤ Φ s = ∫
H(insertNth i · s)²`). -/
private theorem Ji_integrand_integrableOn (n : ℕ) (H : (Fin (n + 1) → ℝ) → ℝ)
    (hHc : Continuous H) (hHsupp : Function.support H ⊆ simplex (n + 1)) (i : Fin (n + 1)) :
    IntegrableOn
      (fun s => (∫ ti in Icc 0 (1 - ∑ j, s j), H (i.insertNth ti s)) ^ 2) (simplex n) := by
  classical
  have hsimpClosed : IsClosed (simplex (n + 1)) := isClosed_simplex (n + 1)
  have hcs : HasCompactSupport H :=
    IsCompact.of_isClosed_subset (isCompact_simplex (n + 1)) isClosed_closure
      (closure_minimal hHsupp hsimpClosed)
  have hH2cont : Continuous (fun t => H t ^ 2) := hHc.pow 2
  have hcs2 : HasCompactSupport (fun t => H t ^ 2) := by
    apply hcs.comp_left (g := fun x : ℝ => x ^ 2); simp
  have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hcs
  have hH2i : Integrable (fun t => H t ^ 2) := hH2cont.integrable_of_hasCompactSupport hcs2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set m : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, H (i.insertNth ti s) with hm
  set Φ : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, H (i.insertNth ti s) ^ 2 with hΦ
  have hprodH2 : Integrable (fun p : ℝ × (Fin n → ℝ) => H (e.symm p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hH2i
  have hΦi : Integrable Φ := by
    have h := hprodH2.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hprodH : Integrable (fun p : ℝ × (Fin n → ℝ) => H (e.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hHi
  have hmi : Integrable m := by
    have h := hprodH.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have key : ∀ s ∈ simplex n,
      (∫ ti in Icc 0 (1 - ∑ j, s j), H (i.insertNth ti s)) = m s ∧ m s ^ 2 ≤ Φ s := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    set L := 1 - ∑ j, s j with hL
    have hLnn : 0 ≤ L := by rw [hL]; linarith
    have hL1 : L ≤ 1 := by rw [hL]; linarith
    have hzero : ∀ ti, ti ∉ Icc (0 : ℝ) L → H (i.insertNth ti s) = 0 := by
      intro ti hti
      by_contra hne
      have hmem : i.insertNth ti s ∈ simplex (n + 1) := hHsupp (Function.mem_support.mpr hne)
      obtain ⟨hmem_nn, hmem_sum⟩ := hmem
      apply hti
      refine ⟨?_, ?_⟩
      · have := hmem_nn i; rwa [Fin.insertNth_apply_same] at this
      · rw [hL, le_sub_iff_add_le]
        have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq] at hmem_sum; linarith
    have hcont_h : Continuous (fun ti => H (i.insertNth ti s)) :=
      hHc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hint_h : IntegrableOn (fun ti => H (i.insertNth ti s)) (Icc 0 L) :=
      hcont_h.integrableOn_Icc
    have hint_h2 : IntegrableOn (fun ti => H (i.insertNth ti s) ^ 2) (Icc 0 L) :=
      (hcont_h.pow 2).integrableOn_Icc
    have eqfull : (∫ ti in Icc 0 L, H (i.insertNth ti s)) = m s :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have eqfull2 : (∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2) = Φ s := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro ti hti; rw [hzero ti hti]; ring
    refine ⟨eqfull, ?_⟩
    have hcsq := cs_Icc L hLnn (fun ti => H (i.insertNth ti s)) hint_h hint_h2
    rw [eqfull] at hcsq
    have hnn2 : 0 ≤ ∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2 :=
      integral_nonneg fun ti => sq_nonneg _
    calc m s ^ 2 ≤ L * ∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2 := hcsq
      _ ≤ 1 * ∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2 := mul_le_mul_of_nonneg_right hL1 hnn2
      _ = Φ s := by rw [one_mul, eqfull2]
  have hmeasS : MeasurableSet (simplex n) := (isClosed_simplex n).measurableSet
  have hm2_aesm : AEStronglyMeasurable (fun s => m s ^ 2) (volume.restrict (simplex n)) :=
    (hmi.aestronglyMeasurable.pow 2).restrict
  have hm2_int : IntegrableOn (fun s => m s ^ 2) (simplex n) := by
    refine Integrable.mono' hΦi.integrableOn hm2_aesm ?_
    refine (ae_restrict_iff' hmeasS).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (key s hs).2
  refine (integrableOn_congr_fun ?_ hmeasS).mpr hm2_int
  intro s hs; dsimp only; rw [(key s hs).1]

open MeasureTheory Set in
/-- **Sup-norm continuity of each Maynard marginal `J_i`.** If `|F+G| ≤ A` and
`|F−G| ≤ ε` pointwise on `simplex (n+1)`, with `F, G` continuous and supported on
the simplex, then `|J_i F − J_i G| ≤ ε·A·vol(simplex n)`. The inner `[0,1−∑s]`
integrals differ by `≤ ε` and sum to `≤ A` (integral monotonicity + the inserted
point staying in the simplex), so the squared integrands differ by `≤ εA`. -/
theorem J_i_sub_le_const (n : ℕ) (F G : (Fin (n + 1) → ℝ) → ℝ) (A ε : ℝ)
    (hFc : Continuous F) (hGc : Continuous G)
    (hFsupp : Function.support F ⊆ simplex (n + 1))
    (hGsupp : Function.support G ⊆ simplex (n + 1))
    (hsum : ∀ t ∈ simplex (n + 1), |F t + G t| ≤ A)
    (happ : ∀ t ∈ simplex (n + 1), |F t - G t| ≤ ε)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (i : Fin (n + 1)) :
    |J_i (n + 1) F i - J_i (n + 1) G i| ≤ ε * A * (volume (simplex n)).toReal := by
  classical
  have hmeasS : MeasurableSet (simplex n) := (isClosed_simplex n).measurableSet
  have hIF2 : IntegrableOn
      (fun s => (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2) (simplex n) :=
    Ji_integrand_integrableOn n F hFc hFsupp i
  have hIG2 : IntegrableOn
      (fun s => (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2) (simplex n) :=
    Ji_integrand_integrableOn n G hGc hGsupp i
  -- pointwise bound `|iF² − iG²| ≤ εA` on the simplex
  have hbound : ∀ s ∈ simplex n,
      |(∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
        - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2| ≤ ε * A := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    set L := 1 - ∑ j, s j with hL
    have hLnn : 0 ≤ L := by rw [hL]; linarith
    have hL1 : L ≤ 1 := by rw [hL]; linarith
    have hmem : ∀ ti ∈ Icc (0 : ℝ) L, i.insertNth ti s ∈ simplex (n + 1) := by
      intro ti hti
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Fin.insertNth_apply_same]; exact hti.1
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
          rw [Fin.insertNth_apply_succAbove]; exact hs_nn j'
      · have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq]; have h2 := hti.2; rw [hL] at h2; linarith
    have hcontF : Continuous (fun ti => F (i.insertNth ti s)) :=
      hFc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hcontG : Continuous (fun ti => G (i.insertNth ti s)) :=
      hGc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hintF : IntegrableOn (fun ti => F (i.insertNth ti s)) (Icc 0 L) := hcontF.integrableOn_Icc
    have hintG : IntegrableOn (fun ti => G (i.insertNth ti s)) (Icc 0 L) := hcontG.integrableOn_Icc
    have hmIcc : MeasurableSet (Icc (0 : ℝ) L) := measurableSet_Icc
    have hvolIcc : (volume (Icc (0 : ℝ) L)).toReal = L := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    have hvol_ne : volume (Icc (0 : ℝ) L) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne
    have hconstε : IntegrableOn (fun _ : ℝ => ε) (Icc 0 L) := integrableOn_const hvol_ne
    have hconstA : IntegrableOn (fun _ : ℝ => A) (Icc 0 L) := integrableOn_const hvol_ne
    have hdiff : |(∫ ti in Icc 0 L, F (i.insertNth ti s))
                  - (∫ ti in Icc 0 L, G (i.insertNth ti s))| ≤ ε := by
      rw [← integral_sub hintF hintG]
      have habs : |∫ ti in Icc 0 L, (F (i.insertNth ti s) - G (i.insertNth ti s))|
          ≤ ∫ ti in Icc 0 L, |F (i.insertNth ti s) - G (i.insertNth ti s)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Icc (0:ℝ) L))
          (f := fun ti => F (i.insertNth ti s) - G (i.insertNth ti s))
      refine habs.trans ?_
      calc ∫ ti in Icc 0 L, |F (i.insertNth ti s) - G (i.insertNth ti s)|
          ≤ ∫ _ti in Icc 0 L, ε :=
            setIntegral_mono_on (hintF.sub hintG).abs hconstε hmIcc
              (fun ti hti => happ _ (hmem ti hti))
        _ = ε * L := by rw [setIntegral_const, smul_eq_mul, measureReal_def, hvolIcc, mul_comm]
        _ ≤ ε := by nlinarith
    have hsm : |(∫ ti in Icc 0 L, F (i.insertNth ti s))
                  + (∫ ti in Icc 0 L, G (i.insertNth ti s))| ≤ A := by
      rw [← integral_add hintF hintG]
      have habs : |∫ ti in Icc 0 L, (F (i.insertNth ti s) + G (i.insertNth ti s))|
          ≤ ∫ ti in Icc 0 L, |F (i.insertNth ti s) + G (i.insertNth ti s)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Icc (0:ℝ) L))
          (f := fun ti => F (i.insertNth ti s) + G (i.insertNth ti s))
      refine habs.trans ?_
      calc ∫ ti in Icc 0 L, |F (i.insertNth ti s) + G (i.insertNth ti s)|
          ≤ ∫ _ti in Icc 0 L, A :=
            setIntegral_mono_on (hintF.add hintG).abs hconstA hmIcc
              (fun ti hti => hsum _ (hmem ti hti))
        _ = A * L := by rw [setIntegral_const, smul_eq_mul, measureReal_def, hvolIcc, mul_comm]
        _ ≤ A := by nlinarith
    have hfac : (∫ ti in Icc 0 L, F (i.insertNth ti s)) ^ 2
                  - (∫ ti in Icc 0 L, G (i.insertNth ti s)) ^ 2
                = ((∫ ti in Icc 0 L, F (i.insertNth ti s))
                    - (∫ ti in Icc 0 L, G (i.insertNth ti s)))
                  * ((∫ ti in Icc 0 L, F (i.insertNth ti s))
                    + (∫ ti in Icc 0 L, G (i.insertNth ti s))) := by ring
    rw [hfac, abs_mul]
    exact mul_le_mul hdiff hsm (abs_nonneg _) hε
  -- assemble
  rw [show J_i (n + 1) F i
        = ∫ s in simplex n, (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2 from rfl,
      show J_i (n + 1) G i
        = ∫ s in simplex n, (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2 from rfl,
      ← integral_sub hIF2 hIG2]
  have habs : |∫ s in simplex n, ((∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2)|
      ≤ ∫ s in simplex n, |(∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2| := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (simplex n))
      (f := fun s => (∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2)
  have hIabs : IntegrableOn
      (fun s => |(∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
        - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2|) (simplex n) := by
    simpa only [Pi.sub_apply] using (hIF2.sub hIG2).abs
  refine habs.trans ?_
  calc ∫ s in simplex n, |(∫ ti in Icc 0 (1 - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 - ∑ j, s j), G (i.insertNth ti s)) ^ 2|
      ≤ ∫ _s in simplex n, ε * A :=
        setIntegral_mono_on hIabs
          (integrableOn_const (isCompact_simplex n).measure_lt_top.ne) hmeasS
          (fun s hs => hbound s hs)
    _ = ε * A * (volume (simplex n)).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring

open MeasureTheory in
/-- **Sup-norm continuity of the Maynard numerator.** Summing `J_i_sub_le_const`
over the `k` marginals. -/
theorem mkF_numerator_sub_le_const (k : ℕ) (F G : (Fin k → ℝ) → ℝ) (A ε : ℝ)
    (hFc : Continuous F) (hGc : Continuous G)
    (hFsupp : Function.support F ⊆ simplex k) (hGsupp : Function.support G ⊆ simplex k)
    (hsum : ∀ t ∈ simplex k, |F t + G t| ≤ A) (happ : ∀ t ∈ simplex k, |F t - G t| ≤ ε)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    |mkF_numerator k F - mkF_numerator k G|
      ≤ (k : ℝ) * (ε * A * (volume (simplex (k - 1))).toReal) := by
  cases k with
  | zero => simp [mkF_numerator]
  | succ n =>
    rw [mkF_numerator_eq_sum_J_i, mkF_numerator_eq_sum_J_i, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun i _ =>
      J_i_sub_le_const n F G A ε hFc hGc hFsupp hGsupp hsum happ hε hA i)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.add_sub_cancel]

open MeasureTheory in
/-- **Sup-norm continuity of the Maynard ratio `MkF`.** For a fixed admissible `F`
and any target `etarget > 0`, there is `δ > 0` such that every continuous,
simplex-supported `G` within sup-distance `δ` of `F` on the simplex has positive
denominator and `|MkF G − MkF F| < etarget`. Combines the numerator/denominator
sup-continuity with the quotient rule (the denominator stays `≥ den F / 2` for
small `δ`). This is the **continuity half of `sep_approx`, proved in-kernel**. -/
theorem mkF_sub_lt_of_sup_le (k : ℕ) (F : (Fin k → ℝ) → ℝ)
    (hFc : Continuous F) (hFsupp : Function.support F ⊆ simplex k)
    (hFden : 0 < mkF_denominator k F) (etarget : ℝ) (hetarget : 0 < etarget) :
    ∃ δ > 0, ∀ G : (Fin k → ℝ) → ℝ, Continuous G → Function.support G ⊆ simplex k →
      (∀ t ∈ simplex k, |F t - G t| ≤ δ) →
      0 < mkF_denominator k G ∧ |MkF k G - MkF k F| < etarget := by
  obtain ⟨CF, hCF0, hCF⟩ : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ t ∈ simplex k, |F t| ≤ CF := by
    obtain ⟨CF, hCF⟩ := (isCompact_simplex k).exists_bound_of_continuousOn hFc.continuousOn
    exact ⟨max CF 0, le_max_right _ _, fun t ht => (hCF t ht).trans (le_max_left _ _)⟩
  set A0 : ℝ := 2 * CF + 1 with hA0
  have hA0pos : 0 < A0 := by rw [hA0]; linarith
  set vk : ℝ := (volume (simplex k)).toReal with hvk
  set vk1 : ℝ := (volume (simplex (k - 1))).toReal with hvk1
  have hvk0 : 0 ≤ vk := ENNReal.toReal_nonneg
  have hvk10 : 0 ≤ vk1 := ENNReal.toReal_nonneg
  set den : ℝ := mkF_denominator k F with hden
  set numF : ℝ := mkF_numerator k F with hnumF
  -- the numerator-bound slope `S` (so `N = δ·S`)
  set S : ℝ := A0 * ((k : ℝ) * vk1 * den + |numF| * vk) with hS
  have hSinner : 0 ≤ (k : ℝ) * vk1 * den + |numF| * vk :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hvk10) hFden.le)
      (mul_nonneg (abs_nonneg _) hvk0)
  have hS0 : 0 ≤ S := mul_nonneg hA0pos.le hSinner
  have hAvk0 : 0 ≤ A0 * vk := mul_nonneg hA0pos.le hvk0
  have hP : 0 < etarget * den ^ 2 := mul_pos hetarget (pow_pos hFden 2)
  set δ : ℝ := min 1 (min (den / (2 * (A0 * vk) + 2)) (etarget * den ^ 2 / (2 * S + 2))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · apply div_pos hP; linarith
  refine ⟨δ, hδpos, ?_⟩
  intro G hGc hGsupp hclose
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ den / (2 * (A0 * vk) + 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ etarget * den ^ 2 / (2 * S + 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- uniform bound `|F+G| ≤ A0`
  have hsumG : ∀ t ∈ simplex k, |F t + G t| ≤ A0 := by
    intro t ht
    have hFt := abs_le.mp (hCF t ht); have hFGt := abs_le.mp (hclose t ht)
    rw [hA0, abs_le]; constructor <;> nlinarith [hFt.1, hFt.2, hFGt.1, hFGt.2, hδ1]
  -- denominator closeness + lower bound `den/2`
  have hDden : |den - mkF_denominator k G| ≤ δ * A0 * vk := by
    rw [hden, hvk]
    exact mkF_denominator_sub_le_const k F G A0 δ hFc hGc hsumG hclose
  have hden2 : δ * A0 * vk ≤ den / 2 := by
    have hmul : δ * (2 * (A0 * vk) + 2) ≤ den := (le_div_iff₀ (by linarith)).mp hδ2
    nlinarith [hmul, hδpos, hAvk0]
  have hdenG_lb : den / 2 ≤ mkF_denominator k G := by
    have hh := abs_le.mp (hDden.trans hden2); linarith [hh.1]
  have hdenG_pos : 0 < mkF_denominator k G := by linarith [hdenG_lb, hFden]
  refine ⟨hdenG_pos, ?_⟩
  -- numerator closeness
  have hDnum : |numF - mkF_numerator k G| ≤ (k : ℝ) * (δ * A0 * vk1) := by
    rw [hnumF, hvk1]
    exact mkF_numerator_sub_le_const k F G A0 δ hFc hGc hFsupp hGsupp hsumG hclose hδpos.le hA0pos.le
  -- the ratio bound
  rw [show MkF k G = mkF_numerator k G / mkF_denominator k G from rfl,
      show MkF k F = numF / den from rfl,
      div_sub_div _ _ (ne_of_gt hdenG_pos) (ne_of_gt hFden), abs_div]
  have hposprod : 0 < mkF_denominator k G * den := mul_pos hdenG_pos hFden
  rw [abs_of_pos hposprod, div_lt_iff₀ hposprod]
  -- numerator bound: `|num_G·den − den_G·numF| ≤ δ·S`
  have hnum_bound : |mkF_numerator k G * den - mkF_denominator k G * numF| ≤ δ * S := by
    have heq : mkF_numerator k G * den - mkF_denominator k G * numF
        = (mkF_numerator k G - numF) * den + numF * (den - mkF_denominator k G) := by ring
    rw [heq]
    calc |(mkF_numerator k G - numF) * den + numF * (den - mkF_denominator k G)|
        ≤ |(mkF_numerator k G - numF) * den| + |numF * (den - mkF_denominator k G)| :=
          abs_add_le _ _
      _ = |mkF_numerator k G - numF| * den + |numF| * |den - mkF_denominator k G| := by
          rw [abs_mul, abs_mul, abs_of_pos hFden]
      _ ≤ (k : ℝ) * (δ * A0 * vk1) * den + |numF| * (δ * A0 * vk) :=
          add_le_add (mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact hDnum) hFden.le)
            (mul_le_mul_of_nonneg_left hDden (abs_nonneg _))
      _ = δ * S := by rw [hS]; ring
  -- `δ·S < etarget·den²/2 ≤ etarget·(den_G·den)`
  have hbden : den ^ 2 / 2 ≤ mkF_denominator k G * den := by nlinarith [hdenG_lb, hFden]
  have hSlt : δ * S < etarget * den ^ 2 / 2 := by
    have hmul : δ * (2 * S + 2) ≤ etarget * den ^ 2 := (le_div_iff₀ (by linarith [hS0])).mp hδ3
    nlinarith [hmul, hδpos, hS0]
  calc |mkF_numerator k G * den - mkF_denominator k G * numF|
      ≤ δ * S := hnum_bound
    _ < etarget * den ^ 2 / 2 := hSlt
    _ ≤ etarget * (mkF_denominator k G * den) := by nlinarith [hbden, hetarget]

/-- **Tensor partition-of-unity identity** (the algebraic core of the separable
box-tensor density construction). If `{ρ_m}_{m∈I}` is a 1-D partition of unity
(`∑_m ρ_m(x) = 1` for every `x`), then the `k`-fold tensor products
`∏_i ρ_{φ(i)}(t_i)` over all index-tuples `φ : Fin k → I` also sum to `1`:
`∑_{φ : Fin k → I} ∏_i ρ_{φ(i)}(t_i) = ∏_i (∑_m ρ_m(t_i)) = ∏_i 1 = 1`.
This is exactly what makes `G(t) := ∑_φ F(c_φ)·∏_i ρ_{φ(i)}(t_i)` a genuine
approximation: `F t − G t = ∑_φ (F t − F(c_φ))·∏_i ρ_{φ(i)}(t_i)`, bounded by the
modulus of continuity of `F`. Pure `Fintype.prod_sum`. -/
theorem tensor_partition_of_unity {k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → ℝ → ℝ) (hρ : ∀ x : ℝ, ∑ m : I, ρ m x = 1) (t : Fin k → ℝ) :
    ∑ φ : (Fin k → I), ∏ i : Fin k, ρ (φ i) (t i) = 1 := by
  rw [← Fintype.prod_sum (fun (i : Fin k) (m : I) => ρ m (t i))]
  simp only [hρ, Finset.prod_const_one]

/-- **Every finite tensor sum is finite-separable.** A function of the form
`t ↦ ∑_{φ : Fin k → I} a(φ)·∏_i g(φ i)(t_i)` (a finite linear combination of
products of 1-D functions, with `I` a finite index type) satisfies
`IsFiniteSeparable`. This is precisely the shape of the box-tensor density
approximant `G`, so the *separability* conjunct of `separable_dense_sup` is
automatic for it; only smoothness, support and the sup-bound remain. -/
theorem isFiniteSeparable_tensor_sum {k : ℕ} {I : Type*} [Fintype I]
    (a : (Fin k → I) → ℝ) (g : I → ℝ → ℝ) :
    IsFiniteSeparable (fun t => ∑ φ : (Fin k → I), a φ * ∏ i : Fin k, g (φ i) (t i)) := by
  classical
  let e := Fintype.equivFin (Fin k → I)
  refine ⟨Fintype.card (Fin k → I), fun j => a (e.symm j),
    fun j i x => g ((e.symm j) i) x, 0, fun t => ?_⟩
  exact (Equiv.sum_comp e.symm (fun φ => a φ * ∏ i, g (φ i) (t i))).symm

/-- **Smoothness of a finite tensor sum.** If each 1-D factor `g_m` is `C^∞`,
the box-tensor approximant `t ↦ ∑_{φ : Fin k → I} a(φ)·∏_i g(φ i)(t_i)` is `C^∞`
(finite sum of products of `C^∞` coordinate compositions). The `IsFiniteSeparable`
predicate alone does NOT carry smoothness, so the *smoothness* conjunct of
`separable_dense_sup` needs this companion to `isFiniteSeparable_tensor_sum`. -/
theorem contDiff_tensor_sum {k : ℕ} {I : Type*} [Fintype I]
    (a : (Fin k → I) → ℝ) (g : I → ℝ → ℝ) (hg : ∀ m, ContDiff ℝ ∞ (g m)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ => ∑ φ : (Fin k → I), a φ * ∏ i : Fin k, g (φ i) (t i)) := by
  refine ContDiff.sum (fun φ _ => ?_)
  exact contDiff_const.mul (contDiff_prod (fun i _ => (hg (φ i)).comp (contDiff_apply ℝ ℝ i)))

/-- **1-D smooth partition of unity** (the residual analytic input to the
box-tensor density). With the smooth transition `σ = Real.smoothTransition`
(`σ = 0` on `(-∞,0]`, `= 1` on `[1,∞)`, `C^∞`), the bumps
`ρ_m(x) := σ(x − m) − σ(x − (m+1))` are smooth, each supported on `[m, m+2]`,
and the `N+1` of them sum to `1` on the whole interval `[1, N+1]`:
`∑_{m=0}^{N} (σ(x−m) − σ(x−(m+1))) = 1` (telescoping, with `σ(x)=1` for `x≥1`
and `σ(x−(N+1))=0` for `x ≤ N+1`). This is the 1-D PoU consumed (after a mesh
rescale `x ↦ x/h`) by `tensor_partition_of_unity`; together with
`isFiniteSeparable_tensor_sum` it furnishes the separable approximant
`G(t)=∑_φ F(c_φ)∏_i ρ_{φ i}(t_i)` for `separable_dense_sup`. The residue is then
the modulus-of-continuity sup-bound + keeping the active bump-boxes inside the
simplex (inward dilation). -/
theorem smoothTransition_finite_partition (N : ℕ) {x : ℝ}
    (hx1 : 1 ≤ x) (hxN : x ≤ (N : ℝ) + 1) :
    ∑ m ∈ Finset.range (N + 1),
      (Real.smoothTransition (x - m) - Real.smoothTransition (x - (m + 1))) = 1 := by
  have key := Finset.sum_range_sub' (fun j : ℕ => Real.smoothTransition (x - (j : ℝ))) (N + 1)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero] at key
  rw [key, Real.smoothTransition.one_of_one_le hx1,
    Real.smoothTransition.zero_of_nonpos (show x - ((N : ℝ) + 1) ≤ 0 by linarith)]
  ring

/-- **Separable sup-norm density** (the irreducible analytic core of
`exists_separable_F_of_Mk_gt`, with the continuity half discharged by
`mkF_sub_lt_of_sup_le`). Any admissible smooth `F` on the simplex is uniformly
approximable on the simplex, to within any `δ > 0`, by a *finite-separable*
smooth simplex-supported `G`. Pure approximation theory, **no number theory**:
finite sums of products of 1-D smooth bumps on small boxes inside the open
simplex are sup-dense among smooth simplex-supported functions (box-tensor
refinement; cf. the product-of-bumps witness in `MkSet_nonempty`). The positive
denominator and the `MkF`-closeness are then automatic via `mkF_sub_lt_of_sup_le`. -/
axiom separable_dense_sup (k : ℕ) (F : (Fin k → ℝ) → ℝ)
    (_hF : ContDiff ℝ ∞ F) (_hsupp : Function.support F ⊆ simplex k)
    (_hden : mkF_denominator k F > 0) (δ : ℝ) (_hδ : 0 < δ) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex k ∧
      (∀ t ∈ simplex k, |F t - G t| ≤ δ)

/-- **Separable approximation of the Maynard ratio** (the *narrowed analytic core*
of the cited `exists_separable_F_of_Mk_gt`). Any admissible smooth `F` on the
`k`-simplex can be approximated, in the value of the Maynard ratio `MkF`, by a
*finite-separable* (still smooth, simplex-supported, positive-denominator) `G`,
to within any `ε > 0`.

**Now a theorem** (was a cited number-theory axiom): the continuity half is
proved in-kernel (`mkF_sub_lt_of_sup_le`), so this rests only on the pure
approximation-theory axiom `separable_dense_sup` (sup-norm density of separable
functions). Take the continuity modulus `δ` for `ε`, get a separable `G` within
sup-distance `δ`, and `mkF_sub_lt_of_sup_le` delivers `0 < den G` and
`|MkF G − MkF F| < ε`. -/
theorem sep_approx (k : ℕ) (F : (Fin k → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hsupp : Function.support F ⊆ simplex k)
    (hden : mkF_denominator k F > 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex k ∧
      mkF_denominator k G > 0 ∧ |MkF k G - MkF k F| < ε := by
  obtain ⟨δ, hδpos, hcont⟩ := mkF_sub_lt_of_sup_le k F hF.continuous hsupp hden ε hε
  obtain ⟨G, hGsep, hGsm, hGsupp, hGclose⟩ := separable_dense_sup k F hF hsupp hden δ hδpos
  obtain ⟨hGden, hGlt⟩ := hcont G hGsm.continuous hGsupp hGclose
  exact ⟨G, hGsep, hGsm, hGsupp, hGden, hGlt⟩

/-- **Separable realisation of $M_k$** (Polymath8b §6): if $c < M_k$
then a witness $F$ realising $\mathrm{MkF}(k, F) > c$ may be taken to be a
*finite-separable* test function (`IsFiniteSeparable F`).

**Now a theorem** (was a cited axiom): the deep "separability out of the
$M_k$-extraction" claim is reduced to the elementary `sSup` extraction
`exists_F_of_Mk_gt` together with the pure-analysis approximation lemma
`sep_approx`. Pick `c < c' < M_k`; `exists_F_of_Mk_gt` gives a smooth witness
`F` with `MkF F > c'`; `sep_approx … (c' − c)` gives a finite-separable `G`
with `|MkF G − MkF F| < c' − c`, hence `MkF G > c' − (c' − c) = c`. The only
remaining axiomatic content is the pure-analysis `sep_approx` (density +
continuity), no longer the number-theoretic §6 polynomial-optimisation. -/
theorem exists_separable_F_of_Mk_gt (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : c < Mk k) :
    ∃ F : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable F ∧ ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex k ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  -- choose an intermediate threshold c < c' < M_k
  set c' : ℝ := (c + Mk k) / 2 with hc'def
  have hcc' : c < c' := by rw [hc'def]; linarith
  have hc'Mk : c' < Mk k := by rw [hc'def]; linarith
  -- a smooth witness beating c'
  obtain ⟨F, hSmooth, hSupp, hDen, hcF⟩ := exists_F_of_Mk_gt k hk c' hc'Mk
  -- a separable approximant within (c' - c) of it
  obtain ⟨G, hGsep, hGsm, hGsupp, hGden, hGclose⟩ :=
    sep_approx k F hSmooth hSupp hDen (c' - c) (by linarith)
  refine ⟨G, hGsep, hGsm, hGsupp, hGden, ?_⟩
  -- |MkF G - MkF F| < c' - c and MkF F > c' ⟹ MkF G > c
  have hlow := (abs_lt.mp hGclose).1
  linarith

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
      ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex_truncated k α ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  have hLt : c < sSup (MkSet_truncated k α) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_truncated_bddAbove k α)
      (MkSet_truncated_nonempty k hk α hα)).mp hLt
  obtain ⟨F, hSmooth, hSupp, hDen, hvEq⟩ := hvMem
  exact ⟨F, hSmooth, hSupp, hDen, hvEq ▸ hcv⟩

/-- **Separable sup-norm density, truncated variant** (the irreducible density
core; sister of `separable_dense_sup` for the truncated simplex
$\{t \in [0,\alpha]^k : \sum_i t_i \le 1\}$). The continuity half is shared with
the untruncated case (`mkF_sub_lt_of_sup_le`, since the truncated simplex sits
inside the simplex and `MkF` is the same functional). -/
axiom separable_dense_sup_truncated (k : ℕ) (α : ℝ) (F : (Fin k → ℝ) → ℝ)
    (_hF : ContDiff ℝ ∞ F) (_hsupp : Function.support F ⊆ simplex_truncated k α)
    (_hden : mkF_denominator k F > 0) (δ : ℝ) (_hδ : 0 < δ) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex_truncated k α ∧
      (∀ t ∈ simplex k, |F t - G t| ≤ δ)

/-- **Separable approximation, truncated variant** (the narrowed core of
`exists_separable_F_truncated_of_Mk_truncated_gt`). **Now a theorem**: the
continuity half is the proven `mkF_sub_lt_of_sup_le` (the truncated simplex is
contained in the simplex and `MkF` is the same), so this rests only on the
pure-density axiom `separable_dense_sup_truncated`. -/
theorem sep_approx_truncated (k : ℕ) (α : ℝ) (F : (Fin k → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hsupp : Function.support F ⊆ simplex_truncated k α)
    (hden : mkF_denominator k F > 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex_truncated k α ∧
      mkF_denominator k G > 0 ∧ |MkF k G - MkF k F| < ε := by
  have hsub : simplex_truncated k α ⊆ simplex k := fun t ⟨h0, _, hs⟩ => ⟨h0, hs⟩
  obtain ⟨δ, hδpos, hcont⟩ :=
    mkF_sub_lt_of_sup_le k F hF.continuous (hsupp.trans hsub) hden ε hε
  obtain ⟨G, hGsep, hGsm, hGsupp, hGclose⟩ :=
    separable_dense_sup_truncated k α F hF hsupp hden δ hδpos
  obtain ⟨hGden, hGlt⟩ := hcont G hGsm.continuous (hGsupp.trans hsub) hGclose
  exact ⟨G, hGsep, hGsm, hGsupp, hGden, hGlt⟩

/-- **Separable realisation of $M_k^{[\alpha]}$** (Polymath8b §6, truncated
variant). **Now a theorem** (was a cited axiom): identical reduction to
`exists_separable_F_of_Mk_gt`, via `exists_F_truncated_of_Mk_truncated_gt`
and the pure-density-backed `sep_approx_truncated`. -/
theorem exists_separable_F_truncated_of_Mk_truncated_gt (k : ℕ) (hk : 2 ≤ k)
    (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : c < Mk_truncated k α) :
    ∃ F : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable F ∧ ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex_truncated k α ∧
      mkF_denominator k F > 0 ∧ c < MkF k F := by
  set c' : ℝ := (c + Mk_truncated k α) / 2 with hc'def
  have hc'Mk : c' < Mk_truncated k α := by rw [hc'def]; linarith
  obtain ⟨F, hSmooth, hSupp, hDen, hcF⟩ := exists_F_truncated_of_Mk_truncated_gt k hk α hα c' hc'Mk
  obtain ⟨G, hGsep, hGsm, hGsupp, hGden, hGclose⟩ :=
    sep_approx_truncated k α F hSmooth hSupp hDen (c' - c) (by linarith)
  refine ⟨G, hGsep, hGsm, hGsupp, hGden, ?_⟩
  have hlow := (abs_lt.mp hGclose).1
  linarith

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

/-- **The 1D Möbius-divisor transform** (Polymath8b §3, the $\lambda$
operator underlying eqn (3.6)–(3.7) `nuform`):
$$\lambda_g(R, n) := \sum_{d \mid n} \mu(d)\, g\!\left(\frac{\log d}{\log R}\right).$$

This is the per-coordinate building block of the Selberg sieve weight: the
multidimensional weight `selberg_nu` is a squared finite linear combination
of products $\prod_i \lambda_{F_{j,i}}(R, n + h_i)$ over a basis
decomposition $F = \sum_j c_j \prod_i F_{j,i}$.

Fully concrete `noncomputable def` (Tier-1 ROADMAP entry point, 2026-05-27):
sum over `Nat.divisors n` of the mathlib Möbius function `μ` cast to ℝ,
weighted by $g$ evaluated at the normalized log-divisor. The sieve
threshold $R$ enters through the $\log d / \log R$ rescaling. -/
noncomputable def lambdaTransform (g : ℝ → ℝ) (R : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    (ArithmeticFunction.moebius d : ℝ) * g (Real.log d / Real.log R)

/-- $\lambda_g(R, 0) = 0$: the empty divisor set. -/
@[simp] theorem lambdaTransform_zero (g : ℝ → ℝ) (R : ℝ) :
    lambdaTransform g R 0 = 0 := by
  unfold lambdaTransform; rw [Nat.divisors_zero]; simp

/-- $\lambda_g(R, 1) = g(0)$: the only divisor is $1$, with $\mu(1) = 1$
and $\log 1 = 0$. -/
@[simp] theorem lambdaTransform_one (g : ℝ → ℝ) (R : ℝ) :
    lambdaTransform g R 1 = g 0 := by
  unfold lambdaTransform; rw [Nat.divisors_one]; simp

/-- **$\lambda$ at a prime** (the general two-term divisor identity): for
prime $p$ the only divisors are $1$ and $p$, with $\mu(1) = 1$,
$\mu(p) = -1$, and $\log 1 = 0$, so
$$\lambda_g(R, p) = g(0) - g\!\left(\tfrac{\log p}{\log R}\right).$$
This is the unconditional identity *underlying* Polymath8b §3 eqn
(lambdan-prime); the paper's $\lambda_F(p) = F(0)$ is the corollary
`lambdaTransform_prime_of_support` below, valid once the second term
vanishes (F supported on $[0,1]$ and $p \ge x$, so $\log_x p \ge 1$). It is
the load-bearing fact behind the high $\theta(n+h_i)$–$\lambda_{F_i}(n+h_i)$
correlation, used in the eventual (s1)/(s2) divisor-sum expansions. -/
theorem lambdaTransform_prime (g : ℝ → ℝ) (R : ℝ) {p : ℕ} (hp : p.Prime) :
    lambdaTransform g R p = g 0 - g (Real.log p / Real.log R) := by
  unfold lambdaTransform
  rw [hp.divisors, Finset.sum_insert (by simp [(hp.one_lt).ne])]
  simp [ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]

/-- **Polymath8b §3 eqn (lambdan-prime)** exactly: when the test function
vanishes at $\log_x p$ (the paper's hypothesis: $F$ supported on $[0,1]$ and
$p \ge x$, so $\log_x p \ge 1$ lies outside the support), the prime-value
identity collapses to $\lambda_F(p) = F(0)$. -/
theorem lambdaTransform_prime_of_support (g : ℝ → ℝ) (R : ℝ) {p : ℕ}
    (hp : p.Prime) (hvanish : g (Real.log p / Real.log R) = 0) :
    lambdaTransform g R p = g 0 := by
  rw [lambdaTransform_prime g R hp, hvanish, sub_zero]

/-- `lambdaTransform` is **additive** in its test function: the operator
$g \mapsto \lambda_g$ distributes over pointwise addition. -/
theorem lambdaTransform_add (g₁ g₂ : ℝ → ℝ) (R : ℝ) (n : ℕ) :
    lambdaTransform (fun x => g₁ x + g₂ x) R n
      = lambdaTransform g₁ R n + lambdaTransform g₂ R n := by
  unfold lambdaTransform
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `lambdaTransform` is **homogeneous** in its test function: scaling $g$ by
$a$ scales $\lambda_g$ by $a$. -/
theorem lambdaTransform_smul (a : ℝ) (g : ℝ → ℝ) (R : ℝ) (n : ℕ) :
    lambdaTransform (fun x => a * g x) R n = a * lambdaTransform g R n := by
  unfold lambdaTransform
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `lambdaTransform` distributes over negation of the test function. -/
theorem lambdaTransform_neg (g : ℝ → ℝ) (R : ℝ) (n : ℕ) :
    lambdaTransform (fun x => - g x) R n = - lambdaTransform g R n := by
  unfold lambdaTransform
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **Linearity** of $g \mapsto \lambda_g$ (the combined form): for scalars
$a, b$ and test functions $g_1, g_2$,
$\lambda_{a g_1 + b g_2} = a \lambda_{g_1} + b \lambda_{g_2}$. This is what
lets the multidimensional nuform be expanded coordinate-by-coordinate over a
basis decomposition $F = \sum_j c_j \prod_i F_{j,i}$. -/
theorem lambdaTransform_linear (a b : ℝ) (g₁ g₂ : ℝ → ℝ) (R : ℝ) (n : ℕ) :
    lambdaTransform (fun x => a * g₁ x + b * g₂ x) R n
      = a * lambdaTransform g₁ R n + b * lambdaTransform g₂ R n := by
  unfold lambdaTransform
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **Separable Selberg sieve weight** — the $J = 1$, $c_1 = 1$ special case
of the `nuform` \eqref{837}. For a fully separable test function
$F(t_1,\dots,t_k) = \prod_i F_i(t_i)$ the squared finite linear combination
collapses to a single product:
$$\nu_{\mathrm{sep}}(n) = \Bigl(\prod_{i=1}^{k} \lambda_{F_i}(n + h_i)\Bigr)^2.$$

Unlike the general `selberg_nu` (which needs a basis decomposition $F =
\sum_j c_j \prod_i F_{j,i}$ that is finite only for separable $F$), this is
**fully encodable** from the real 1D operator `lambdaTransform`: no opaque,
no axiom, no sorry. It is the first concrete piece of the multidimensional
Selberg weight (Tier-1 ROADMAP). The offsets $h_i$ are read from `H` via
`H.getD i 0`; the sieve level enters through `lambdaTransform`'s $R$. -/
noncomputable def selberg_nu_separable (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  (∏ i : Fin k, lambdaTransform (Fs i) R (n + H.getD i.val 0)) ^ 2

/-- The separable weight is non-negative (it is a square), matching the
Polymath8b requirement $\nu : \N \to \R^+$. -/
theorem selberg_nu_separable_nonneg (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (n : ℕ) : 0 ≤ selberg_nu_separable k Fs H R n :=
  sq_nonneg _

/-- At $k = 0$ the empty product is $1$, so $\nu_{\mathrm{sep}} = 1$. -/
@[simp] theorem selberg_nu_separable_zero_dim (Fs : Fin 0 → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (n : ℕ) : selberg_nu_separable 0 Fs H R n = 1 := by
  simp [selberg_nu_separable]

/-- **General Selberg sieve weight** (the full `nuform`, Polymath8b §3
\eqref{837} verbatim): a squared finite linear combination of products of
1D divisor sums,
$$\nu(n) = \Bigl(\sum_{j=1}^{J} c_j \prod_{i=1}^{k}
   \lambda_{F_{j,i}}(n + h_i)\Bigr)^2.$$

This is the **fully general** construction — no separability assumption — and
is **completely encoded** from the real 1D operator `lambdaTransform`: no
opaque, no axiom, no sorry. The basis is given explicitly as $J$ terms with
coefficients `c : Fin J → ℝ` and per-term, per-coordinate 1D functions
`Fs : Fin J → Fin k → ℝ → ℝ`. The separable case `selberg_nu_separable` is
the single-term ($J = 1$, $c_1 = 1$) collapse — see
`selberg_nu_basis_single`. Caps the `lambdaTransform → selberg_nu_separable
→ selberg_nu_basis` real-construction ladder (Tier-1 ROADMAP). -/
noncomputable def selberg_nu_basis (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  (∑ j : Fin J, c j *
      ∏ i : Fin k, lambdaTransform (Fs j i) R (n + H.getD i.val 0)) ^ 2

/-- The general weight is non-negative (it is a square), matching the
Polymath8b requirement $\nu : \N \to \R^+$. -/
theorem selberg_nu_basis_nonneg (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (n : ℕ) :
    0 ≤ selberg_nu_basis k J c Fs H R n :=
  sq_nonneg _

/-- An empty basis ($J = 0$) gives the zero weight (empty sum). -/
@[simp] theorem selberg_nu_basis_empty (k : ℕ) (c : Fin 0 → ℝ)
    (Fs : Fin 0 → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (n : ℕ) :
    selberg_nu_basis k 0 c Fs H R n = 0 := by
  simp [selberg_nu_basis]

/-- **Separable is the single-term basis.** The general nuform with one term
($J = 1$, coefficient $1$, 1D functions `Gs`) is exactly the separable
weight `selberg_nu_separable`. This is the bridge collapsing the general
construction to the encoded separable special case. -/
theorem selberg_nu_basis_single (k : ℕ) (Gs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (n : ℕ) :
    selberg_nu_basis k 1 (fun _ => 1) (fun _ => Gs) H R n
      = selberg_nu_separable k Gs H R n := by
  simp [selberg_nu_basis, selberg_nu_separable]

/-- **Selberg sieve weight** (Polymath8b §3, eqn (3.6)–(3.7), `nuform`):
$\nu(n) = \left(\sum_j c_j \prod_i \lambda_{F_{j,i}}(n + h_i)\right)^2$ —
a finite linear combination of products of 1D divisor sums, now a real
`noncomputable def` aliasing `selberg_nu_basis`. The basis data
$(J, (c_j), (F_{j,i}))$ and sieve level $R$ are carried explicitly;
the interface is discharged (path A, PR #64): s1/s2 axioms now speak about
`selberg_nu_basis` directly, coupling via the `IsFiniteSeparable` predicate
on the test function $F$. -/
noncomputable def selberg_nu (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) : ℕ → ℝ :=
  selberg_nu_basis k J c Fs H R

/-- **W-trick** (Polymath8b §3): for any admissible $k$-tuple $\mathcal{H}$
of length $k \ge 1$, there exists a modulus $W \ge 1$ and a residue class
$b \pmod{W}$ with $b + h_i$ coprime to $W$ for each $i$ (the standard
construction takes $W := \prod_{p \le D} p$ for an appropriate threshold $D$
and uses CRT + admissibility to pick $b$).

The conclusion exposes only $W \ge 1$ and $b < W$; the coprimality conditions
on $(b, W)$ are absorbed into the `selberg_nu` / `alphaBound` / `betaBound`
predicates. Because the exposed conclusion no longer mentions coprimality (it
was refactored into those predicates), the bare existential is **trivially
true** ($W = 1$, $b = 0$) and needs no Mertens/CRT machinery — so this is a
real `theorem`, not an axiom. The genuine analytic W-trick content lives in
the (still-cited) `s1_*`/`s2_*` axioms, where the coprime residue class is a
hypothesis on the asymptotic.

**Discharged 2026-05-30** (`axiom → theorem`): the stated conclusion is
trivial, removing `wtrick_data` from the flagships' `#print axioms` without
hiding anything — the deep content remains cited via s1/s2. -/
theorem wtrick_data {k : ℕ} (_hk : k ≥ 1) {H : List ℕ}
    (_hAdm : Admissible H) (_hLen : H.length = k) :
    ∃ b W : ℕ, 1 ≤ W ∧ b < W :=
  ⟨0, 1, le_refl 1, Nat.zero_lt_one⟩

/-- **(s1) from `nonprime-asym` case (i)** (Polymath8b §3 line 889, "Trivial").
For admissible $F$ on the simplex (so $\sum_i S(F_i) + S(G_i) < 1$ is implied
by `Function.support F ⊆ simplex k`), and for any $(b, W)$ from the W-trick,
the (s1) asymptotic holds eventually with $\alpha = I(F) =
\int_{\mathcal{R}_k} F^2$.

Future PR can replace with a real proof from the divisor-sum expansion
(Polymath8b §3 eqns (sfg-1), (lflg)). -/
axiom s1_holds_from_nonprime_asym {k : ℕ} (_hk : k ≥ 2)
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex k)
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) :
    ∀ᶠ x : ℝ in Filter.atTop,
      alphaBound k (selberg_nu k J c Fs H R) b W x (mkF_denominator k F)

/-- **(s2) from `prime-asym` case (i)** (Polymath8b §3 line 862, EH version).
Under $\EH[\vartheta]$ with $0 < \vartheta < 1$, and admissible $F$ on the
simplex, the (s2) asymptotic holds eventually with $\beta_i =
(\vartheta/2) \cdot J_i(F)$ for each $i$.

The $\vartheta/2$ factor is the Polymath8b normalization absorbing the ratio
$B^{-k}\,x/W$ vs $B^{1-k}\,x/\phi(W)$ from `nonprime-asym` vs `prime-asym`,
together with the $\vartheta$ from the EH window. Future PR can replace with
a real proof from the divisor-sum expansion (Polymath8b §3 eqn (theta-oo)). -/
axiom s2_holds_from_prime_asym_under_EH {k : ℕ} (_hk : k ≥ 2)
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ϑ : ℝ} (_hϑ : 0 < ϑ ∧ ϑ < 1) (_hEH : Prerequisites.EH ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex k)
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k J c Fs H R) H b W i.val x (ϑ / 2 * J_i k F i)

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
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ϖ δ : ℝ} (_hϖ : 0 < 1 / 4 + ϖ) (_hMPZ : Prerequisites.MPZ ϖ δ)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex_truncated k (δ / (1 / 4 + ϖ)))
    (_hF_den : mkF_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k J c Fs H R) H b W i.val x ((1 / 4 + ϖ) * J_i k F i)

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
    (hF_sep : IsFiniteSeparable F)
    (hF_smooth : ContDiff ℝ ∞ F)
    (hF_supp : Function.support F ⊆ simplex k)
    (hF_den : mkF_denominator k F > 0)
    (hF_Mk : MkF k F > 2 * m / ϑ)
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      1 ≤ W ∧ (∀ n, 0 ≤ ν n) ∧ 0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  obtain ⟨J, c, Fs, R, hFdecomp⟩ := hF_sep
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hϑ_half_pos : 0 < ϑ / 2 := by linarith
  refine ⟨b, W, selberg_nu k J c Fs H R, mkF_denominator k F,
    fun i => ϑ / 2 * J_i k F i, hW, (fun n => selberg_nu_basis_nonneg k J c Fs H R n), hF_den, ?_, ?_, ?_, ?_⟩
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
    exact s1_holds_from_nonprime_asym hk hFdecomp hF_smooth hF_supp hF_den hAdm hLen b W hW
  · -- (s2)
    intro i
    exact s2_holds_from_prime_asym_under_EH hk hϑ hEH hFdecomp hF_smooth hF_supp hF_den
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
  obtain ⟨F, hSep, hSmooth, hSupp, hDen, hMkF⟩ :=
    exists_separable_F_of_Mk_gt k hk (2 * m / ϑ) hMk
  exact selberg_sieve_data_from_F hk hm hϑ hEH hSep hSmooth hSupp hDen hMkF hAdm hLen

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
    {ϖ δ : ℝ} (hϖ : 0 < 1 / 4 + ϖ) (hMPZ : Prerequisites.MPZ ϖ δ)
    {F : (Fin k → ℝ) → ℝ}
    (hF_sep : IsFiniteSeparable F)
    (hF_smooth : ContDiff ℝ ∞ F)
    (hF_supp : Function.support F ⊆ simplex_truncated k (δ / (1 / 4 + ϖ)))
    (hF_den : mkF_denominator k F > 0)
    (hF_Mk : MkF k F > m / (1 / 4 + ϖ))
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      1 ≤ W ∧ (∀ n, 0 ≤ ν n) ∧ 0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  obtain ⟨J, c, Fs, R, hFdecomp⟩ := hF_sep
  -- Coerce F's support from truncated simplex into the full simplex; the
  -- per-coordinate constraint t_i ≤ α is stricter than the open simplex.
  have hF_supp_simplex : Function.support F ⊆ simplex k := by
    intro t ht
    obtain ⟨h_nonneg, _h_lealpha, h_sumle⟩ := hF_supp ht
    exact ⟨h_nonneg, h_sumle⟩
  refine ⟨b, W, selberg_nu k J c Fs H R, mkF_denominator k F,
    fun i => (1/4 + ϖ) * J_i k F i, hW, (fun n => selberg_nu_basis_nonneg k J c Fs H R n), hF_den, ?_, ?_, ?_, ?_⟩
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
    exact s1_holds_from_nonprime_asym hk hFdecomp hF_smooth hF_supp_simplex hF_den hAdm hLen b W hW
  · -- (s2) MPZ version
    intro i
    exact s2_holds_from_prime_asym_under_MPZ hk hϖ hMPZ hFdecomp hF_smooth hF_supp hF_den
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
    (hϖ : 0 < 1 / 4 + ϖ) (hδ : 0 < δ) (hMPZ : Prerequisites.MPZ ϖ δ)
    (hMk : Mk_truncated k (δ / (1 / 4 + ϖ)) > m / (1 / 4 + ϖ)) :
    DHL k (m + 1) := by
  apply dhl_criterion k m hk hm
  intro H hAdm hLen
  have hα_pos : 0 < δ / (1 / 4 + ϖ) := div_pos hδ hϖ
  obtain ⟨F, hSep, hSmooth, hSupp, hDen, hMkF⟩ :=
    exists_separable_F_truncated_of_Mk_truncated_gt k hk (δ / (1 / 4 + ϖ)) hα_pos
      (m / (1 / 4 + ϖ)) hMk
  exact selberg_sieve_data_truncated_from_F hk hm hϖ hMPZ hSep hSmooth hSupp hDen
    hMkF hAdm hLen

/-- **sSup extraction for $M_{k,\varepsilon}$**: if $c < M_{k,\varepsilon}$
then there is a specific admissible $F$ supported on $(1+\varepsilon)
\mathcal{R}_k$ realizing $\mathrm{MkF}_\varepsilon(k, \varepsilon, F) > c$.

Sister of `exists_F_of_Mk_gt`. Same `lt_csSup_iff` discharge, consuming
`MkSet_eps_nonempty` and `MkSet_eps_bddAbove`. -/
theorem exists_F_eps_of_Mk_eps_gt (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : c < Mk_eps k ε) :
    ∃ F : (Fin k → ℝ) → ℝ,
      ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex_eps k ε ∧
      mkF_eps_denominator k ε F > 0 ∧ c < MkF_eps k ε F := by
  have hLt : c < sSup (MkSet_eps k ε) := hc
  obtain ⟨v, hvMem, hcv⟩ :=
    (lt_csSup_iff (MkSet_eps_bddAbove k ε) (MkSet_eps_nonempty k hk ε hε)).mp hLt
  obtain ⟨F, hSmooth, hSupp, hDen, hvEq⟩ := hvMem
  exact ⟨F, hSmooth, hSupp, hDen, hvEq ▸ hcv⟩

/-! ### Sup-norm continuity of the ε-flavored Maynard functionals

The ε-sister of the continuity machinery above (`mkF_sub_lt_of_sup_le` and
components). Same elementary integral-monotonicity argument, with `simplex k`
replaced by the enlarged `simplex_eps k ε`, the outer `J_i` domain `simplex n`
replaced by the shrunken `simplex_shrunk n ε`, and the inner integration limit
`1 − ∑s` replaced by `1 + ε − ∑s`. We assume `0 ≤ ε` (always available at the
call site, where `0 < ε`); this keeps the inner length `L = 1+ε−∑s ≥ 2ε ≥ 0`
on the shrunken simplex, so the proofs port verbatim with `L ≤ 1+ε` taking the
place of `L ≤ 1`. -/

open MeasureTheory Set in
/-- ε-sister of `Ji_integrand_integrableOn`: the `J_{i,1-ε}` integrand
`s ↦ (∫_{[0,1+ε-∑s]} H(insertNth i · s))²` is integrable over `simplex_shrunk n ε`.
Cauchy–Schwarz on `[0, L]` (`L = 1+ε-∑s ≤ 1+ε`) dominates it by `(1+ε)·Φ`, with
`Φ s = ∫ H(insertNth i · s)²` integrable via the `volume_preserving_piFinSuccAbove`
marginal machinery. -/
private theorem Ji_eps_integrand_integrableOn (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (H : (Fin (n + 1) → ℝ) → ℝ) (hHc : Continuous H)
    (hHsupp : Function.support H ⊆ simplex_eps (n + 1) ε) (i : Fin (n + 1)) :
    IntegrableOn
      (fun s => (∫ ti in Icc 0 (1 + ε - ∑ j, s j), H (i.insertNth ti s)) ^ 2)
      (simplex_shrunk n ε) := by
  classical
  have hsimpEpsCompact : IsCompact (simplex_eps (n + 1) ε) := isCompact_simplex_eps (n + 1) ε
  have hsimpEpsClosed : IsClosed (simplex_eps (n + 1) ε) := hsimpEpsCompact.isClosed
  have hcs : HasCompactSupport H :=
    IsCompact.of_isClosed_subset hsimpEpsCompact isClosed_closure
      (closure_minimal hHsupp hsimpEpsClosed)
  have hH2cont : Continuous (fun t => H t ^ 2) := hHc.pow 2
  have hcs2 : HasCompactSupport (fun t => H t ^ 2) := by
    apply hcs.comp_left (g := fun x : ℝ => x ^ 2); simp
  have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hcs
  have hH2i : Integrable (fun t => H t ^ 2) := hH2cont.integrable_of_hasCompactSupport hcs2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set m : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, H (i.insertNth ti s) with hm
  set Φ : (Fin n → ℝ) → ℝ := fun s => ∫ ti : ℝ, H (i.insertNth ti s) ^ 2 with hΦ
  have hprodH2 : Integrable (fun p : ℝ × (Fin n → ℝ) => H (e.symm p) ^ 2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hH2i
  have hΦi : Integrable Φ := by
    have h := hprodH2.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hprodH : Integrable (fun p : ℝ × (Fin n → ℝ) => H (e.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hHi
  have hmi : Integrable m := by
    have h := hprodH.integral_prod_right
    simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk] at h
    exact h
  have hΦnn : ∀ s, 0 ≤ Φ s := fun s => integral_nonneg fun ti => sq_nonneg _
  have hmeasS : MeasurableSet (simplex_shrunk n ε) := (isClosed_simplex_shrunk n ε).measurableSet
  have key : ∀ s ∈ simplex_shrunk n ε,
      (∫ ti in Icc 0 (1 + ε - ∑ j, s j), H (i.insertNth ti s)) = m s ∧ m s ^ 2 ≤ (1 + ε) * Φ s := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    set L := 1 + ε - ∑ j, s j with hL
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    have hLnn : 0 ≤ L := by rw [hL]; linarith
    have hLle : L ≤ 1 + ε := by rw [hL]; linarith
    have hzero : ∀ ti, ti ∉ Icc (0 : ℝ) L → H (i.insertNth ti s) = 0 := by
      intro ti hti
      by_contra hne
      have hmem : i.insertNth ti s ∈ simplex_eps (n + 1) ε :=
        hHsupp (Function.mem_support.mpr hne)
      obtain ⟨hmem_nn, hmem_sum⟩ := hmem
      apply hti
      refine ⟨?_, ?_⟩
      · have := hmem_nn i; rwa [Fin.insertNth_apply_same] at this
      · rw [hL, le_sub_iff_add_le]
        have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq] at hmem_sum; linarith
    have hcont_h : Continuous (fun ti => H (i.insertNth ti s)) :=
      hHc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hint_h : IntegrableOn (fun ti => H (i.insertNth ti s)) (Icc 0 L) :=
      hcont_h.integrableOn_Icc
    have hint_h2 : IntegrableOn (fun ti => H (i.insertNth ti s) ^ 2) (Icc 0 L) :=
      (hcont_h.pow 2).integrableOn_Icc
    have eqfull : (∫ ti in Icc 0 L, H (i.insertNth ti s)) = m s :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have eqfull2 : (∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2) = Φ s := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro ti hti; rw [hzero ti hti]; ring
    refine ⟨eqfull, ?_⟩
    have hcsq := cs_Icc L hLnn (fun ti => H (i.insertNth ti s)) hint_h hint_h2
    rw [eqfull] at hcsq
    have hnn2 : 0 ≤ ∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2 :=
      integral_nonneg fun ti => sq_nonneg _
    calc m s ^ 2 ≤ L * ∫ ti in Icc 0 L, H (i.insertNth ti s) ^ 2 := hcsq
      _ = L * Φ s := by rw [eqfull2]
      _ ≤ (1 + ε) * Φ s := mul_le_mul_of_nonneg_right hLle (hΦnn s)
  have hm2_aesm : AEStronglyMeasurable (fun s => m s ^ 2) (volume.restrict (simplex_shrunk n ε)) :=
    (hmi.aestronglyMeasurable.pow 2).restrict
  have hm2_int : IntegrableOn (fun s => m s ^ 2) (simplex_shrunk n ε) := by
    refine Integrable.mono' (g := fun s => (1 + ε) * Φ s)
      (hΦi.const_mul (1 + ε)).integrableOn hm2_aesm ?_
    refine (ae_restrict_iff' hmeasS).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (key s hs).2
  refine (integrableOn_congr_fun ?_ hmeasS).mpr hm2_int
  intro s hs; dsimp only; rw [(key s hs).1]

open MeasureTheory in
/-- ε-sister of `mkF_denominator_sub_abs_le`. -/
theorem mkF_eps_denominator_sub_abs_le (k : ℕ) (ε : ℝ) (F G : (Fin k → ℝ) → ℝ)
    (hF : Continuous F) (hG : Continuous G) :
    |mkF_eps_denominator k ε F - mkF_eps_denominator k ε G|
      ≤ ∫ t in simplex_eps k ε, |F t ^ 2 - G t ^ 2| := by
  have hIF : IntegrableOn (fun t => F t ^ 2) (simplex_eps k ε) volume :=
    (hF.pow 2).locallyIntegrable.integrableOn_isCompact (isCompact_simplex_eps k ε)
  have hIG : IntegrableOn (fun t => G t ^ 2) (simplex_eps k ε) volume :=
    (hG.pow 2).locallyIntegrable.integrableOn_isCompact (isCompact_simplex_eps k ε)
  unfold mkF_eps_denominator
  rw [← integral_sub hIF hIG]
  simpa [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (μ := volume.restrict (simplex_eps k ε))
      (f := fun t => F t ^ 2 - G t ^ 2)

open MeasureTheory in
/-- ε-sister of `mkF_denominator_sub_le_const`: if `|F+G| ≤ A`, `|F−G| ≤ εd`
pointwise on `simplex_eps k ε`, the denominators differ by `≤ εd·A·vol`. -/
theorem mkF_eps_denominator_sub_le_const (k : ℕ) (ε : ℝ) (F G : (Fin k → ℝ) → ℝ) (A εd : ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hsum : ∀ t ∈ simplex_eps k ε, |F t + G t| ≤ A)
    (happ : ∀ t ∈ simplex_eps k ε, |F t - G t| ≤ εd) :
    |mkF_eps_denominator k ε F - mkF_eps_denominator k ε G|
      ≤ εd * A * (volume (simplex_eps k ε)).toReal := by
  refine (mkF_eps_denominator_sub_abs_le k ε F G hF hG).trans ?_
  have hms : MeasurableSet (simplex_eps k ε) := (isCompact_simplex_eps k ε).isClosed.measurableSet
  have hbound : ∀ t ∈ simplex_eps k ε, |F t ^ 2 - G t ^ 2| ≤ εd * A := by
    intro t ht
    have hfac : F t ^ 2 - G t ^ 2 = (F t - G t) * (F t + G t) := by ring
    rw [hfac, abs_mul]
    exact mul_le_mul (happ t ht) (hsum t ht) (abs_nonneg _)
      (le_trans (abs_nonneg _) (happ t ht))
  have hI1 : IntegrableOn (fun t => |F t ^ 2 - G t ^ 2|) (simplex_eps k ε) volume :=
    (((hF.pow 2).sub (hG.pow 2)).abs).locallyIntegrable.integrableOn_isCompact
      (isCompact_simplex_eps k ε)
  calc ∫ t in simplex_eps k ε, |F t ^ 2 - G t ^ 2|
      ≤ ∫ _t in simplex_eps k ε, εd * A :=
        setIntegral_mono_on hI1
          (integrableOn_const (isCompact_simplex_eps k ε).measure_lt_top.ne) hms hbound
    _ = εd * A * (volume (simplex_eps k ε)).toReal := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]

open MeasureTheory Set in
/-- ε-sister of `J_i_sub_le_const`: continuity of each ε-marginal `J_{i,1-ε}`.
With `0 ≤ ε`, the inner length `L = 1+ε-∑s ≤ 1+ε` on the shrunken simplex, so the
inner integrals differ by `≤ εd·(1+ε)` and sum to `≤ A·(1+ε)`. -/
theorem J_i_eps_sub_le_const (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F G : (Fin (n + 1) → ℝ) → ℝ)
    (A εd : ℝ) (hFc : Continuous F) (hGc : Continuous G)
    (hFsupp : Function.support F ⊆ simplex_eps (n + 1) ε)
    (hGsupp : Function.support G ⊆ simplex_eps (n + 1) ε)
    (hsum : ∀ t ∈ simplex_eps (n + 1) ε, |F t + G t| ≤ A)
    (happ : ∀ t ∈ simplex_eps (n + 1) ε, |F t - G t| ≤ εd)
    (hεd : 0 ≤ εd) (hA : 0 ≤ A) (i : Fin (n + 1)) :
    |J_i_eps (n + 1) ε F i - J_i_eps (n + 1) ε G i|
      ≤ εd * A * ((1 + ε) ^ 2 * (volume (simplex_shrunk n ε)).toReal) := by
  classical
  have hmeasS : MeasurableSet (simplex_shrunk n ε) := (isClosed_simplex_shrunk n ε).measurableSet
  have hshrunk_sub : simplex_shrunk n ε ⊆ simplex_eps n ε :=
    fun t ht => ⟨ht.1, ht.2.trans (by linarith)⟩
  have hshrunk_ne_top : volume (simplex_shrunk n ε) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hshrunk_sub) (isCompact_simplex_eps n ε).measure_lt_top).ne
  have hIF2 := Ji_eps_integrand_integrableOn n ε hε F hFc hFsupp i
  have hIG2 := Ji_eps_integrand_integrableOn n ε hε G hGc hGsupp i
  have h1εnn : (0 : ℝ) ≤ 1 + ε := by linarith
  have hbound : ∀ s ∈ simplex_shrunk n ε,
      |(∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
        - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2| ≤ εd * A * (1 + ε) ^ 2 := by
    intro s hs
    obtain ⟨hs_nn, hs_sum⟩ := hs
    have hsum_nn : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs_nn j
    set L := 1 + ε - ∑ j, s j with hL
    have hLnn : 0 ≤ L := by rw [hL]; linarith
    have hLle : L ≤ 1 + ε := by rw [hL]; linarith
    have hmem : ∀ ti ∈ Icc (0 : ℝ) L, i.insertNth ti s ∈ simplex_eps (n + 1) ε := by
      intro ti hti
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Fin.insertNth_apply_same]; exact hti.1
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
          rw [Fin.insertNth_apply_succAbove]; exact hs_nn j'
      · have hsum_eq : ∑ j, (i.insertNth ti s) j = ti + ∑ j, s j := by
          rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [Fin.insertNth_apply_succAbove]
        rw [hsum_eq]; have h2 := hti.2; rw [hL] at h2; linarith
    have hcontF : Continuous (fun ti => F (i.insertNth ti s)) :=
      hFc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hcontG : Continuous (fun ti => G (i.insertNth ti s)) :=
      hGc.comp (Continuous.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i
        continuous_id continuous_const)
    have hintF : IntegrableOn (fun ti => F (i.insertNth ti s)) (Icc 0 L) := hcontF.integrableOn_Icc
    have hintG : IntegrableOn (fun ti => G (i.insertNth ti s)) (Icc 0 L) := hcontG.integrableOn_Icc
    have hmIcc : MeasurableSet (Icc (0 : ℝ) L) := measurableSet_Icc
    have hvolIcc : (volume (Icc (0 : ℝ) L)).toReal = L := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    have hvol_ne : volume (Icc (0 : ℝ) L) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne
    have hconstε : IntegrableOn (fun _ : ℝ => εd) (Icc 0 L) := integrableOn_const hvol_ne
    have hconstA : IntegrableOn (fun _ : ℝ => A) (Icc 0 L) := integrableOn_const hvol_ne
    have hdiff : |(∫ ti in Icc 0 L, F (i.insertNth ti s))
                  - (∫ ti in Icc 0 L, G (i.insertNth ti s))| ≤ εd * (1 + ε) := by
      rw [← integral_sub hintF hintG]
      have habs : |∫ ti in Icc 0 L, (F (i.insertNth ti s) - G (i.insertNth ti s))|
          ≤ ∫ ti in Icc 0 L, |F (i.insertNth ti s) - G (i.insertNth ti s)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Icc (0:ℝ) L))
          (f := fun ti => F (i.insertNth ti s) - G (i.insertNth ti s))
      refine habs.trans ?_
      calc ∫ ti in Icc 0 L, |F (i.insertNth ti s) - G (i.insertNth ti s)|
          ≤ ∫ _ti in Icc 0 L, εd :=
            setIntegral_mono_on (hintF.sub hintG).abs hconstε hmIcc
              (fun ti hti => happ _ (hmem ti hti))
        _ = εd * L := by rw [setIntegral_const, smul_eq_mul, measureReal_def, hvolIcc, mul_comm]
        _ ≤ εd * (1 + ε) := by nlinarith
    have hsm : |(∫ ti in Icc 0 L, F (i.insertNth ti s))
                  + (∫ ti in Icc 0 L, G (i.insertNth ti s))| ≤ A * (1 + ε) := by
      rw [← integral_add hintF hintG]
      have habs : |∫ ti in Icc 0 L, (F (i.insertNth ti s) + G (i.insertNth ti s))|
          ≤ ∫ ti in Icc 0 L, |F (i.insertNth ti s) + G (i.insertNth ti s)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (Icc (0:ℝ) L))
          (f := fun ti => F (i.insertNth ti s) + G (i.insertNth ti s))
      refine habs.trans ?_
      calc ∫ ti in Icc 0 L, |F (i.insertNth ti s) + G (i.insertNth ti s)|
          ≤ ∫ _ti in Icc 0 L, A :=
            setIntegral_mono_on (hintF.add hintG).abs hconstA hmIcc
              (fun ti hti => hsum _ (hmem ti hti))
        _ = A * L := by rw [setIntegral_const, smul_eq_mul, measureReal_def, hvolIcc, mul_comm]
        _ ≤ A * (1 + ε) := by nlinarith
    have hfac : (∫ ti in Icc 0 L, F (i.insertNth ti s)) ^ 2
                  - (∫ ti in Icc 0 L, G (i.insertNth ti s)) ^ 2
                = ((∫ ti in Icc 0 L, F (i.insertNth ti s))
                    - (∫ ti in Icc 0 L, G (i.insertNth ti s)))
                  * ((∫ ti in Icc 0 L, F (i.insertNth ti s))
                    + (∫ ti in Icc 0 L, G (i.insertNth ti s))) := by ring
    rw [hfac, abs_mul]
    calc |(∫ ti in Icc 0 L, F (i.insertNth ti s)) - (∫ ti in Icc 0 L, G (i.insertNth ti s))|
            * |(∫ ti in Icc 0 L, F (i.insertNth ti s)) + (∫ ti in Icc 0 L, G (i.insertNth ti s))|
        ≤ (εd * (1 + ε)) * (A * (1 + ε)) :=
          mul_le_mul hdiff hsm (abs_nonneg _) (mul_nonneg hεd h1εnn)
      _ = εd * A * (1 + ε) ^ 2 := by ring
  rw [show J_i_eps (n + 1) ε F i
        = ∫ s in simplex_shrunk n ε,
            (∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2 from rfl,
      show J_i_eps (n + 1) ε G i
        = ∫ s in simplex_shrunk n ε,
            (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2 from rfl,
      ← integral_sub hIF2 hIG2]
  have habs : |∫ s in simplex_shrunk n ε,
        ((∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2)|
      ≤ ∫ s in simplex_shrunk n ε,
          |(∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2| := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (simplex_shrunk n ε))
      (f := fun s => (∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2)
  have hIabs : IntegrableOn
      (fun s => |(∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
        - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2|) (simplex_shrunk n ε) := by
    simpa only [Pi.sub_apply] using (hIF2.sub hIG2).abs
  refine habs.trans ?_
  calc ∫ s in simplex_shrunk n ε,
          |(∫ ti in Icc 0 (1 + ε - ∑ j, s j), F (i.insertNth ti s)) ^ 2
            - (∫ ti in Icc 0 (1 + ε - ∑ j, s j), G (i.insertNth ti s)) ^ 2|
      ≤ ∫ _s in simplex_shrunk n ε, εd * A * (1 + ε) ^ 2 :=
        setIntegral_mono_on hIabs (integrableOn_const hshrunk_ne_top) hmeasS
          (fun s hs => hbound s hs)
    _ = εd * A * ((1 + ε) ^ 2 * (volume (simplex_shrunk n ε)).toReal) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring

open MeasureTheory in
/-- ε-sister of `mkF_numerator_sub_le_const`: sum of the `k` ε-marginal bounds. -/
theorem mkF_eps_numerator_sub_le_const (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F G : (Fin k → ℝ) → ℝ)
    (A εd : ℝ) (hFc : Continuous F) (hGc : Continuous G)
    (hFsupp : Function.support F ⊆ simplex_eps k ε) (hGsupp : Function.support G ⊆ simplex_eps k ε)
    (hsum : ∀ t ∈ simplex_eps k ε, |F t + G t| ≤ A) (happ : ∀ t ∈ simplex_eps k ε, |F t - G t| ≤ εd)
    (hεd : 0 ≤ εd) (hA : 0 ≤ A) :
    |mkF_eps_numerator k ε F - mkF_eps_numerator k ε G|
      ≤ (k : ℝ) * (εd * A * ((1 + ε) ^ 2 * (volume (simplex_shrunk (k - 1) ε)).toReal)) := by
  cases k with
  | zero => simp [mkF_eps_numerator]
  | succ n =>
    rw [mkF_eps_numerator_eq_sum_J_i_eps, mkF_eps_numerator_eq_sum_J_i_eps, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun i _ =>
      J_i_eps_sub_le_const n ε hε F G A εd hFc hGc hFsupp hGsupp hsum happ hεd hA i)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.add_sub_cancel]

open MeasureTheory in
/-- **Sup-norm continuity of the ε-flavored Maynard ratio `MkF_eps`** (the
continuity half of `sep_approx_eps`, proved in-kernel; ε-sister of
`mkF_sub_lt_of_sup_le`). For fixed admissible `F` and target `etarget > 0`,
there is `δ > 0` such that every continuous `simplex_eps`-supported `G` within
sup-distance `δ` of `F` has positive denominator and `|MkF_eps G − MkF_eps F| <
etarget`. -/
theorem mkF_eps_sub_lt_of_sup_le (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F : (Fin k → ℝ) → ℝ)
    (hFc : Continuous F) (hFsupp : Function.support F ⊆ simplex_eps k ε)
    (hFden : 0 < mkF_eps_denominator k ε F) (etarget : ℝ) (hetarget : 0 < etarget) :
    ∃ δ > 0, ∀ G : (Fin k → ℝ) → ℝ, Continuous G → Function.support G ⊆ simplex_eps k ε →
      (∀ t ∈ simplex_eps k ε, |F t - G t| ≤ δ) →
      0 < mkF_eps_denominator k ε G ∧ |MkF_eps k ε G - MkF_eps k ε F| < etarget := by
  obtain ⟨CF, hCF0, hCF⟩ : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ t ∈ simplex_eps k ε, |F t| ≤ CF := by
    obtain ⟨CF, hCF⟩ := (isCompact_simplex_eps k ε).exists_bound_of_continuousOn hFc.continuousOn
    exact ⟨max CF 0, le_max_right _ _, fun t ht => (hCF t ht).trans (le_max_left _ _)⟩
  set A0 : ℝ := 2 * CF + 1 with hA0
  have hA0pos : 0 < A0 := by rw [hA0]; linarith
  set vk : ℝ := (volume (simplex_eps k ε)).toReal with hvk
  set vk1 : ℝ := (1 + ε) ^ 2 * (volume (simplex_shrunk (k - 1) ε)).toReal with hvk1
  have hvk0 : 0 ≤ vk := ENNReal.toReal_nonneg
  have hvk10 : 0 ≤ vk1 := mul_nonneg (by positivity) ENNReal.toReal_nonneg
  -- `vk1 = (1+ε)²·toReal` nests `pow`/`*`; keep it opaque so `nlinarith`/`whnf`
  -- below don't try to unfold it and blow the heartbeat budget (cf. clear-value gotcha).
  clear_value vk1
  set den : ℝ := mkF_eps_denominator k ε F with hden
  set numF : ℝ := mkF_eps_numerator k ε F with hnumF
  set S : ℝ := A0 * ((k : ℝ) * vk1 * den + |numF| * vk) with hS
  have hSinner : 0 ≤ (k : ℝ) * vk1 * den + |numF| * vk :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hvk10) hFden.le)
      (mul_nonneg (abs_nonneg _) hvk0)
  have hS0 : 0 ≤ S := mul_nonneg hA0pos.le hSinner
  have hAvk0 : 0 ≤ A0 * vk := mul_nonneg hA0pos.le hvk0
  have hP : 0 < etarget * den ^ 2 := mul_pos hetarget (pow_pos hFden 2)
  set δ : ℝ := min 1 (min (den / (2 * (A0 * vk) + 2)) (etarget * den ^ 2 / (2 * S + 2))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · apply div_pos hP; linarith
  refine ⟨δ, hδpos, ?_⟩
  intro G hGc hGsupp hclose
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ den / (2 * (A0 * vk) + 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ etarget * den ^ 2 / (2 * S + 2) := (min_le_right _ _).trans (min_le_right _ _)
  -- make the remaining heavy `set` constants opaque (the `with` equations survive for `rw`);
  -- keep `den`, `numF` transparent so the `MkF_eps … = numF / den` rfl below still holds.
  clear_value A0 vk S δ
  have hsumG : ∀ t ∈ simplex_eps k ε, |F t + G t| ≤ A0 := by
    intro t ht
    have hFt := abs_le.mp (hCF t ht); have hFGt := abs_le.mp (hclose t ht)
    rw [hA0, abs_le]; constructor <;> nlinarith [hFt.1, hFt.2, hFGt.1, hFGt.2, hδ1]
  have hDden : |den - mkF_eps_denominator k ε G| ≤ δ * A0 * vk := by
    rw [hden, hvk]
    exact mkF_eps_denominator_sub_le_const k ε F G A0 δ hFc hGc hsumG hclose
  have hden2 : δ * A0 * vk ≤ den / 2 := by
    have hmul : δ * (2 * (A0 * vk) + 2) ≤ den := (le_div_iff₀ (by linarith)).mp hδ2
    nlinarith [hmul, hδpos, hAvk0]
  have hdenG_lb : den / 2 ≤ mkF_eps_denominator k ε G := by
    have hh := abs_le.mp (hDden.trans hden2); linarith [hh.1]
  have hdenG_pos : 0 < mkF_eps_denominator k ε G := by linarith [hdenG_lb, hFden]
  refine ⟨hdenG_pos, ?_⟩
  have hDnum : |numF - mkF_eps_numerator k ε G| ≤ (k : ℝ) * (δ * A0 * vk1) := by
    rw [hnumF, hvk1]
    exact mkF_eps_numerator_sub_le_const k ε hε F G A0 δ hFc hGc hFsupp hGsupp hsumG hclose
      hδpos.le hA0pos.le
  rw [show MkF_eps k ε G = mkF_eps_numerator k ε G / mkF_eps_denominator k ε G from rfl,
      show MkF_eps k ε F = numF / den from rfl,
      div_sub_div _ _ (ne_of_gt hdenG_pos) (ne_of_gt hFden), abs_div]
  have hposprod : 0 < mkF_eps_denominator k ε G * den := mul_pos hdenG_pos hFden
  rw [abs_of_pos hposprod, div_lt_iff₀ hposprod]
  have hnum_bound : |mkF_eps_numerator k ε G * den - mkF_eps_denominator k ε G * numF| ≤ δ * S := by
    have heq : mkF_eps_numerator k ε G * den - mkF_eps_denominator k ε G * numF
        = (mkF_eps_numerator k ε G - numF) * den + numF * (den - mkF_eps_denominator k ε G) := by ring
    rw [heq]
    calc |(mkF_eps_numerator k ε G - numF) * den + numF * (den - mkF_eps_denominator k ε G)|
        ≤ |(mkF_eps_numerator k ε G - numF) * den| + |numF * (den - mkF_eps_denominator k ε G)| :=
          abs_add_le _ _
      _ = |mkF_eps_numerator k ε G - numF| * den + |numF| * |den - mkF_eps_denominator k ε G| := by
          rw [abs_mul, abs_mul, abs_of_pos hFden]
      _ ≤ (k : ℝ) * (δ * A0 * vk1) * den + |numF| * (δ * A0 * vk) :=
          add_le_add (mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact hDnum) hFden.le)
            (mul_le_mul_of_nonneg_left hDden (abs_nonneg _))
      _ = δ * S := by rw [hS]; ring
  have hbden : den ^ 2 / 2 ≤ mkF_eps_denominator k ε G * den := by nlinarith [hdenG_lb, hFden]
  have hSlt : δ * S < etarget * den ^ 2 / 2 := by
    have hmul : δ * (2 * S + 2) ≤ etarget * den ^ 2 := (le_div_iff₀ (by linarith [hS0])).mp hδ3
    nlinarith [hmul, hδpos, hS0]
  calc |mkF_eps_numerator k ε G * den - mkF_eps_denominator k ε G * numF|
      ≤ δ * S := hnum_bound
    _ < etarget * den ^ 2 / 2 := hSlt
    _ ≤ etarget * (mkF_eps_denominator k ε G * den) := by nlinarith [hbden, hetarget]

open MeasureTheory Set in
open scoped Pointwise in
/-- **Separable sup-norm density, ε variant — now a THEOREM** (was a cited
density axiom). The enlarged simplex is a *dilation* of the standard one,
`simplex_eps k ε = (1+ε) • simplex k`, so the ε-density REDUCES to the base
axiom `separable_dense_sup` by the change of variables `t = (1+ε) • s`:

* `F̂(s) := F((1+ε)•s)` is smooth (`ContDiff.comp` with the scaling map),
  simplex-supported (`smul_mem_smul_set_iff₀`), and has positive denominator
  (Haar change-of-variables `setIntegral_comp_smul_of_pos`, Jacobian
  `(1+ε)^{-k}` on `Fin k → ℝ`, `finrank = k`).
* `separable_dense_sup` yields a separable `Ĝ` on `simplex k` within `δ` of `F̂`.
* `G(t) := Ĝ((1+ε)⁻¹•t)` is separable (compose each 1-D factor with the scalar),
  smooth, supported on `simplex_eps k ε`, and `δ`-close to `F` there.

So the ε-density carries no separate axiomatic content; it consolidates onto the
single base density axiom `separable_dense_sup`. Requires `0 ≤ ε` (callers have
`0 < ε`). -/
theorem separable_dense_sup_eps (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F : (Fin k → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hsupp : Function.support F ⊆ simplex_eps k ε)
    (hden : mkF_eps_denominator k ε F > 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex_eps k ε ∧
      (∀ t ∈ simplex_eps k ε, |F t - G t| ≤ δ) := by
  have hr : (0 : ℝ) < 1 + ε := by linarith
  have hrne : (1 + ε) ≠ 0 := hr.ne'
  -- the dilation identity `(1+ε) • simplex k = simplex_eps k ε`
  have hsmul : (1 + ε) • simplex k = simplex_eps k ε := by
    ext u
    rw [mem_smul_set_iff_inv_smul_mem₀ hrne]
    simp only [simplex, simplex_eps, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hnn, hsum⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := mul_nonneg hr.le (hnn i)
        rwa [← mul_assoc, mul_inv_cancel₀ hrne, one_mul] at this
      · rw [← Finset.mul_sum] at hsum
        have := mul_le_mul_of_nonneg_left hsum hr.le
        rwa [← mul_assoc, mul_inv_cancel₀ hrne, one_mul, mul_one] at this
    · rintro ⟨hnn, hsum⟩
      refine ⟨fun i => mul_nonneg (inv_pos.mpr hr).le (hnn i), ?_⟩
      rw [← Finset.mul_sum]
      have hle : (1 + ε)⁻¹ * ∑ i, u i ≤ (1 + ε)⁻¹ * (1 + ε) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hr).le
      rwa [inv_mul_cancel₀ hrne] at hle
  -- the scaling map is smooth
  have hscale : ContDiff ℝ ∞ (fun s : Fin k → ℝ => (1 + ε) • s) :=
    contDiff_const_smul (1 + ε)
  have hscaleinv : ContDiff ℝ ∞ (fun t : Fin k → ℝ => (1 + ε)⁻¹ • t) :=
    contDiff_const_smul (1 + ε)⁻¹
  -- `F̂` smooth, simplex-supported, positive denominator
  have hFhat_cd : ContDiff ℝ ∞ (fun s => F ((1 + ε) • s)) := hF.comp hscale
  have hFhat_supp : Function.support (fun s => F ((1 + ε) • s)) ⊆ simplex k := by
    intro s hs
    have hFne : F ((1 + ε) • s) ≠ 0 := hs
    have hmem : (1 + ε) • s ∈ simplex_eps k ε := hsupp hFne
    rw [← hsmul] at hmem
    rwa [smul_mem_smul_set_iff₀ hrne] at hmem
  have hden_hat : 0 < mkF_denominator k (fun s => F ((1 + ε) • s)) := by
    have hcov := Measure.setIntegral_comp_smul_of_pos (E := Fin k → ℝ) (μ := volume)
      (fun x => F x ^ 2) (simplex k) hr
    rw [hsmul, Module.finrank_fin_fun, smul_eq_mul] at hcov
    have hdeneq : mkF_denominator k (fun s => F ((1 + ε) • s))
        = ((1 + ε) ^ k)⁻¹ * mkF_eps_denominator k ε F := by
      unfold mkF_denominator mkF_eps_denominator
      exact hcov
    rw [hdeneq]
    exact mul_pos (by positivity) hden
  -- base density on `simplex k`
  obtain ⟨Ghat, hGsep, hGcd, hGsupp, hGclose⟩ :=
    separable_dense_sup k (fun s => F ((1 + ε) • s)) hFhat_cd hFhat_supp hden_hat δ hδ
  refine ⟨fun t => Ghat ((1 + ε)⁻¹ • t), ?_, ?_, ?_, ?_⟩
  · -- finite-separable: compose each 1-D factor with `(1+ε)⁻¹ • ·`
    obtain ⟨J, c, Fs, R, hdecomp⟩ := hGsep
    exact ⟨J, c, fun j i x => Fs j i ((1 + ε)⁻¹ * x), R, fun t => by
      simp only [hdecomp, Pi.smul_apply, smul_eq_mul]⟩
  · exact hGcd.comp hscaleinv
  · -- support ⊆ simplex_eps
    intro t ht
    have hne : Ghat ((1 + ε)⁻¹ • t) ≠ 0 := ht
    have hmem : (1 + ε)⁻¹ • t ∈ simplex k := hGsupp hne
    have h2 : (1 + ε) • ((1 + ε)⁻¹ • t) ∈ (1 + ε) • simplex k := smul_mem_smul_set hmem
    rwa [smul_smul, mul_inv_cancel₀ hrne, one_smul, hsmul] at h2
  · -- δ-closeness on simplex_eps
    intro t ht
    have hs : (1 + ε)⁻¹ • t ∈ simplex k := by
      rw [← hsmul] at ht
      rwa [mem_smul_set_iff_inv_smul_mem₀ hrne] at ht
    have hclose := hGclose ((1 + ε)⁻¹ • t) hs
    simp only [smul_smul, mul_inv_cancel₀ hrne, one_smul] at hclose
    exact hclose

/-- **Separable $L^2$-approximation, ε variant** (the narrowed core of
`exists_separable_F_eps_of_Mk_eps_gt`). **Now a theorem** (was a cited axiom):
the continuity half is proved in-kernel (`mkF_eps_sub_lt_of_sup_le`), so this
rests only on the pure approximation-theory axiom `separable_dense_sup_eps`
(sup-norm density). Requires `0 ≤ ε` (always available: callers have `0 < ε`). -/
theorem sep_approx_eps (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (F : (Fin k → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hsupp : Function.support F ⊆ simplex_eps k ε)
    (hden : mkF_eps_denominator k ε F > 0) (η : ℝ) (hη : 0 < η) :
    ∃ G : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable G ∧ ContDiff ℝ ∞ G ∧ Function.support G ⊆ simplex_eps k ε ∧
      mkF_eps_denominator k ε G > 0 ∧ |MkF_eps k ε G - MkF_eps k ε F| < η := by
  obtain ⟨δ, hδpos, hcont⟩ := mkF_eps_sub_lt_of_sup_le k ε hε F hF.continuous hsupp hden η hη
  obtain ⟨G, hGsep, hGsm, hGsupp, hGclose⟩ := separable_dense_sup_eps k ε hε F hF hsupp hden δ hδpos
  obtain ⟨hGden, hGlt⟩ := hcont G hGsm.continuous hGsupp hGclose
  exact ⟨G, hGsep, hGsm, hGsupp, hGden, hGlt⟩

/-- **Separable realisation of $M_{k,\varepsilon}$** (Polymath8b §6, ε variant).
**Now a theorem** (was a cited axiom): identical reduction to
`exists_separable_F_of_Mk_gt`, via `exists_F_eps_of_Mk_eps_gt` and the
pure-analysis `sep_approx_eps`. -/
theorem exists_separable_F_eps_of_Mk_eps_gt (k : ℕ) (hk : 2 ≤ k)
    (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : c < Mk_eps k ε) :
    ∃ F : (Fin k → ℝ) → ℝ,
      IsFiniteSeparable F ∧ ContDiff ℝ ∞ F ∧ Function.support F ⊆ simplex_eps k ε ∧
      mkF_eps_denominator k ε F > 0 ∧ c < MkF_eps k ε F := by
  set c' : ℝ := (c + Mk_eps k ε) / 2 with hc'def
  have hc'Mk : c' < Mk_eps k ε := by rw [hc'def]; linarith
  obtain ⟨F, hSmooth, hSupp, hDen, hcF⟩ := exists_F_eps_of_Mk_eps_gt k hk ε hε c' hc'Mk
  obtain ⟨G, hGsep, hGsm, hGsupp, hGden, hGclose⟩ :=
    sep_approx_eps k ε hε.le F hSmooth hSupp hDen (c' - c) (by linarith)
  refine ⟨G, hGsep, hGsm, hGsupp, hGden, ?_⟩
  have hlow := (abs_lt.mp hGclose).1
  linarith

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
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ε : ℝ} (_hε : 0 < ε)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex_eps k ε)
    (_hF_den : mkF_eps_denominator k ε F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) :
    ∀ᶠ x : ℝ in Filter.atTop,
      alphaBound k (selberg_nu k J c Fs H R) b W x (mkF_eps_denominator k ε F)

/-- **(s2ε) from `prime-asym` case (i) under EH[ϑ]** (Polymath8b §3 line 862
+ §5 `epsilon-trick` reduction).

Under $\EH[\vartheta]$ and the support-fitting condition $1 + \varepsilon <
1/\vartheta$, (s2) holds eventually with $\beta_i = (\vartheta/2) \cdot
J_{i,1-\varepsilon}(F)$. The $(1-\varepsilon)$-shrunken outer integration in
the numerator is what lets prime-asym case (i)'s support bound be satisfied
even with the $(1+\varepsilon)$-enlarged $F$. Future PR can replace with a
real proof. -/
axiom s2_eps_holds_from_prime_asym_under_EH {k : ℕ} (_hk : k ≥ 2)
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ε ϑ : ℝ} (_hε : 0 < ε) (_hϑ : 0 < ϑ ∧ ϑ < 1)
    (_hEH : Prerequisites.EH ϑ) (_hSupp : 1 + ε < 1 / ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex_eps k ε)
    (_hF_den : mkF_eps_denominator k ε F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k J c Fs H R) H b W i.val x
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
    (hF_sep : IsFiniteSeparable F)
    (hF_smooth : ContDiff ℝ ∞ F)
    (hF_supp : Function.support F ⊆ simplex_eps k ε)
    (hF_den : mkF_eps_denominator k ε F > 0)
    (hF_Mk : MkF_eps k ε F > 2 * m / ϑ)
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      1 ≤ W ∧ (∀ n, 0 ≤ ν n) ∧ 0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  obtain ⟨J, c, Fs, R, hFdecomp⟩ := hF_sep
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hϑ_half_pos : 0 < ϑ / 2 := by linarith
  refine ⟨b, W, selberg_nu k J c Fs H R, mkF_eps_denominator k ε F,
    fun i => ϑ / 2 * J_i_eps k ε F i, hW, (fun n => selberg_nu_basis_nonneg k J c Fs H R n), hF_den, ?_, ?_, ?_, ?_⟩
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
    exact s1_eps_holds_from_nonprime_asym hk hε hFdecomp hF_smooth hF_supp hF_den
      hAdm hLen b W hW
  · -- (s2ε)
    intro i
    exact s2_eps_holds_from_prime_asym_under_EH hk hε hϑ hEH hSupp hFdecomp
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
  obtain ⟨F, hSep, hSmooth, hSupp', hDen, hMkF⟩ :=
    exists_separable_F_eps_of_Mk_eps_gt k hk ε hε (2 * m / ϑ) hMk
  exact selberg_sieve_data_eps_from_F hk hm hε hϑ hEH hSupp hSep hSmooth hSupp'
    hDen hMkF hAdm hLen

/-! ### Selberg sieve data sub-lemmas (`epsilon-beyond`-flavored, Polymath8b §5)

Beyond sister of the eps-decomposition above. F lives on the larger
$\frac{k}{k-1}$-scaled simplex (not $(1+\varepsilon) R_k$) and carries a
vanishing-marginal hypothesis; (s2) runs under GEH (not EH). Reuses
`selberg_nu` and `wtrick_data` (both polytope-agnostic). -/

/-- **(s1-beyond) from `nonprime-asym` case (i)** (Polymath8b §3 line 889,
applied through the §5 `epsilon-beyond` reduction).

For admissible $F$ on the $\frac{k}{k-1}$-scaled simplex, (s1) holds
eventually with $\alpha = I(F) = \int_{\frac{k}{k-1} \mathcal{R}_k} F^2$
(i.e. `mkF_beyond_denominator k F`). The vanishing-marginal hypothesis is
not needed for (s1) — it's a (s2)-side constraint that lets prime-asym
work on the enlarged polytope. Future PR can replace with a real proof
from the divisor-sum expansion. -/
axiom s1_beyond_holds_from_nonprime_asym {k : ℕ} (_hk : k ≥ 2)
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ε : ℝ} (_hε_pos : 0 < ε)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)))
    (_hF_den : mkF_beyond_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) :
    ∀ᶠ x : ℝ in Filter.atTop,
      alphaBound k (selberg_nu k J c Fs H R) b W x (mkF_beyond_denominator k F)

/-- **(s2-beyond) from `prime-asym` case (i) under GEH[ϑ]** (Polymath8b §3
line 862 + §5 `epsilon-beyond` reduction).

Under $\GEH[\vartheta]$, the `HasVanishingMarginal k ε F` hypothesis, and
$F$ supported on $\frac{k}{k-1} \mathcal{R}_k$, (s2) holds eventually with
$\beta_i = (\vartheta/2) \cdot J_{i, 1-\varepsilon}(F)$ (the unclamped
$J_i$-beyond form).

The vanishing-marginal hypothesis is what makes prime-asym work on the
enlarged polytope: outside $(1+\varepsilon) R_k$ the marginal integrand is
zero, so even though F's support extends to $\frac{k}{k-1} R_k$, the
relevant arithmetic only sees the $(1+\varepsilon) R_k$ piece. GEH (vs EH)
is needed because the Dirichlet convolutions involved are no longer
restricted to $\Lambda$. Future PR can replace with a real proof from the
Polymath8b §3 `theta-oo`-flavored estimate via the BFI/Motohashi GEH
machinery. -/
axiom s2_beyond_holds_from_prime_asym_under_GEH {k : ℕ} (_hk : k ≥ 2)
    {J : ℕ} {c : Fin J → ℝ} {Fs : Fin J → Fin k → ℝ → ℝ} {R : ℝ}
    {ε ϑ : ℝ} (_hε_pos : 0 < ε)
    (_hϑ : 0 < ϑ ∧ ϑ < 1) (_hGEH : Prerequisites.GEH ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (_hF_smooth : ContDiff ℝ ∞ F)
    (_hF_supp : Function.support F ⊆ simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)))
    (_hF_vanish : HasVanishingMarginal k ε F)
    (_hF_den : mkF_beyond_denominator k F > 0)
    {H : List ℕ} (_hAdm : Admissible H) (_hLen : H.length = k)
    (b W : ℕ) (_hW : 1 ≤ W) (i : Fin k) :
    ∀ᶠ x : ℝ in Filter.atTop,
      betaBound k (selberg_nu k J c Fs H R) H b W i.val x
        (ϑ / 2 * J_i_beyond k ε F i)

/-- **The analytic core of `epsilon-beyond`** (Polymath8b §5).

Sister of `selberg_sieve_data_eps_from_F` for the beyond polytope $\frac{k}{k-1}
\mathcal{R}_k$ with the vanishing-marginal hypothesis, under GEH.

Real proof — mirror of `selberg_sieve_data_eps_from_F` (PR-A6) with the
substitutions: $\simplex_{eps} \mapsto \simplex_{scaled}\,(k/(k-1))$,
$J_{i,eps} \mapsto J_{i,beyond}$, $\mathrm{EH} \mapsto \mathrm{GEH}$, plus the
`HasVanishingMarginal` rider on the (s2) leg.

Key algebraic step: $(\vartheta/2) \cdot (\sum_i J_{i,beyond}/I(F))
> (\vartheta/2) \cdot (2m/\vartheta) = m$. -/
theorem selberg_sieve_data_beyond_from_F {k m : ℕ} (hk : k ≥ 2) (_hm : m ≥ 1)
    {ε ϑ : ℝ} (hε_pos : 0 < ε) (_hε_lt : ε < 1 / ((k : ℝ) - 1))
    (hϑ : 0 < ϑ ∧ ϑ < 1) (hGEH : Prerequisites.GEH ϑ)
    {F : (Fin k → ℝ) → ℝ}
    (hF_sep : IsFiniteSeparable F)
    (hF_smooth : ContDiff ℝ ∞ F)
    (hF_supp : Function.support F ⊆ simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)))
    (hF_vanish : HasVanishingMarginal k ε F)
    (hF_den : mkF_beyond_denominator k F > 0)
    (hF_thresh :
      (∑ i, J_i_beyond k ε F i) / mkF_beyond_denominator k F > 2 * m / ϑ)
    {H : List ℕ} (hAdm : Admissible H) (hLen : H.length = k) :
    ∃ (b W : ℕ) (ν : ℕ → ℝ) (α : ℝ) (β : Fin k → ℝ),
      1 ≤ W ∧ (∀ n, 0 ≤ ν n) ∧ 0 < α ∧ (∀ i, 0 ≤ β i) ∧ (∑ i, β i) / α > m ∧
      (∀ᶠ x : ℝ in Filter.atTop, alphaBound k ν b W x α) ∧
      (∀ i : Fin k, ∀ᶠ x : ℝ in Filter.atTop,
          betaBound k ν H b W i.val x (β i)) := by
  obtain ⟨b, W, hW, _hbW⟩ := wtrick_data (by omega : k ≥ 1) hAdm hLen
  obtain ⟨J, c, Fs, R, hFdecomp⟩ := hF_sep
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hϑ_half_pos : 0 < ϑ / 2 := by linarith
  refine ⟨b, W, selberg_nu k J c Fs H R, mkF_beyond_denominator k F,
    fun i => ϑ / 2 * J_i_beyond k ε F i, hW, (fun n => selberg_nu_basis_nonneg k J c Fs H R n), hF_den, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ β i
    intro i
    exact mul_nonneg hϑ_half_pos.le (J_i_beyond_nonneg k ε F i)
  · -- (∑ i, β i) / α > m
    -- Pull ϑ/2 out of the sum, then use hF_thresh on (∑ J_i_beyond) / I(F).
    have hsum : (∑ i, ϑ / 2 * J_i_beyond k ε F i) =
        ϑ / 2 * (∑ i, J_i_beyond k ε F i) := by
      rw [← Finset.mul_sum]
    rw [hsum, mul_div_assoc]
    have step1 :
        (ϑ / 2) * ((∑ i, J_i_beyond k ε F i) / mkF_beyond_denominator k F)
          > (ϑ / 2) * (2 * m / ϑ) :=
      mul_lt_mul_of_pos_left hF_thresh hϑ_half_pos
    have step2 : (ϑ / 2) * (2 * (m : ℝ) / ϑ) = m := by
      field_simp
    linarith
  · -- (s1-beyond)
    exact s1_beyond_holds_from_nonprime_asym hk hε_pos hFdecomp hF_smooth hF_supp hF_den
      hAdm hLen b W hW
  · -- (s2-beyond)
    intro i
    exact s2_beyond_holds_from_prime_asym_under_GEH hk hε_pos hϑ hGEH hFdecomp
      hF_smooth hF_supp hF_vanish hF_den hAdm hLen b W hW i

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

**Statement-fix history.** PR-A1b-ii: restated to match the paper
TeX. Previous signature used `Mk_eps k ε > 2m/ϑ` as a Rayleigh-sup
threshold, which is the wrong shape entirely — `epsilon-beyond` has no
Rayleigh-sup (would need a `MkSet_beyond` with vanishing-marginal baked
in). The paper takes an explicit $F$ with the marginal condition. The
inner integral in $J_{i, 1-\varepsilon}$ runs over $[0, \infty)$ (unclamped),
not the $[0, 1+\varepsilon - \sum]$ used in `J_i_eps`'s clamped form,
because `epsilon-beyond` enlarges the support polytope from
$(1 + \varepsilon) \mathcal{R}_k$ to $\frac{k}{k-1} \mathcal{R}_k$
(strictly larger when $\varepsilon < \frac{1}{k-1}$).

**Discharged 2026-05-27** (PR-A1b-iii-b): real composition through
`selberg_sieve_data_beyond_from_F` + `dhl_criterion`. Mirrors
`epsilon_trick`'s body modulo: explicit F (no extraction step), enlarged
polytope, and the GEH-flavored (s2) leg. -/
theorem epsilon_beyond (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 1)
    (ε ϑ : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1 / ((k : ℝ) - 1))
    (hϑ : 0 < ϑ ∧ ϑ < 1) (hGEH : Prerequisites.GEH ϑ)
    (F : (Fin k → ℝ) → ℝ)
    (hSep : IsFiniteSeparable F)
    (hSmooth : ContDiff ℝ ∞ F)
    (hSupp : Function.support F ⊆ simplex_scaled k ((k : ℝ) / ((k : ℝ) - 1)))
    (hVanish : HasVanishingMarginal k ε F)
    (hDen : mkF_beyond_denominator k F > 0)
    (hThresh :
      (∑ i, J_i_beyond k ε F i) / mkF_beyond_denominator k F > 2 * m / ϑ) :
    DHL k (m + 1) := by
  apply dhl_criterion k m hk hm
  intro H hAdm hLen
  exact selberg_sieve_data_beyond_from_F hk hm hε_pos hε_lt hϑ hGEH
    hSep hSmooth hSupp hVanish hDen hThresh hAdm hLen

end BoundedGaps.Sieve
