/-
# Maynard 2014 — Small gaps between primes.

Maynard's main theorem (as restated in Polymath8b Theorem 1.2, "Maynard's
theorem"). The multidimensional Selberg sieve, no MPZ needed — only
Bombieri-Vinogradov.

Reference: Maynard, "Small gaps between primes", Annals of Math 181 (2015),
arXiv:1311.4600.
Local copy: [../papers/pdf/maynard-2015-small-gaps.pdf](../papers/pdf/maynard-2015-small-gaps.pdf)
LaTeX source: [../papers/src/maynard-1311.4600/Small_gaps_between_primes.tex](../papers/src/maynard-1311.4600/Small_gaps_between_primes.tex)
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Prerequisites
import BoundedGaps.Sieve
import BoundedGaps.Polymath8b
import BoundedGaps.Mk5Witness

namespace BoundedGaps.Maynard

open BoundedGaps

/-! ### Unconditional (Polymath8b Theorem 1.2 (i)-(ii))

Maynard's bounds are *weaker* than the Polymath8b refinements, so the
unconditional and EH-asymptotic cases here are dispatched by upcasting
from `Polymath8b`'s stronger results. The only genuinely Maynard-specific
bound this file proves on its own is $H_1 \le 12$ under EH (`H1_le_12_under_EH`):
Maynard 2014 obtains this via $M_5 > 2$, which Polymath8b §1's
**unconditional** $H_1 \le 246$ and **GEH** $H_1 \le 6$ chains do not
themselves give under plain EH. -/

/-- **(i)** $H_1 \le 600$. Maynard 2014's headline result; subsumed by
Polymath8b's $H_1 \le 246$. -/
theorem H1_le_600 : liminfGap 1 ≤ (600 : ℕ∞) :=
  le_trans Polymath8b.H1_le_246
    (by exact_mod_cast (by norm_num : (246 : ℕ) ≤ 600))

/-- **(ii)** $H_m \le C m^3 e^{4m}$ for all $m \ge 1$, effective $C$.

Maynard 2014's asymptotic bound; subsumed by Polymath8b's
$H_m \le C m \exp((4 - 28/157) m)$. For $m \ge 1$, $m \cdot \exp((4 - 28/157)m)
\le m^3 \cdot \exp(4m)$ (since $m \le m^3$ and $4 - 28/157 < 4$). -/
theorem Hm_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤
        ENNReal.ofReal (C * (m : ℝ)^3 * Real.exp (4 * m)) := by
  obtain ⟨C, hC, hPoly⟩ := Polymath8b.Hm_asymptotic_unconditional
  refine ⟨C, hC, fun m hm => ?_⟩
  refine le_trans (hPoly m hm) ?_
  apply ENNReal.ofReal_le_ofReal
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hm3 : (m : ℝ) ≤ m^3 := by
    have h := pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 3)
    simpa using h
  have hExp : Real.exp ((4 - 28/157) * m) ≤ Real.exp (4 * m) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h1 : C * m * Real.exp ((4 - 28/157) * m) ≤ C * m^3 * Real.exp (4 * m) := by
    have : C * (m : ℝ) * Real.exp ((4 - 28/157) * m) ≤
        C * (m : ℝ)^3 * Real.exp ((4 - 28/157) * m) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left hm3 hC.le
    refine le_trans this ?_
    apply mul_le_mul_of_nonneg_left hExp
    positivity
  exact h1

/-! ### Maynard's $k = 5$ flagship infrastructure (for `H1_le_12_under_EH`)

The optimal $5$-tuple is $(0, 4, 6, 10, 12)$ — admissible, diameter $12$.
Together with $M_5 > 2/\vartheta$ (Maynard 2015 §1, cited as
`mk_5_witness_under_EH`) and `Sieve.maynard_thm` under EH, this gives
$\DHL[5, 2]$ → $H_1 \le 12$ under EH. -/

/-- Maynard's optimal 5-tuple of diameter 12. -/
def tuple_5 : List ℕ := [0, 4, 6, 10, 12]

theorem tuple_5_length : tuple_5.length = 5 := by decide
theorem tuple_5_diameter : diameter tuple_5 = 12 := by decide
theorem tuple_5_sorted : tuple_5.Pairwise (· < ·) := by decide

/-- $(0, 4, 6, 10, 12)$ is admissible: misses class 1 mod 2 (all even),
class 2 mod 3 ($\{0,1,0,1,0\}$), class 3 mod 5 ($\{0,4,1,0,2\}$).
For $p \ge 7$, pigeonhole closes it (5 offsets, $\ge 7$ classes). -/
theorem tuple_5_admissible : Admissible tuple_5 := by
  apply admissible_of_check_small_primes tuple_5_sorted
  intro p hp hple
  rw [tuple_5_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

/-- $H(5) \le 12$: the Maynard 5-tuple of diameter 12 is admissible.

The matching lower bound $H(5) \ge 12$ (so equality, $H(5) = 12$) is a
classical observation cited in Maynard 2015 §1 — not needed for
`H1_le_12_under_EH`, which only consumes the upper bound. -/
theorem narrowness_5_le_12 : narrowness 5 ≤ 12 :=
  narrowness_le_of_admissible_tuple tuple_5_admissible tuple_5_length tuple_5_diameter

/-- **$M_5 > 2/\vartheta$ under EH** (Maynard 2015 Theorem 1.1 + §1 discussion).

**Discharged 2026-05-31** (was `axiom`): `mk_5_witness_under_EH` is now a real
theorem proved in `BoundedGaps.Mk5Witness` (same namespace) via an explicit
degree-3 polynomial witness `P5` with `polynomialMkF P5 = 12048682945/6016885374
> 2`, chained through `Mk_ge_polynomialMkF`. Re-exported here for its consumers
below. -/
example : ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 5 > 2 * 1 / ϑ :=
  mk_5_witness_under_EH

/-- Under EH: **$\DHL[5, 2]$**. Blueprint: `Sieve.maynard_thm` at
$k = 5, m = 1$ with the Maynard $M_5 > 2/\vartheta$ witness. Parallel
to the existing `Polymath8b.dhl_*_under_EH` chain for $k = 54$, etc. -/
theorem dhl_5_2_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 5 2 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_5_witness_under_EH
  exact Sieve.maynard_thm 5 1 (by norm_num) (by norm_num) ϑ hϑ (hEH ϑ hϑ)
    (by exact_mod_cast hMk)

/-! ### Under EH (Polymath8b Theorem 1.2 (iii)-(v)) -/

/-- **(iii)** Under EH: $H_1 \le 12$.

Maynard 2014's headline conditional bound, via the $k = 5$ chain
($M_5 > 2$ gives $\DHL[5, 2]$ under EH, and the optimal 5-tuple
$(0, 4, 6, 10, 12)$ has diameter 12). Polymath8b's stronger
**unconditional** $H_1 \le 246$ does NOT subsume this (12 < 246) and
the **GEH** $H_1 \le 6$ requires the stronger GEH hypothesis. Genuinely
Maynard-specific.

**Discharged 2026-05-27** via the new k=5 flagship chain above
(`dhl_5_2_under_EH` + `narrowness_5_le_12`). -/
theorem H1_le_12_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 1 ≤ (12 : ℕ∞) := by
  have hDHL : DHL 5 2 := dhl_5_2_under_EH hEH
  have h1 : liminfGap 1 ≤ (narrowness 5 : ℕ∞) :=
    dhl_implies_liminfGap 5 1 (by norm_num) hDHL
  calc liminfGap 1
      ≤ (narrowness 5 : ℕ∞) := h1
    _ ≤ (12 : ℕ∞) := by exact_mod_cast narrowness_5_le_12

/-- **(iv)** Under EH: $H_2 \le 600$. Subsumed by Polymath8b's
$H_2 \le 270$ under EH. -/
theorem H2_le_600_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 2 ≤ (600 : ℕ∞) :=
  le_trans (Polymath8b.H2_le_270_under_EH hEH)
    (by exact_mod_cast (by norm_num : (270 : ℕ) ≤ 600))

/-- **(v)** Under EH: $H_m \le C m^3 e^{2m}$ for all $m \ge 1$.

Subsumed by Polymath8b's $H_m \le C m \exp(2m)$. Same envelope argument
as the unconditional asymptotic: $m \le m^3$ for $m \ge 1$. -/
theorem Hm_asymptotic_under_EH
    (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤
        ENNReal.ofReal (C * (m : ℝ)^3 * Real.exp (2 * m)) := by
  obtain ⟨C, hC, hPoly⟩ := Polymath8b.Hm_asymptotic_under_EH hEH
  refine ⟨C, hC, fun m hm => ?_⟩
  refine le_trans (hPoly m hm) ?_
  apply ENNReal.ofReal_le_ofReal
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hm3 : (m : ℝ) ≤ m^3 := by
    have h := pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 3)
    simpa using h
  have : C * (m : ℝ) * Real.exp (2 * m) ≤
      C * (m : ℝ)^3 * Real.exp (2 * m) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left hm3 hC.le
  exact this

end BoundedGaps.Maynard
