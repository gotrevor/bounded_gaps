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

namespace BoundedGaps.Maynard

open BoundedGaps

/-! ### Unconditional (Polymath8b Theorem 1.2 (i)-(ii)) -/

/-- **(i)** $H_1 \le 600$. -/
theorem H1_le_600 : liminfGap 1 ≤ (600 : ℕ∞) := sorry

/-- **(ii)** $H_m \le C m^3 e^{4m}$ for all $m \ge 1$, effective $C$. -/
theorem Hm_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤
        ENNReal.ofReal (C * (m : ℝ)^3 * Real.exp (4 * m)) := sorry

/-! ### Under EH (Polymath8b Theorem 1.2 (iii)-(v)) -/

/-- **(iii)** Under EH: $H_1 \le 12$. -/
theorem H1_le_12_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 1 ≤ (12 : ℕ∞) := sorry

/-- **(iv)** Under EH: $H_2 \le 600$. -/
theorem H2_le_600_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 2 ≤ (600 : ℕ∞) := sorry

/-- **(v)** Under EH: $H_m \le C m^3 e^{2m}$ for all $m \ge 1$. -/
theorem Hm_asymptotic_under_EH
    (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤
        ENNReal.ofReal (C * (m : ℝ)^3 * Real.exp (2 * m)) := sorry

end BoundedGaps.Maynard
