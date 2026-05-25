/-
# Polymath8b — Variants of the Selberg sieve, bounded intervals containing many primes.

Tao, Maynard, et al. (2014). The 246 paper.

Captures: the main theorem (all 13 numerical bounds), the DHL reformulation
(Theorem main-dhl), the H(k) bounds (Theorem hk-bound), the parity-barrier
optimality of $H_1 \le 6$, and the twin-primes-or-Goldbach disjunction.

Local copy: [../papers/pdf/polymath8b-2014-variants.pdf](../papers/pdf/polymath8b-2014-variants.pdf)
LaTeX source: [../papers/src/polymath8b-1407.4897/newergap-submitted.tex](../papers/src/polymath8b-1407.4897/newergap-submitted.tex)

Statements lifted from §1 (Theorem main, Theorem disj), §3 (Theorem main-dhl,
Theorem hk-bound), §7 (parity).
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Prerequisites
import BoundedGaps.Sieve
import BoundedGaps.Maynard
import BoundedGaps.Engelsma

namespace BoundedGaps.Polymath8b

open BoundedGaps

/-! ## §1 — Main Theorem (Theorem 1.3 in the paper, labeled `main`)

All bounds are stated as `liminfGap m ≤ (constant : ℕ∞)`. -/

/-! ### Unconditional bounds (Theorem main, (i)-(vi)) -/

/-- **(i)** $H_1 \le 246$. Uses Bombieri-Vinogradov only. -/
theorem H1_le_246 : liminfGap 1 ≤ (246 : ℕ∞) := sorry

/-- **(ii)** $H_2 \le 398{,}130$. Uses Polymath8a MPZ result. -/
theorem H2_le_398130 : liminfGap 2 ≤ (398130 : ℕ∞) := sorry

/-- **(iii)** $H_3 \le 24{,}797{,}814$. Uses Polymath8a MPZ result. -/
theorem H3_le_24797814 : liminfGap 3 ≤ (24797814 : ℕ∞) := sorry

/-- **(iv)** $H_4 \le 1{,}431{,}556{,}072$. Uses Polymath8a MPZ result. -/
theorem H4_le_1431556072 : liminfGap 4 ≤ (1431556072 : ℕ∞) := sorry

/-- **(v)** $H_5 \le 80{,}550{,}202{,}480$. Uses Polymath8a MPZ result. -/
theorem H5_le_80550202480 : liminfGap 5 ≤ (80550202480 : ℕ∞) := sorry

/-- **(vi)** Asymptotic: $H_m \le C m \exp((4 - 28/157) m)$ for an effective $C$. -/
theorem Hm_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp ((4 - 28/157) * m)) := sorry

/-! ### Under EH[ϑ] for all $0 < \vartheta < 1$ (Theorem main, (vii)-(xi)) -/

/-- **(vii)** Under EH: $H_2 \le 270$. -/
theorem H2_le_270_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 2 ≤ (270 : ℕ∞) := sorry

/-- **(viii)** Under EH: $H_3 \le 52{,}116$. -/
theorem H3_le_52116_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 3 ≤ (52116 : ℕ∞) := sorry

/-- **(ix)** Under EH: $H_4 \le 474{,}266$. -/
theorem H4_le_474266_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 4 ≤ (474266 : ℕ∞) := sorry

/-- **(x)** Under EH: $H_5 \le 4{,}137{,}854$. -/
theorem H5_le_4137854_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 5 ≤ (4137854 : ℕ∞) := sorry

/-- **(xi)** Under EH, asymptotic: $H_m \le C m \exp(2m)$ for an effective $C$. -/
theorem Hm_asymptotic_under_EH
    (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp (2 * m)) := sorry

/-! ### Under GEH[ϑ] for all $0 < \vartheta < 1$ (Theorem main, (xii)-(xiii))

These are the **parity-barrier optimal** results. The bound $H_1 \le 6$ is the
best possible from sieve-theoretic methods alone (Theorem parity_barrier below). -/

/-- **(xii)** Under GEH: $H_1 \le 6$.

This is the parity-barrier-tight bound. See [parity_barrier] for the matching
lower bound on what sieves can achieve. -/
theorem H1_le_6_under_GEH (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    liminfGap 1 ≤ (6 : ℕ∞) := sorry

/-- **(xiii)** Under GEH: $H_2 \le 252$. -/
theorem H2_le_252_under_GEH (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    liminfGap 2 ≤ (252 : ℕ∞) := sorry

/-! ## §3 — The DHL reformulation (Theorem main-dhl)

The numerical bounds in Theorem main all factor through DHL[k, j] claims. -/

/-- **DHL[50, 2]** unconditional → $H_1 \le H(50) = 246$. -/
theorem dhl_50_2 : DHL 50 2 := sorry

/-- **DHL[35410, 3]** unconditional. -/
theorem dhl_35410_3 : DHL 35410 3 := sorry

/-- **DHL[1649821, 4]** unconditional. -/
theorem dhl_1649821_4 : DHL 1649821 4 := sorry

/-- **DHL[75845707, 5]** unconditional. -/
theorem dhl_75845707_5 : DHL 75845707 5 := sorry

/-- **DHL[3473955908, 6]** unconditional. -/
theorem dhl_3473955908_6 : DHL 3473955908 6 := sorry

/-- **DHL[k, m+1]** unconditional asymptotic: holds whenever
$k \ge C \exp((4 - 28/157) m)$. -/
theorem dhl_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ, m ≥ 1 →
      (k : ℝ) ≥ C * Real.exp ((4 - 28/157) * m) → DHL k (m + 1) := sorry

/-- Under EH: **DHL[54, 3]**. -/
theorem dhl_54_3_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 54 3 := sorry

/-- Under EH: **DHL[5511, 4]**. -/
theorem dhl_5511_4_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 5511 4 := sorry

/-- Under EH: **DHL[41588, 5]**. -/
theorem dhl_41588_5_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 41588 5 := sorry

/-- Under EH: **DHL[309661, 6]**. -/
theorem dhl_309661_6_under_EH (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 309661 6 := sorry

/-- Under GEH: **DHL[3, 2]**. The flagship parity-tight result. -/
theorem dhl_3_2_under_GEH (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    DHL 3 2 := sorry

/-- Under GEH: **DHL[51, 3]**. -/
theorem dhl_51_3_under_GEH (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    DHL 51 3 := sorry

/-! ## §3 — Narrowness bounds (Theorem hk-bound) -/

/-- $H(2) = 2$ (the tuple $(0, 2)$ realizes it). Fully proven:
the upper bound is `Basic.narrowness_2_le_two` (the tuple $(0, 2)$ witnesses);
the lower bound is `Basic.narrowness_2_ge_two` (mod-2 parity forces any
admissible 2-tuple's diameter to be even and positive, hence $\ge 2$). -/
theorem narrowness_2 : narrowness 2 = 2 :=
  le_antisymm narrowness_2_le_two narrowness_2_ge_two

/-- $H(3) = 6$ (the tuple $(0, 2, 6)$ realizes it). Fully proven:
the upper bound is `Basic.narrowness_3_le_six` (the tuple $(0,2,6)$ witnesses);
the lower bound is `Basic.narrowness_3_ge_six` (no admissible 3-tuple of
diameter $< 6$, by simultaneous case analysis on residues mod 2 and mod 3). -/
theorem narrowness_3 : narrowness 3 = 6 :=
  le_antisymm narrowness_3_le_six narrowness_3_ge_six

/-- **$H(50) = 246$**: an admissible 50-tuple of diameter 246 exists, and no
narrower one. The 246 bound. The $\le 246$ direction is now proven via
`Engelsma.narrowness_50_le_246` (the Engelsma 50-tuple witnesses it); the
$\ge 246$ direction (no admissible 50-tuple has smaller diameter) is exact
by Clark-Jarvis 2001 for $k \le 342$ but requires exhaustive enumeration. -/
theorem narrowness_50 : narrowness 50 = 246 := by
  apply le_antisymm
  · exact Engelsma.narrowness_50_le_246
  · sorry  -- ≥ 246: Clark-Jarvis exhaustive enumeration, out of current scope

/-- $H(51) = 252$. -/
theorem narrowness_51 : narrowness 51 = 252 := sorry

/-- $H(54) = 270$. -/
theorem narrowness_54 : narrowness 54 = 270 := sorry

/-- $H(5511) \le 52116$. -/
theorem narrowness_5511_le : narrowness 5511 ≤ 52116 := sorry

/-- $H(35410) \le 398130$. -/
theorem narrowness_35410_le : narrowness 35410 ≤ 398130 := sorry

/-- $H(41588) \le 474266$. -/
theorem narrowness_41588_le : narrowness 41588 ≤ 474266 := sorry

/-- $H(309661) \le 4137854$. -/
theorem narrowness_309661_le : narrowness 309661 ≤ 4137854 := sorry

/-- $H(1649821) \le 24797814$. -/
theorem narrowness_1649821_le : narrowness 1649821 ≤ 24797814 := sorry

/-- $H(75845707) \le 1431556072$. -/
theorem narrowness_75845707_le : narrowness 75845707 ≤ 1431556072 := sorry

/-- $H(3473955908) \le 80550202480$. -/
theorem narrowness_3473955908_le : narrowness 3473955908 ≤ 80550202480 := sorry

/-- Asymptotic upper bound: $H(k) \le k \log k + k \log \log k - k + o(k)$. -/
theorem narrowness_asymptotic_upper :
    (fun k : ℕ => (narrowness k : ℝ))
      =O[Filter.atTop]
      (fun k : ℕ => (k : ℝ) * Real.log k) := sorry

/-- Brun-Titchmarsh lower bound: $H(k) \ge (\tfrac12 + o(1)) k \log k$. -/
theorem narrowness_asymptotic_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in Filter.atTop,
      (narrowness k : ℝ) ≥ (1/2 - ε) * k * Real.log k := sorry

/-! ## §7 — The parity barrier -/

/-- **The parity barrier** (Polymath8b §7, after Selberg): no purely
sieve-theoretic argument can establish $H_1 \le 4$, even under the
generalized Elliott-Halberstam conjecture.

Statement is informal — "sieve-theoretic" isn't a formal predicate. Captured
here as a propositional placeholder for the paper's heuristic theorem. -/
axiom SieveTheoreticArgument (proves : Prop) : Prop

theorem parity_barrier :
    ¬ SieveTheoreticArgument (liminfGap 1 ≤ (4 : ℕ∞)) := sorry

/-! ## §8 — The twin-primes-or-Goldbach disjunction (Theorem disj) -/

/-- **Twin Primes Conjecture**: there are infinitely many primes $p$ with
$p + 2$ also prime. Equivalently, $H_1 = 2$. -/
def TwinPrimesConjecture : Prop :=
  Set.Infinite { p : ℕ | p.Prime ∧ (p + 2).Prime }

/-- **Near-miss Goldbach** (Polymath8b Theorem 1.4(b)): for every sufficiently
large multiple of 6, *both* of the following hold — at least one of $n, n-2$
is a sum of two primes, and at least one of $n, n+2$ is also.

(I.e., every sufficiently large even number lies within 2 of a sum of two
primes.) -/
def NearMissGoldbach : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, 6 ∣ n →
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨
     (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 2 = p + q)) ∧
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨
     (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n + 2 = p + q))

/-- **Polymath8b Theorem 1.4 (disjunction)**: under GEH, at least one of
the twin primes conjecture or the near-miss Goldbach statement holds. -/
theorem twin_primes_or_near_miss_Goldbach
    (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    TwinPrimesConjecture ∨ NearMissGoldbach := sorry

end BoundedGaps.Polymath8b
