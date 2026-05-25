/-
# Twin Primes Conjecture — the asymptote.

Open since antiquity. The conjecture every result in this project is reaching
for: $H_1 = 2$.

Brun's theorem (1919) shows $\sum_{p, p+2 \text{ both prime}} 1/p$ converges,
so twin primes are sparse even if infinite. (Brun's constant $\approx 1.9021605$.)
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Polymath8b

namespace BoundedGaps.TwinPrimes

open BoundedGaps

/-- The twin primes conjecture, restated locally so we can prove things about
it without pulling in all of `Polymath8b`. Equivalent to
`Polymath8b.TwinPrimesConjecture`. -/
def TwinPrimesConjecture : Prop := Polymath8b.TwinPrimesConjecture

/-- $H_1 = 2$ is the twin-prime statement in liminf notation. -/
-- TRIAGE: PROVABLE (~1-3h) — real Filter.liminf + Nat.nth Nat.Prime work.
-- Two directions: (a) twin primes i.o. → liminfGap 1 ≤ 2 (bridge between
-- Set.Infinite predicate and the prime-index gap function); (b) liminfGap 1 ≥ 2
-- (gaps between consecutive primes ≥ 3 are even, push through atTop filter).
-- Probed 2026-05-25, deemed hard-world; bundle with Basic.liminfGap_one_le_iff.
theorem twinPrimes_iff_liminfGap_one : TwinPrimesConjecture ↔ liminfGap 1 = 2 := sorry

/-- The polymath8b-to-twin-primes gap, made explicit: we have $H_1 \le 246$,
we want $H_1 = 2$. Stated as a placeholder claim about the difference. -/
theorem polymath_to_twinPrimes_gap :
    liminfGap 1 ≤ (246 : ℕ∞) ∧ ¬ TwinPrimesConjecture → True := by
  intro _; trivial

end BoundedGaps.TwinPrimes
