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

/-- $H_1 = 2$ is the twin-prime statement in liminf notation.

Proof: decompose into the unconditional `liminfGap 1 ≥ 2` (gaps between
consecutive primes are eventually even and positive, hence ≥ 2) and the
conjectural `liminfGap 1 ≤ 2`. The latter is equivalent to `BoundedGap 2`
via `Basic.liminfGap_one_le_iff`, which in turn is equivalent to
TwinPrimesConjecture modulo the (2, 3) edge case (the only consecutive
primes with odd difference). -/
theorem twinPrimes_iff_liminfGap_one : TwinPrimesConjecture ↔ liminfGap 1 = 2 := by
  -- Unfold the local alias.
  change Polymath8b.TwinPrimesConjecture ↔ liminfGap 1 = 2
  rw [show Polymath8b.TwinPrimesConjecture =
        Set.Infinite { p : ℕ | p.Prime ∧ (p + 2).Prime } from rfl]
  -- We'll show: TP-set Infinite ↔ liminfGap 1 ≤ 2 (and combine with ≥ 2 for =).
  constructor
  · -- Forward: TwinPrimes → liminfGap 1 = 2
    intro hTP
    -- TwinPrimes implies BoundedGap 2
    have hBG : BoundedGap 2 := by
      unfold BoundedGap
      apply hTP.mono
      intro p hp
      exact ⟨hp.1, p + 2, hp.2, by omega, by omega⟩
    have hLe : liminfGap 1 ≤ ((2 : ℕ) : ℕ∞) := (liminfGap_one_le_iff 2).mpr hBG
    have hGe : ((2 : ℕ) : ℕ∞) ≤ liminfGap 1 := by exact_mod_cast liminfGap_one_ge_two
    have : liminfGap 1 = ((2 : ℕ) : ℕ∞) := le_antisymm hLe hGe
    simpa using this
  · -- Backward: liminfGap 1 = 2 → TwinPrimes
    intro hEq
    have hLe : liminfGap 1 ≤ ((2 : ℕ) : ℕ∞) := by
      rw [hEq]; norm_cast
    have hBG : BoundedGap 2 := (liminfGap_one_le_iff 2).mp hLe
    -- BoundedGap 2: ∃∞ primes p with q prime, p < q, q - p ≤ 2.
    -- For p ≠ 2, the witness q must satisfy q = p + 2 (since q = p + 1 with q
    -- prime forces p = 2, contradiction). So BoundedGap 2 minus {2} ⊆ TwinPrimes.
    unfold BoundedGap at hBG
    apply (hBG.diff (Set.finite_singleton 2)).mono
    intro p hp
    simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    obtain ⟨⟨hpPrime, q, hqPrime, hpLtQ, hqLeP2⟩, hpNe2⟩ := hp
    refine ⟨hpPrime, ?_⟩
    -- p prime, p ≠ 2 ⟹ p odd. q ∈ {p+1, p+2}; q = p+1 contradicts q prime (q even ≥ 4).
    have hpOdd : Odd p := hpPrime.odd_of_ne_two hpNe2
    have hpGe3 : 3 ≤ p := by
      rcases hpPrime.two_le.lt_or_eq with hLt | hEq2
      · exact hLt
      · exact absurd hEq2.symm hpNe2
    have hCases : q = p + 1 ∨ q = p + 2 := by omega
    rcases hCases with heq | heq
    · -- q = p + 1: q is even ≥ 4, contradicts q prime.
      exfalso
      have hqEven : Even q := by
        rw [heq]
        exact hpOdd.add_one
      have hqEq2 : q = 2 := hqPrime.even_iff.mp hqEven
      omega
    · rw [← heq]; exact hqPrime

/-- The polymath8b-to-twin-primes gap, made explicit: we have $H_1 \le 246$,
we want $H_1 = 2$. Stated as a placeholder claim about the difference. -/
theorem polymath_to_twinPrimes_gap :
    liminfGap 1 ≤ (246 : ℕ∞) ∧ ¬ TwinPrimesConjecture → True := by
  intro _; trivial

end BoundedGaps.TwinPrimes
