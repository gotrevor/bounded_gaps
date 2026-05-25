/-
# Bound-tightening targets.

This file makes the path to a lower bound on $H_1$ explicit. Three theorems:

1. **`H1_le_of_Mk_witness`** — the bridge. Given an admissible $k$-tuple $H$
   and a proof that $M_k > 4$, deduce $H_1 \le \mathrm{diameter}(H)$.

2. **`H1_le_240_if_Mk_49_witness`** — instantiate the bridge with the
   Engelsma 49-tuple of diameter 240. Reduces "improve 246 → 240" to
   "prove $M_{49} > 4$".

3. **`H1_le_236_if_Mk_48_witness`** — same with the 48-tuple of diameter 236.
   "Improve 246 → 236" reduces to "prove $M_{48} > 4$".

The bridge itself is `sorry` because it composes the §5 criterion theorems
(also `sorry`, awaiting the analytic-NT prerequisites). But the *structure*
is now explicit: any future numerical proof of $M_{49} > 4$ or $M_{48} > 4$
plugs directly into a known bound.

Polymath8b §7 ("Additional remarks", item 2) explicitly identifies improved
basis functions for the variational problem as the natural next step — piecewise
polynomials with carefully chosen polytope supports. That work is what would
discharge the $M_k > 4$ hypothesis.
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Sieve
import BoundedGaps.Prerequisites
import BoundedGaps.Engelsma
import BoundedGaps.Maynard
import BoundedGaps.Polymath8b

namespace BoundedGaps.Targets

open BoundedGaps

/-! ## The bridge -/

/-- **Bridge theorem**: an admissible $k$-tuple $H$ and a verified $M_k > 4$
yields the bound $H_1 \le \mathrm{diameter}(H)$.

Proof obligation: compose `Sieve.epsilon_trick` (which gives `DHL k 2` from
$M_{k, \varepsilon} > 4$, in the BV regime) with `dhl_implies_liminfGap` for
$m = 1$. The `M_k` vs `M_{k, \varepsilon}` distinction is glossed over; the
real theorem would split on which Polymath8b criterion is being invoked. -/
theorem H1_le_of_Mk_witness (k : ℕ) (H : List ℕ)
    (_hAdm : Admissible H) (_hLen : H.length = k)
    (_hMk : Sieve.Mk k > 4) :
    liminfGap 1 ≤ (diameter H : ℕ∞) := sorry

/-! ## Current record: $H_1 \le 246$ (Polymath8b 2014) -/

/-- The current published bound, instantiated through the bridge.

Discharging this requires both:
- `Engelsma.tuple_50_admissible` (currently 1 sorry on the all-primes check)
- `Sieve.Mk 50 > 4` (the headline computation of Polymath8b §6 — extensive
  numerical work with polynomial sieve weights, Maple-computed). -/
theorem H1_le_246 (hMk : Sieve.Mk 50 > 4) :
    liminfGap 1 ≤ (246 : ℕ∞) := by
  have h := H1_le_of_Mk_witness 50 Engelsma.tuple_50
    Engelsma.tuple_50_admissible Engelsma.tuple_50_length hMk
  rw [Engelsma.tuple_50_diameter] at h
  exact h

/-! ## Open door 1: $H_1 \le 240$ — improvement by 6 -/

/-- **If** someone proves $M_{49} > 4$, then $H_1 \le 240$ — improving the
current bound by 6.

Status: $M_{49}$ is presumably computable to high accuracy; the question is
whether the rigorous lower bound can be pushed past 4. Polymath8b §7 item 2
suggests piecewise-polynomial sieve weights with carefully chosen polytope
supports are the natural next attempt. -/
theorem H1_le_240_if_Mk_49_witness (hMk : Sieve.Mk 49 > 4) :
    liminfGap 1 ≤ (240 : ℕ∞) := by
  have h := H1_le_of_Mk_witness 49 Engelsma.tuple_49
    Engelsma.tuple_49_admissible Engelsma.tuple_49_length hMk
  rw [Engelsma.tuple_49_diameter] at h
  exact h

/-! ## Open door 2: $H_1 \le 236$ — improvement by 10 -/

/-- **If** someone proves $M_{48} > 4$, then $H_1 \le 236$ — improving the
current bound by 10.

Same status as the $k = 49$ case but with more demand on the variational
lower bound (smaller $k$ makes $M_k$ smaller, so $M_k > 4$ is harder to
establish). -/
theorem H1_le_236_if_Mk_48_witness (hMk : Sieve.Mk 48 > 4) :
    liminfGap 1 ≤ (236 : ℕ∞) := by
  have h := H1_le_of_Mk_witness 48 Engelsma.tuple_48
    Engelsma.tuple_48_admissible Engelsma.tuple_48_length hMk
  rw [Engelsma.tuple_48_diameter] at h
  exact h

/-! ## Conditional bounds: tighter under EH / GEH

We already have these in `Maynard.lean` and `Polymath8b.lean`; restating
the headlines here for the "improvements menu". -/

/-- Under EH for all $\vartheta < 1$: $H_1 \le 12$ (Maynard). -/
example : (∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) →
    liminfGap 1 ≤ (12 : ℕ∞) :=
  Maynard.H1_le_12_under_EH

/-- Under GEH for all $\vartheta < 1$: $H_1 \le 6$ (Polymath8b, parity-tight). -/
example : (∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) →
    liminfGap 1 ≤ (6 : ℕ∞) :=
  Polymath8b.H1_le_6_under_GEH

end BoundedGaps.Targets
