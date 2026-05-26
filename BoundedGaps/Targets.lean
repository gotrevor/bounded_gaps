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

Proof: compose `Sieve.maynard_thm` (which gives `DHL k 2` from `Mk k > 2/ϑ`
with `EH[ϑ]`, picking $\vartheta < 1/2$ — automatic via Bombieri-Vinogradov)
with `dhl_two_implies_boundedGap` + `liminfGap_one_le_iff`. The 2× threshold
condition `Mk k > 4` is the boundary case: any `ϑ ∈ (2/Mk k, 1/2)` works,
e.g. `ϑ := 1/Mk k + 1/4`. -/
theorem H1_le_of_Mk_witness (k : ℕ) (H : List ℕ)
    (hAdm : Admissible H) (hLen : H.length = k)
    (hMk : Sieve.Mk k > 4) :
    liminfGap 1 ≤ (diameter H : ℕ∞) := by
  -- Step 1: derive k ≥ 2 (Mk k ≤ 1 for k ≤ 1 by Cauchy-Schwarz).
  have hkGe2 : 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    have hMkLe : Sieve.Mk k ≤ 1 := Sieve.Mk_le_one_of_k_le_one k (by omega)
    linarith
  -- Step 2: pick ϑ := 1/Mk + 1/4. Then 2/Mk < ϑ < 1/2.
  set MkV := Sieve.Mk k with hMkV
  have hMkPos : (0 : ℝ) < MkV := lt_trans (by norm_num) hMk
  set ϑ : ℝ := 1 / MkV + 1 / 4
  have hϑPos : 0 < ϑ := by positivity
  have hϑLtHalf : ϑ < 1 / 2 := by
    have h1Mk : 1 / MkV < 1 / 4 := by
      rw [one_div_lt_one_div hMkPos (by norm_num : (0:ℝ) < 4)]
      linarith
    show 1 / MkV + 1 / 4 < 1 / 2
    linarith
  have hϑBV : 0 < ϑ ∧ ϑ < 1 / 2 := ⟨hϑPos, hϑLtHalf⟩
  have hEH : Prerequisites.EH ϑ := Prerequisites.BombieriVinogradov hϑBV
  have hϑLtOne : 0 < ϑ ∧ ϑ < 1 :=
    ⟨hϑPos, hϑLtHalf.trans (by norm_num)⟩
  -- Step 3: MkV > 2 * 1 / ϑ. Algebra: MkV * ϑ = MkV * (1/MkV + 1/4) = 1 + MkV/4 > 2.
  have hMkGt : MkV > 2 * (1 : ℕ) / ϑ := by
    have hKey : 2 < MkV * ϑ := by
      have hExpand : MkV * ϑ = 1 + MkV / 4 := by
        show MkV * (1 / MkV + 1 / 4) = 1 + MkV / 4
        field_simp
      linarith
    have : (2 : ℝ) * (1 : ℕ) / ϑ < MkV := by
      rw [show (2 * (1 : ℕ) : ℝ) / ϑ = 2 / ϑ from by push_cast; ring]
      rw [div_lt_iff₀ hϑPos]
      linarith
    exact this
  -- Step 4: apply maynard_thm to get DHL[k, 2].
  have hDHL : DHL k 2 := by
    have h := Sieve.maynard_thm k 1 hkGe2 (by norm_num : 1 ≤ 1) ϑ hϑLtOne hEH hMkGt
    convert h using 1
  -- Step 5: DHL[k, 2] + admissibility → BoundedGap (diameter H).
  have hBG : BoundedGap (diameter H) :=
    dhl_two_implies_boundedGap k hDHL H hAdm hLen
  -- Step 6: BoundedGap → liminfGap 1 ≤ diameter H.
  exact (liminfGap_one_le_iff (diameter H)).mpr hBG

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
supports are the natural next attempt.

**The wall, honestly** (note added 2026-05-25): Polymath8b explicitly tried
symmetric polynomials in their sieve weight basis up to degree 23 and could
not push $M_{49}$ past 4 (they barely cleared 4 for $M_{50}$). 11 years of
nobody finding a witness $F$ with $M_{49}(F) > 4$ is signal. Anyone retrying
would need a richer function-space basis — higher-degree polynomials,
non-symmetric weights, or non-polynomial weights entirely — plus an SDP
solver to handle the resulting variational problem. Time-scope estimate:
multi-month numerical project even with modern tools, not a one-afternoon
hit. (~70% confidence.) The Lean side is ready; the math is the bottleneck. -/
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
