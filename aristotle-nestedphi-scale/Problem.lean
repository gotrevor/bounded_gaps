import Mathlib

/-!
# Change-of-variables for the iterated simplex cross-section integral

`nestedPhi gs s` is the iterated "simplex cross-section" integral attached to a list of test
functions `gs = [g₁,…,g_k]`:
  `nestedPhi [] s = 1`,  `nestedPhi (g::gs) s = ∫_{y in 0..(1-s)} g(y) · nestedPhi gs (s+y)`.
So `nestedPhi gs 0 = ∫_{y₁+…+y_k ≤ 1, yᵢ≥0} ∏ gᵢ(yᵢ)` and `nestedPhi gs (1-t)` is the same integral
over the scaled simplex `{∑ yᵢ ≤ t}`.

GOAL (`nestedPhi_scale`): the linear change of variables `yᵢ = t·zᵢ` on the simplex `{∑yᵢ ≤ t}`
gives the Jacobian `t^k` and rescales each function:
  `nestedPhi gs (1 - t) = t ^ (gs.length) · nestedPhi (gs.map (fun g => fun u => g (t*u))) 0`,  t ≠ 0.

ROUTE (already laid out below; fill the three `sorry`s):
1. `simplexPhi gs a` = same iterated integral but with explicit outer budget `a` (bounds `a`, `a-y`,
   `a-y-y'`, …). `nestedPhi_eq_simplexPhi`: `nestedPhi gs (1-a) = simplexPhi gs a` (induction on `gs`;
   the cons step is `intervalIntegral.integral_congr` reducing to the IH at budget `a-y`).
2. `simplexPhi_scale`: `simplexPhi gs (t*a) = t^(gs.length) · simplexPhi (gs.map (t-scale)) a`
   (induction on `gs`; the cons step substitutes `y = t·z` via
   `intervalIntegral.mul_integral_comp_mul_left` — note `c * ∫ x in a..b, f (c*x) = ∫ x in c*a..c*b, f x`
   — then applies the IH at budget `a-z`).
3. `nestedPhi_scale` chains: `nestedPhi gs (1-t) = simplexPhi gs t = simplexPhi gs (t*1)
   = t^|gs| · simplexPhi gsT 1 = t^|gs| · nestedPhi gsT (1-1) = t^|gs| · nestedPhi gsT 0`.

If a step resists, KEEP the proved reductions and leave only the genuinely stuck step as an isolated
`sorry` so the file still builds.
-/

open MeasureTheory intervalIntegral

namespace AristotleScale

/-- iterated simplex cross-section integral, offset form. -/
noncomputable def nestedPhi : List (ℝ → ℝ) → ℝ → ℝ
  | [], _ => 1
  | g :: gs, s => ∫ y in (0 : ℝ)..(1 - s), g y * nestedPhi gs (s + y)

/-- iterated simplex integral, explicit-budget form (outer bound `a`, inner `a-y`, …). -/
noncomputable def simplexPhi : List (ℝ → ℝ) → ℝ → ℝ
  | [], _ => 1
  | g :: gs, a => ∫ y in (0 : ℝ)..a, g y * simplexPhi gs (a - y)

@[simp] lemma nestedPhi_nil (s : ℝ) : nestedPhi [] s = 1 := rfl
@[simp] lemma simplexPhi_nil (a : ℝ) : simplexPhi [] a = 1 := rfl

lemma nestedPhi_eq_simplexPhi : ∀ (gs : List (ℝ → ℝ)) (a : ℝ),
    nestedPhi gs (1 - a) = simplexPhi gs a := by
  sorry

lemma simplexPhi_scale : ∀ (gs : List (ℝ → ℝ)) (t a : ℝ), t ≠ 0 →
    simplexPhi gs (t * a)
      = t ^ gs.length * simplexPhi (gs.map (fun g => fun u => g (t * u))) a := by
  sorry

/-- **Change of variables for `nestedPhi`** (the goal). -/
theorem nestedPhi_scale (gs : List (ℝ → ℝ)) (t : ℝ) (ht : t ≠ 0) :
    nestedPhi gs (1 - t)
      = t ^ gs.length * nestedPhi (gs.map (fun g => fun u => g (t * u))) 0 := by
  sorry

end AristotleScale
