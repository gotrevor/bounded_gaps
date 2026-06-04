import BoundedGaps.WeightedRiemann3D

/-!
# Generic `k`-D coupled log-weighted Riemann limit (recursive framework).

The 1-D (`WeightedMertens.riemann_sum_log_weight`), 2-D (`WeightedRiemann2D.weighted_riemann_2d`),
and 3-D (`WeightedRiemann3D.weighted_riemann_3d`) simplex limits are special cases of ONE generic
statement over a *list* of test functions. This file sets up the recursive scaffold — definitions,
their specialisations to the proven low-dimensional cases, and the base case — so the inductive
proof (reducing level `k` to level `k-1` via the SAME `perturbed_riemann` + Pólya + rescaling
pattern that `WeightedRiemann3D` works out concretely) can be built on top.

- `nestedLogSum R Gs Q` — the nested truncated log-weighted sum for the function list `Gs`, with
  outer scale `R` and current truncation budget `Q` (starts at `R`, divided by each index):
  `nestedLogSum R (g::gs) Q = ∑_{n≤Q} g(log n/log R)/n · nestedLogSum R gs (Q/n)`. For
  `Gs = [g₁,…,g_k]`, `nestedLogSum R Gs R = ∑_{n₁≤R}∑_{n₂≤R/n₁}⋯ ∏ gᵢ(log nᵢ/log R)/nᵢ`, the
  `∏ nᵢ ≤ R` (simplex) coupled sum.
- `nestedPhi Gs s` — the recursive simplex cross-section integral, the limit's value:
  `nestedPhi (g::gs) s = ∫₀^{1-s} g(y)·nestedPhi gs (s+y) dy`, `nestedPhi [] s = 1`. It generalises
  `Phi` (`nestedPhi [g] = Phi g`) and `Phi2` (`nestedPhi [g,h] = Phi2 g h`).

The generic theorem (to prove by induction, next):
  `Gs = g₀ :: rest`, `g₀` continuous, `rest` continuous and `≥ 0` ⟹
  `nestedLogSum R Gs R / (log R)^(Gs.length) → nestedPhi Gs 0 = ∫_{simplex} ∏ Gs`.
The base case `Gs = []` is `1 → 1`; the step reuses the 3-D blueprint one list-cons up.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace BoundedGaps.WeightedRiemannKD

open BoundedGaps.WeightedRiemann2D (Phi)
open BoundedGaps.WeightedRiemann3D (Phi2)

/-- The nested truncated log-weighted sum for a list of functions. `R` is the (fixed) outer scale;
`Q` is the current truncation budget (the running `R / (product of outer indices)`). -/
noncomputable def nestedLogSum (R : ℕ) : List (ℝ → ℝ) → ℕ → ℝ
  | [], _ => 1
  | g :: gs, Q =>
      ∑ n ∈ Finset.Icc 2 Q, g (Real.log n / Real.log R) / (n : ℝ) * nestedLogSum R gs (Q / n)

/-- The recursive simplex cross-section integral (the limit value). `nestedPhi (g::gs) s` integrates
`g` against the `(k-1)`-D cross-section of the remaining list, over the slab `[0, 1-s]`. -/
noncomputable def nestedPhi : List (ℝ → ℝ) → ℝ → ℝ
  | [], _ => 1
  | g :: gs, s => ∫ y in (0 : ℝ)..(1 - s), g y * nestedPhi gs (s + y)

@[simp] lemma nestedLogSum_nil (R Q : ℕ) : nestedLogSum R [] Q = 1 := rfl

@[simp] lemma nestedLogSum_cons (R : ℕ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (Q : ℕ) :
    nestedLogSum R (g :: gs) Q
      = ∑ n ∈ Finset.Icc 2 Q, g (Real.log n / Real.log R) / (n : ℝ) * nestedLogSum R gs (Q / n) :=
  rfl

@[simp] lemma nestedPhi_nil (s : ℝ) : nestedPhi [] s = 1 := rfl

@[simp] lemma nestedPhi_cons (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (s : ℝ) :
    nestedPhi (g :: gs) s = ∫ y in (0 : ℝ)..(1 - s), g y * nestedPhi gs (s + y) := rfl

/-- `nestedPhi [g]` is the 1-D cross-section `Phi g`. -/
lemma nestedPhi_singleton (g : ℝ → ℝ) : nestedPhi [g] = Phi g := by
  funext s
  simp only [nestedPhi_cons, nestedPhi_nil, mul_one, Phi]

/-- `nestedPhi [g, h]` is the 2-D cross-section `Phi2 g h`. -/
lemma nestedPhi_pair (g h : ℝ → ℝ) : nestedPhi [g, h] = Phi2 g h := by
  funext s
  rw [nestedPhi_cons, nestedPhi_singleton]
  rfl

/-- **Base case of the generic limit.** For the empty list, `nestedLogSum R [] R / (log R)^0 = 1`
converges to `nestedPhi [] 0 = 1`. -/
theorem weighted_riemann_kd_nil :
    Tendsto (fun R : ℕ => nestedLogSum R [] R / (Real.log R) ^ (([] : List (ℝ → ℝ)).length))
      atTop (nhds (nestedPhi [] 0)) := by
  simp only [nestedLogSum_nil, List.length_nil, pow_zero, div_one, nestedPhi_nil]
  exact tendsto_const_nhds

/-- The 1-D nested log-sum is the standard single log-weighted sum (`nestedLogSum R [g] R` with the
trailing `nestedLogSum R [] (R/n) = 1` factored out). -/
lemma nestedLogSum_singleton (R : ℕ) (g : ℝ → ℝ) :
    nestedLogSum R [g] R = ∑ n ∈ Finset.Icc 2 R, g (Real.log n / Real.log R) / (n : ℝ) := by
  simp only [nestedLogSum_cons, nestedLogSum_nil, mul_one]

/-- The 2-D nested log-sum unfolds to the coupled double sum over `n₁·n₂ ≤ R` (matching the form of
`weighted_riemann_2d`: inner truncation `R/n₁`, summand `g₁·g₂/(n₁ n₂)`). -/
lemma nestedLogSum_pair (R : ℕ) (g h : ℝ → ℝ) :
    nestedLogSum R [g, h] R
      = ∑ n₁ ∈ Finset.Icc 2 R, ∑ n₂ ∈ Finset.Icc 2 (R / n₁),
          g (Real.log n₁ / Real.log R) * h (Real.log n₂ / Real.log R)
            / ((n₁ : ℝ) * (n₂ : ℝ)) := by
  simp only [nestedLogSum_cons, nestedLogSum_nil, mul_one]
  refine Finset.sum_congr rfl (fun n₁ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n₂ _ => ?_)
  ring

end BoundedGaps.WeightedRiemannKD
