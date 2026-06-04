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

/-- **`nestedPhi Gs` is continuous** when every function in `Gs` is continuous — the generic
`phi2_continuous`, by induction on the list. Base: `nestedPhi [] = const 1`. Step: the integrand
`(s,y) ↦ g(y)·nestedPhi gs (s+y)` is jointly continuous (IH), so the parametric primitive composed
with `s ↦ (s, 1-s)` is continuous. -/
lemma nestedPhi_continuous : ∀ (Gs : List (ℝ → ℝ)), (∀ g ∈ Gs, Continuous g) →
    Continuous (nestedPhi Gs)
  | [], _ => continuous_const
  | g :: gs, h => by
      have hg : Continuous g := h g (List.mem_cons.mpr (Or.inl rfl))
      have hgs : Continuous (nestedPhi gs) :=
        nestedPhi_continuous gs (fun f hf => h f (List.mem_cons.mpr (Or.inr hf)))
      have huncurry : Continuous (Function.uncurry (fun s y => g y * nestedPhi gs (s + y))) :=
        (hg.comp continuous_snd).mul (hgs.comp (continuous_fst.add continuous_snd))
      have hpar := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0 : ℝ)) huncurry
      exact hpar.comp (continuous_id.prodMk (continuous_const.sub continuous_id))

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

open BoundedGaps.WeightedRiemann2D (perturbed_riemann)

/-- **Generic factor step** (the `three_d_factor` analog, any list length). The level-`k+1` nested
sum, normalized by `(log R)^(k+1)`, factors over the OUTER index `n` into the `perturbed_riemann`
shape with inner term `a R n := nestedLogSum R gs (R/n) / (log R)^k`. Pure field algebra. -/
lemma nestedLogSum_factor (R : ℕ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) :
    nestedLogSum R (g :: gs) R / (Real.log R) ^ (gs.length + 1)
      = (∑ n ∈ Finset.Icc 2 R, g (Real.log n / Real.log R)
          * (nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length) / (n : ℝ)) / Real.log R := by
  rw [nestedLogSum_cons]
  have key : ∀ n ∈ Finset.Icc 2 R,
      g (Real.log n / Real.log R)
          * (nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length) / (n : ℝ)
      = (g (Real.log n / Real.log R) * nestedLogSum R gs (R / n) / (n : ℝ))
          / (Real.log R) ^ gs.length := by
    intro n _; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, div_div, ← pow_succ]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => by ring)

/-- **Generic inductive-step reduction** (the `weighted_riemann_3d_of_inner` analog, any list).
GIVEN the inner-uniform convergence of the `(k-1)`-D tail
`nestedLogSum R gs (R/n)/(log R)^k → nestedPhi gs` (uniformly in `n ∈ [2,R]`) and continuity of the
tail limit `nestedPhi gs`, the level-`k` simplex
limit holds: `nestedLogSum R (g::gs) R / (log R)^|g::gs| → nestedPhi (g::gs) 0`. Combines
`nestedLogSum_factor` with the SAME reusable `perturbed_riemann` (outer `F := g`, `Φ := nestedPhi
gs`). This is the engine; the remaining inductive obligations (the inner-uniform — via Pólya + the
`t`-rescaling pointwise step reducing to level `k-1` — and `nestedPhi gs` continuity) mirror the 3-D
`inner_uniform_3d_of_pointwise_nonneg` / `psi3_pointwise` / `phi2_continuous` one list-cons up. -/
theorem weighted_riemann_cons_of_inner (g : ℝ → ℝ) (gs : List (ℝ → ℝ))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hΦcont : ContinuousOn (nestedPhi gs) (Set.Icc (0 : ℝ) 1))
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ n ∈ Finset.Icc 2 R,
        |nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length
          - nestedPhi gs (Real.log n / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ => nestedLogSum R (g :: gs) R / (Real.log R) ^ (g :: gs).length)
      atTop (nhds (nestedPhi (g :: gs) 0)) := by
  have hlim : nestedPhi (g :: gs) 0 = ∫ x in (0 : ℝ)..1, g x * nestedPhi gs x := by
    rw [nestedPhi_cons]; simp only [sub_zero, zero_add]
  rw [hlim, List.length_cons, funext (fun R => nestedLogSum_factor R g gs)]
  exact perturbed_riemann g (nestedPhi gs)
    (fun R n => nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length) hg hΦcont huni

end BoundedGaps.WeightedRiemannKD
