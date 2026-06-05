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

/-- **`nestedLogSum` is nonnegative** for nonnegative function lists (induction on the list; each
summand is `(g/n)·(tail ≥ 0)`). A Pólya prerequisite. -/
lemma nestedLogSum_nonneg (R : ℕ) : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) →
    ∀ Q, 0 ≤ nestedLogSum R gs Q
  | [], _, _ => by rw [nestedLogSum_nil]; norm_num
  | g :: gs, h, Q => by
      rw [nestedLogSum_cons]
      refine Finset.sum_nonneg (fun n _ => ?_)
      have hg : ∀ x, 0 ≤ g x := h g (List.mem_cons.mpr (Or.inl rfl))
      have hgs : 0 ≤ nestedLogSum R gs (Q / n) :=
        nestedLogSum_nonneg R gs (fun f hf => h f (List.mem_cons.mpr (Or.inr hf))) (Q / n)
      exact mul_nonneg (div_nonneg (hg _) (by positivity)) hgs

/-- **`nestedLogSum R gs` is monotone in the budget `Q`** for nonnegative lists (induction on the
list; mirrors `psi3_monotoneOn`: as `Q` grows both the outer index set and each inner budget `Q/n`
grow, all summands `≥ 0`). The Pólya monotonicity for the generic inner-uniform. -/
lemma nestedLogSum_mono (R : ℕ) : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) →
    Monotone (nestedLogSum R gs)
  | [], _ => by rw [show nestedLogSum R [] = fun _ => (1 : ℝ) from rfl]; exact monotone_const
  | g :: gs, h => by
      intro Q Q' hQ
      have hg : ∀ x, 0 ≤ g x := h g (List.mem_cons.mpr (Or.inl rfl))
      have htail := fun f hf => h f (List.mem_cons.mpr (Or.inr hf))
      have hgs_nn : ∀ Q, 0 ≤ nestedLogSum R gs Q := nestedLogSum_nonneg R gs htail
      have hgs_mono : Monotone (nestedLogSum R gs) := nestedLogSum_mono R gs htail
      rw [nestedLogSum_cons, nestedLogSum_cons]
      calc ∑ n ∈ Finset.Icc 2 Q,
              g (Real.log n / Real.log R) / (n : ℝ) * nestedLogSum R gs (Q / n)
          ≤ ∑ n ∈ Finset.Icc 2 Q,
              g (Real.log n / Real.log R) / (n : ℝ) * nestedLogSum R gs (Q' / n) :=
            Finset.sum_le_sum (fun n _ =>
              mul_le_mul_of_nonneg_left (hgs_mono (Nat.div_le_div_right hQ))
                (div_nonneg (hg _) (by positivity)))
        _ ≤ ∑ n ∈ Finset.Icc 2 Q',
              g (Real.log n / Real.log R) / (n : ℝ) * nestedLogSum R gs (Q' / n) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ)
              (fun n _ _ => mul_nonneg (div_nonneg (hg _) (by positivity)) (hgs_nn _))

/-- The reparametrised level-`k` nested sum (outer truncation `⌊R^t⌋`), normalised by `(log R)^k`.
At `t = 1 - log n/log R` it relates the tail term to the budget `R/n` (the generic `Psi3`). -/
noncomputable def PsiK (R : ℕ) (gs : List (ℝ → ℝ)) (t : ℝ) : ℝ :=
  nestedLogSum R gs ⌊(R : ℝ) ^ t⌋₊ / (Real.log R) ^ gs.length

/-- **`PsiK R gs` is monotone in `t`** (for nonnegative `gs`): `⌊R^t⌋` grows with `t`, and
`nestedLogSum R gs` is monotone in its budget (`nestedLogSum_mono`). The generic `psi3_monotoneOn`,
the Pólya monotonicity for the generic inner-uniform. -/
lemma psiK_monotoneOn (R : ℕ) (gs : List (ℝ → ℝ)) (h : ∀ g ∈ gs, ∀ x, 0 ≤ g x) :
    MonotoneOn (PsiK R gs) (Set.Icc (0 : ℝ) 1) := by
  rcases Nat.lt_or_ge R 2 with hRlt | hR2
  · have hlog0 : Real.log (R : ℝ) = 0 := by interval_cases R <;> simp
    intro a _ b _ _
    rcases gs with _ | ⟨g, gs'⟩
    · simp [PsiK]
    · simp [PsiK, hlog0, List.length_cons, zero_pow]
  · have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    have hlogpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    intro a _ b _ hab
    have hpow : (R : ℝ) ^ a ≤ (R : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hR1' hab
    have hfloor : ⌊(R : ℝ) ^ a⌋₊ ≤ ⌊(R : ℝ) ^ b⌋₊ := Nat.floor_mono hpow
    exact div_le_div_of_nonneg_right (nestedLogSum_mono R gs h hfloor) (by positivity)

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

/-- **Reparametrisation:** at `t = 1 - log n/log R`, `PsiK` is the tail term of the factor lemma
(`nestedLogSum R gs (R/n)/(log R)^k`). Via `floor_rpow_one_sub` (`⌊R^t⌋ = R/n`). -/
lemma psiK_reparam (R : ℕ) (gs : List (ℝ → ℝ)) (n : ℕ) (hR2 : 2 ≤ R) (hn1 : 1 ≤ n) :
    PsiK R gs (1 - Real.log n / Real.log R)
      = nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length := by
  unfold PsiK
  rw [BoundedGaps.InnerUniformReduction.floor_rpow_one_sub R n hR2 hn1]

/-- **Generic inner-uniform from the pointwise scale-change** (the `inner_uniform_3d_of_pointwise`
analog). GIVEN the pointwise limit `PsiK R gs t → nestedPhi gs (1-t)` for every `t ∈ [0,1]`, the
term `nestedLogSum R gs (R/n)/(log R)^k` converges to `nestedPhi gs (log n/log R)` UNIFORMLY in
`n ∈ [2,R]` — exactly the `huni` of `weighted_riemann_cons_of_inner`. Pólya (`psiK_monotoneOn`
monotone + `nestedPhi_continuous` limit) + the `t = 1-log n/log R` reparametrisation. -/
theorem inner_uniform_kd_of_pointwise (gs : List (ℝ → ℝ))
    (hnn : ∀ g ∈ gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ gs, Continuous g)
    (hptw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => PsiK R gs t) atTop (nhds (nestedPhi gs (1 - t)))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ n ∈ Finset.Icc 2 R,
      |nestedLogSum R gs (R / n) / (Real.log R) ^ gs.length
        - nestedPhi gs (Real.log n / Real.log R)| ≤ ε := by
  have hΦcont : ContinuousOn (fun t => nestedPhi gs (1 - t)) (Set.Icc (0 : ℝ) 1) :=
    ((nestedPhi_continuous gs hcont).comp (continuous_const.sub continuous_id)).continuousOn
  have hpoly := BoundedGaps.PolyaUniform.polya_uniform
    (fun t => nestedPhi gs (1 - t)) (fun R => PsiK R gs) hΦcont
    (fun R => psiK_monotoneOn R gs hnn) hptw
  intro ε hε
  filter_upwards [hpoly ε hε, eventually_ge_atTop 2] with R hR hR2 n hn
  obtain ⟨hn2, hnR⟩ := Finset.mem_Icc.mp hn
  have hn1 : 1 ≤ n := by omega
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR2)
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogn_le : Real.log (n : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnR)
  have htn_mem : (1 - Real.log n / Real.log R) ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : Real.log n / Real.log R ≤ 1 := by rw [div_le_one hlogRpos]; exact hlogn_le
    have h0 : 0 ≤ Real.log n / Real.log R := div_nonneg hlogn_nonneg hlogRpos.le
    exact ⟨by linarith, by linarith⟩
  have hreparam := psiK_reparam R gs n hR2 hn1
  have hphi_eq : nestedPhi gs (1 - (1 - Real.log n / Real.log R))
      = nestedPhi gs (Real.log n / Real.log R) := by congr 1; ring
  have hb := hR (1 - Real.log n / Real.log R) htn_mem
  rw [hreparam, hphi_eq] at hb
  exact hb

/-- **Generic k-D simplex limit — modulo the pointwise heart.** GIVEN the generic pointwise
scale-change `hpw` (for every nonnegative continuous list `gs`, `PsiK R gs t → nestedPhi gs (1-t)`
for each `t`), the full `k`-D coupled log-weighted Riemann sum converges to the iterated simplex
integral, for EVERY nonnegative continuous list `Gs`:
`nestedLogSum R Gs R / (log R)^|Gs| → nestedPhi Gs 0 = ∫_{simplex} ∏ Gs`. Each list length is one
application of `weighted_riemann_cons_of_inner ∘ inner_uniform_kd_of_pointwise ∘ hpw` (base `nil`).

This isolates the ENTIRE remaining generic obligation to `hpw` — the generic `psi3_pointwise`, whose
own proof will be by strong induction feeding this theorem's `gs`-level conclusion back in (the
recursive heart). Everything else in the generic `k`-D induction is done. -/
theorem weighted_riemann_kd_of_pointwise
    (hpw : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) → (∀ g ∈ gs, Continuous g) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Tendsto (fun R : ℕ => PsiK R gs t) atTop (nhds (nestedPhi gs (1 - t))))
    (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSum R Gs R / (Real.log R) ^ Gs.length)
      atTop (nhds (nestedPhi Gs 0)) := by
  cases Gs with
  | nil => exact weighted_riemann_kd_nil
  | cons g gs =>
      have htail_nn : ∀ f ∈ gs, ∀ x, 0 ≤ f x := fun f hf => hnn f (List.mem_cons.mpr (Or.inr hf))
      have htail_cont : ∀ f ∈ gs, Continuous f :=
        fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf))
      refine weighted_riemann_cons_of_inner g gs
        (hcont g (List.mem_cons.mpr (Or.inl rfl))).continuousOn
        (nestedPhi_continuous gs htail_cont).continuousOn ?_
      exact inner_uniform_kd_of_pointwise gs htail_nn htail_cont (hpw gs htail_nn htail_cont)

/-! ### Infrastructure for the generic pointwise scale-change `psi_k_pointwise`.

The remaining lemma `psi_k_pointwise` (`hpw`) is proved by strong induction on `gs.length`, mirroring
`WeightedRiemann3D.psi3_pointwise`. The new wrinkle vs the concrete 3-D double sum is the **generic
drift over the nested sum**: at level `N = ⌊R^t⌋` and `c_R = log N/log R → t`, the "real" sum
`nestedLogSum R gs N` (log-ratios at base `R`) must be compared termwise with the rescaled Riemann
sum `nestedLogSum N (gs.map (·∘(t*·))) N` (log-ratios at base `N`). Both equal `evalNest (log N) c gs
N` for `c = c_R` resp. `c = t`, because `log n/log R = c_R · (log n/log N)`. The drift bound
(`evalNest_dist`) is the telescoping product inequality `|∏ aᵢ - ∏ bᵢ| ≤ ∑ⱼ … |aⱼ-bⱼ| …` summed over
the nested structure, bounded by the bare nested harmonic sum `harmNest`. -/

/-- The nested log-weighted sum with the log-ratios at "effective log-base" `L` and an extra **scale
factor** `c` on each argument: term `g (c · (log n / L)) / n`. Both `nestedLogSum R gs N` (base `R`,
via `c = log N/log R`) and `nestedLogSum N (t-scaled gs) N` (base `N`, via `c = t`) are instances at
`L = log N` — the common shape for the drift comparison. -/
noncomputable def evalNest (L c : ℝ) : List (ℝ → ℝ) → ℕ → ℝ
  | [], _ => 1
  | g :: gs, Q =>
      ∑ n ∈ Finset.Icc 2 Q, g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n)

/-- The bare nested harmonic sum (all functions `≡ 1`): `harmNest 0 _ = 1`,
`harmNest (k+1) Q = ∑_{n≤Q} (1/n)·harmNest k (Q/n)`. The drift bound's right factor. -/
noncomputable def harmNest : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (k + 1), Q => ∑ n ∈ Finset.Icc 2 Q, (1 : ℝ) / (n : ℝ) * harmNest k (Q / n)

@[simp] lemma evalNest_nil (L c : ℝ) (Q : ℕ) : evalNest L c [] Q = 1 := rfl

@[simp] lemma evalNest_cons (L c : ℝ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (Q : ℕ) :
    evalNest L c (g :: gs) Q
      = ∑ n ∈ Finset.Icc 2 Q, g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n) := rfl

@[simp] lemma harmNest_zero (Q : ℕ) : harmNest 0 Q = 1 := rfl

@[simp] lemma harmNest_succ (k Q : ℕ) :
    harmNest (k + 1) Q = ∑ n ∈ Finset.Icc 2 Q, (1 : ℝ) / (n : ℝ) * harmNest k (Q / n) := rfl

/-- `harmNest` is nonnegative. -/
lemma harmNest_nonneg : ∀ (k Q : ℕ), 0 ≤ harmNest k Q
  | 0, _ => by simp
  | (k + 1), Q => by
      rw [harmNest_succ]
      refine Finset.sum_nonneg (fun n hn => ?_)
      have : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by positivity
      exact mul_nonneg this (harmNest_nonneg k (Q / n))

/-- **Bridge 1.** With effective base `L = log N` and scale `c = log N / log R`, `evalNest` reproduces
the genuine `nestedLogSum R gs Q` (because `(log N/log R)·(log n/log N) = log n/log R`). Needs
`log N ≠ 0`. -/
lemma evalNest_eq_nestedLogSum_base (R N : ℕ) (hN : Real.log (N : ℝ) ≠ 0) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      evalNest (Real.log (N : ℝ)) (Real.log (N : ℝ) / Real.log (R : ℝ)) gs Q
        = nestedLogSum R gs Q
  | [], _ => by simp
  | g :: gs, Q => by
      rw [evalNest_cons, nestedLogSum_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [evalNest_eq_nestedLogSum_base R N hN gs (Q / n)]
      congr 2
      field_simp

/-- **Bridge 2.** With effective base `L = log N` and scale `c = t`, `evalNest` reproduces the
rescaled Riemann sum `nestedLogSum N (gs.map (·∘(t*·))) Q` (definitionally: the `t`-scaled function
applied to `log n/log N` is `g` applied to `t·(log n/log N)`). -/
lemma evalNest_eq_nestedLogSum_scaled (N : ℕ) (t : ℝ) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      evalNest (Real.log (N : ℝ)) t gs Q
        = nestedLogSum N (gs.map (fun g => fun u => g (t * u))) Q
  | [], _ => by simp
  | g :: gs, Q => by
      rw [evalNest_cons, List.map_cons, nestedLogSum_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [evalNest_eq_nestedLogSum_scaled N t gs (Q / n)]

/-- **Sup bound for `evalNest`.** If each `g ∈ gs` satisfies `|g (c·u)| ≤ M` for `u ∈ [0,1]`, and the
log-ratios stay `≤ 1` (`log m ≤ L` for `m ≤ Q`), then `|evalNest L c gs Q| ≤ (max M 1)^|gs| ·
harmNest |gs| Q`. Induction on `gs`; each level contributes a factor `≤ max M 1`. -/
lemma evalNest_abs_le (L : ℝ) (hL : 0 < L) (c M : ℝ) (hM : 0 ≤ M) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u)| ≤ M) →
      (∀ m : ℕ, m ≤ Q → Real.log (m : ℝ) ≤ L) →
      |evalNest L c gs Q| ≤ (max M 1) ^ gs.length * harmNest gs.length Q
  | [], Q, _, _ => by simp
  | g :: gs, Q, hbd, hQL => by
      set K := max M 1 with hKdef
      have hMK : M ≤ K := le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
      have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      rw [evalNest_cons]
      calc |∑ n ∈ Finset.Icc 2 Q,
                g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n)|
          ≤ ∑ n ∈ Finset.Icc 2 Q,
                |g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 2 Q,
                K ^ (g :: gs).length * ((1 / (n : ℝ)) * harmNest gs.length (Q / n)) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            obtain ⟨hn2, hnQ⟩ := Finset.mem_Icc.mp hn
            have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
            have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            have hu0 : 0 ≤ Real.log (n : ℝ) / L := div_nonneg hlogn0 hL.le
            have hu1 : Real.log (n : ℝ) / L ≤ 1 := by
              rw [div_le_one hL]; exact hQL n hnQ
            have hgbd : |g (c * (Real.log n / L))| ≤ M :=
              hbd g (List.mem_cons.mpr (Or.inl rfl)) _ hu0 hu1
            have hQL' : ∀ m : ℕ, m ≤ Q / n → Real.log (m : ℝ) ≤ L :=
              fun m hm => hQL m (le_trans hm (Nat.div_le_self Q n))
            have hIH := evalNest_abs_le L hL c M hM gs (Q / n)
              (fun f hf => hbd f (List.mem_cons.mpr (Or.inr hf))) hQL'
            have hharm0 : 0 ≤ harmNest gs.length (Q / n) := harmNest_nonneg _ _
            have hKgs0 : 0 ≤ K ^ gs.length := pow_nonneg hK0 _
            rw [abs_mul, abs_div, Nat.abs_cast]
            calc |g (c * (Real.log n / L))| / (n : ℝ) * |evalNest L c gs (Q / n)|
                ≤ M / (n : ℝ) * (K ^ gs.length * harmNest gs.length (Q / n)) := by
                  gcongr
              _ ≤ K ^ (g :: gs).length * ((1 / (n : ℝ)) * harmNest gs.length (Q / n)) := by
                  rw [List.length_cons, pow_succ]
                  rw [show M / (n : ℝ) * (K ^ gs.length * harmNest gs.length (Q / n))
                        = M * (K ^ gs.length * harmNest gs.length (Q / n)) * (1 / (n : ℝ)) from by ring,
                      show K ^ gs.length * K * ((1 / (n : ℝ)) * harmNest gs.length (Q / n))
                        = K * (K ^ gs.length * harmNest gs.length (Q / n)) * (1 / (n : ℝ)) from by ring]
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact mul_le_mul_of_nonneg_right hMK (by positivity)
        _ = K ^ (g :: gs).length * ∑ n ∈ Finset.Icc 2 Q,
                (1 / (n : ℝ)) * harmNest gs.length (Q / n) := by rw [Finset.mul_sum]
        _ = K ^ (g :: gs).length * harmNest (g :: gs).length Q := by
            rw [List.length_cons, harmNest_succ]

/-- **Drift bound for `evalNest`** (the telescoping product inequality over the nested sum). If each
`g ∈ gs` is bounded by `M` under both scales `c, c'` and the two scaled evaluations differ by `≤ ε`
on `[0,1]`, then the two nested sums differ by `≤ |gs| · (max M 1)^|gs| · ε · harmNest |gs| Q`. This
is the generic heart of `psi_k_pointwise`: the `c_R → t` argument drift, absorbed by uniform
continuity, times the bounded nested-harmonic sum. Induction on `gs`; the head split is
`a·A − b·B = a·(A−B) + (a−b)·B` (`evalNest_abs_le` bounds `B`, the IH bounds `A−B`). -/
lemma evalNest_dist (L : ℝ) (hL : 0 < L) (c c' M ε : ℝ) (hM : 0 ≤ M) (hε : 0 ≤ ε) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u)| ≤ M) →
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c' * u)| ≤ M) →
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u) - g (c' * u)| ≤ ε) →
      (∀ m : ℕ, m ≤ Q → Real.log (m : ℝ) ≤ L) →
      |evalNest L c gs Q - evalNest L c' gs Q|
        ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * ε * harmNest gs.length Q
  | [], Q, _, _, _, _ => by simp
  | g :: gs, Q, hbd, hbd', hclose, hQL => by
      set K := max M 1 with hKdef
      have hMK : M ≤ K := le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
      have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      rw [evalNest_cons, evalNest_cons, ← Finset.sum_sub_distrib]
      calc |∑ n ∈ Finset.Icc 2 Q,
                (g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n)
                  - g (c' * (Real.log n / L)) / (n : ℝ) * evalNest L c' gs (Q / n))|
          ≤ ∑ n ∈ Finset.Icc 2 Q,
                |g (c * (Real.log n / L)) / (n : ℝ) * evalNest L c gs (Q / n)
                  - g (c' * (Real.log n / L)) / (n : ℝ) * evalNest L c' gs (Q / n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 2 Q,
                (((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε)
                  * ((1 / (n : ℝ)) * harmNest gs.length (Q / n)) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            obtain ⟨hn2, hnQ⟩ := Finset.mem_Icc.mp hn
            have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
            have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            have hu0 : 0 ≤ Real.log (n : ℝ) / L := div_nonneg hlogn0 hL.le
            have hu1 : Real.log (n : ℝ) / L ≤ 1 := by rw [div_le_one hL]; exact hQL n hnQ
            have hgM : |g (c * (Real.log n / L))| ≤ M :=
              hbd g (List.mem_cons.mpr (Or.inl rfl)) _ hu0 hu1
            have hgcl : |g (c * (Real.log n / L)) - g (c' * (Real.log n / L))| ≤ ε :=
              hclose g (List.mem_cons.mpr (Or.inl rfl)) _ hu0 hu1
            have hQL' : ∀ m : ℕ, m ≤ Q / n → Real.log (m : ℝ) ≤ L :=
              fun m hm => hQL m (le_trans hm (Nat.div_le_self Q n))
            have hAB := evalNest_dist L hL c c' M ε hM hε gs (Q / n)
              (fun f hf => hbd f (List.mem_cons.mpr (Or.inr hf)))
              (fun f hf => hbd' f (List.mem_cons.mpr (Or.inr hf)))
              (fun f hf => hclose f (List.mem_cons.mpr (Or.inr hf))) hQL'
            have hB := evalNest_abs_le L hL c' M hM gs (Q / n)
              (fun f hf => hbd' f (List.mem_cons.mpr (Or.inr hf))) hQL'
            set A := evalNest L c gs (Q / n) with hAdef
            set B := evalNest L c' gs (Q / n) with hBdef
            set hh := harmNest gs.length (Q / n) with hhdef
            have hh0 : 0 ≤ hh := harmNest_nonneg _ _
            have hKgs0 : 0 ≤ K ^ gs.length := pow_nonneg hK0 _
            have hg0 : (0 : ℝ) ≤ (gs.length : ℝ) := Nat.cast_nonneg _
            rw [show g (c * (Real.log n / L)) / (n : ℝ) * A
                    - g (c' * (Real.log n / L)) / (n : ℝ) * B
                  = (1 / (n : ℝ))
                      * (g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B) from by ring,
                abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
            have hbound : |g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B|
                ≤ M * ((gs.length : ℝ) * K ^ gs.length * ε * hh) + ε * (K ^ gs.length * hh) := by
              rw [show g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B
                    = g (c * (Real.log n / L)) * (A - B)
                      + (g (c * (Real.log n / L)) - g (c' * (Real.log n / L))) * B from by ring]
              calc |g (c * (Real.log n / L)) * (A - B)
                      + (g (c * (Real.log n / L)) - g (c' * (Real.log n / L))) * B|
                  ≤ |g (c * (Real.log n / L)) * (A - B)|
                      + |(g (c * (Real.log n / L)) - g (c' * (Real.log n / L))) * B| := abs_add_le _ _
                _ = |g (c * (Real.log n / L))| * |A - B|
                      + |g (c * (Real.log n / L)) - g (c' * (Real.log n / L))| * |B| := by
                    rw [abs_mul, abs_mul]
                _ ≤ M * ((gs.length : ℝ) * K ^ gs.length * ε * hh) + ε * (K ^ gs.length * hh) := by
                    gcongr
            have hbase : (0 : ℝ) ≤ 1 / (n : ℝ) * hh * K ^ gs.length * ε := by positivity
            have hscalar : (gs.length : ℝ) * M + 1 ≤ ((gs.length : ℝ) + 1) * K := by
              nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hMK), hK1]
            calc (1 / (n : ℝ)) * |g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B|
                ≤ (1 / (n : ℝ))
                    * (M * ((gs.length : ℝ) * K ^ gs.length * ε * hh) + ε * (K ^ gs.length * hh)) :=
                  mul_le_mul_of_nonneg_left hbound (by positivity)
              _ = (1 / (n : ℝ) * hh * K ^ gs.length * ε) * ((gs.length : ℝ) * M + 1) := by ring
              _ ≤ (1 / (n : ℝ) * hh * K ^ gs.length * ε) * (((gs.length : ℝ) + 1) * K) :=
                  mul_le_mul_of_nonneg_left hscalar hbase
              _ = ((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε
                    * ((1 / (n : ℝ)) * hh) := by ring
        _ = (((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε)
              * ∑ n ∈ Finset.Icc 2 Q, (1 / (n : ℝ)) * harmNest gs.length (Q / n) := by
            rw [Finset.mul_sum]
        _ = ((g :: gs).length : ℝ) * K ^ (g :: gs).length * ε * harmNest (g :: gs).length Q := by
            rw [List.length_cons, harmNest_succ, pow_succ]; push_cast; ring

/-! ### Change-of-variables for `nestedPhi` (the generic `phi2_scale`).

`nestedPhi gs (1-t) = t^|gs| · nestedPhi (gs.map (t-scale)) 0`. Proved through the explicit-budget
form `simplexPhi gs a` (bounds `a`, `a-y`, …), via `nestedPhi_eq_simplexPhi` and `simplexPhi_scale`
(one linear substitution `y = t·z` per level, `intervalIntegral.mul_integral_comp_mul_left`). -/

/-- Iterated simplex cross-section integral, explicit-budget form (outer bound `a`, inner `a-y`, …).
`simplexPhi gs a = ∫_{∑yᵢ ≤ a, yᵢ≥0} ∏ gᵢ(yᵢ)`. The budget-form sibling of `nestedPhi`. -/
noncomputable def simplexPhi : List (ℝ → ℝ) → ℝ → ℝ
  | [], _ => 1
  | g :: gs, a => ∫ y in (0 : ℝ)..a, g y * simplexPhi gs (a - y)

@[simp] lemma simplexPhi_nil (a : ℝ) : simplexPhi [] a = 1 := rfl

@[simp] lemma simplexPhi_cons (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (a : ℝ) :
    simplexPhi (g :: gs) a = ∫ y in (0 : ℝ)..a, g y * simplexPhi gs (a - y) := rfl

/-- `nestedPhi gs (1-a) = simplexPhi gs a` (the offset vs budget forms agree). Induction on `gs`. -/
lemma nestedPhi_eq_simplexPhi : ∀ (gs : List (ℝ → ℝ)) (a : ℝ),
    nestedPhi gs (1 - a) = simplexPhi gs a
  | [], _ => by simp
  | g :: gs, a => by
      rw [nestedPhi_cons, simplexPhi_cons, show (1 : ℝ) - (1 - a) = a from by ring]
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      rw [show (1 : ℝ) - a + y = 1 - (a - y) from by ring, nestedPhi_eq_simplexPhi gs (a - y)]

/-- **Scaling for `simplexPhi`.** `simplexPhi gs (t·a) = t^|gs| · simplexPhi (gs.map (t-scale)) a`.
Induction on `gs`; the cons step substitutes `y = t·z` (`mul_integral_comp_mul_left`) then applies
the IH at budget `a-z`. -/
lemma simplexPhi_scale (t : ℝ) (ht : t ≠ 0) :
    ∀ (gs : List (ℝ → ℝ)) (a : ℝ),
      simplexPhi gs (t * a)
        = t ^ gs.length * simplexPhi (gs.map (fun g => fun u => g (t * u))) a
  | [], _ => by simp
  | g :: gs, a => by
      rw [List.map_cons, simplexPhi_cons, simplexPhi_cons, List.length_cons, pow_succ]
      have key : (∫ y in (0 : ℝ)..(t * a), g y * simplexPhi gs (t * a - y))
          = t * ∫ z in (0 : ℝ)..a, g (t * z) * simplexPhi gs (t * (a - z)) := by
        have h := intervalIntegral.mul_integral_comp_mul_left (a := (0 : ℝ)) (b := a)
          (f := fun y => g y * simplexPhi gs (t * a - y)) t
        simp only [mul_zero] at h
        rw [← h]
        congr 1
        refine intervalIntegral.integral_congr (fun z _ => ?_)
        rw [show t * a - t * z = t * (a - z) from by ring]
      rw [key]
      have hint : (∫ z in (0 : ℝ)..a, g (t * z) * simplexPhi gs (t * (a - z)))
          = t ^ gs.length
              * ∫ z in (0 : ℝ)..a, g (t * z)
                  * simplexPhi (gs.map (fun g => fun u => g (t * u))) (a - z) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun z _ => ?_)
        rw [simplexPhi_scale t ht gs (a - z)]
        ring
      rw [hint]
      beta_reduce
      ring

/-- **Change of variables for `nestedPhi`** (the generic `phi2_scale`): `nestedPhi gs (1-t) =
t^|gs| · nestedPhi (gs.map (t-scale)) 0`, for `t ≠ 0`. Chains `nestedPhi_eq_simplexPhi` ∘
`simplexPhi_scale` at budget `a = 1`. -/
theorem nestedPhi_scale (gs : List (ℝ → ℝ)) (t : ℝ) (ht : t ≠ 0) :
    nestedPhi gs (1 - t)
      = t ^ gs.length * nestedPhi (gs.map (fun g => fun u => g (t * u))) 0 := by
  rw [nestedPhi_eq_simplexPhi gs t]
  have h1 := simplexPhi_scale t ht gs 1
  rw [mul_one] at h1
  rw [h1, ← nestedPhi_eq_simplexPhi (gs.map (fun g => fun u => g (t * u))) 1]
  norm_num

/-- `harmNest k Q` is the bare nested log-harmonic sum, i.e. `nestedLogSum N (replicate k 1) Q`.
Induction on `k`; the cons step matches `harmNest_succ` once the head function `≡ 1` cancels. -/
lemma harmNest_eq_nestedLogSum (N : ℕ) :
    ∀ (k Q : ℕ), harmNest k Q = nestedLogSum N (List.replicate k (fun _ : ℝ => (1 : ℝ))) Q
  | 0, _ => by simp
  | (k + 1), Q => by
      rw [harmNest_succ, List.replicate_succ, nestedLogSum_cons]
      exact Finset.sum_congr rfl (fun n _ => by rw [harmNest_eq_nestedLogSum N k (Q / n)])

/-- A uniform sup bound `M ≥ 0` for a finite list of continuous functions on `[0,1]`. Induction on
the list (take `max` at each cons). -/
lemma exists_list_bound : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, Continuous g) →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ gs, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ M
  | [], _ => ⟨0, le_refl _, fun g hg => absurd hg (List.not_mem_nil)⟩
  | g :: gs, hcont => by
      obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hcont g (List.mem_cons.mpr (Or.inl rfl))).continuousOn
      obtain ⟨M', hM'0, hM'⟩ :=
        exists_list_bound gs (fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf)))
      have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0 ⟨le_refl _, zero_le_one⟩)
      refine ⟨max Mg M', le_max_of_le_left hMg0, fun f hf x hx => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hf'
      · exact le_trans (hMg x hx) (le_max_left _ _)
      · exact le_trans (hM' f hf' x hx) (le_max_right _ _)

/-- A single uniform-continuity modulus `δ > 0` working for ALL functions in a finite continuous
list on `[0,1]`. Induction on the list (take `min` at each cons). -/
lemma exists_list_unif : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, Continuous g) → ∀ ε > 0,
    ∃ δ > 0, ∀ g ∈ gs, ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      |a - b| ≤ δ → |g a - g b| ≤ ε
  | [], _, ε, _ => ⟨1, one_pos, fun g hg => absurd hg (List.not_mem_nil)⟩
  | g :: gs, hcont, ε, hε => by
      have hucG : UniformContinuousOn g (Set.Icc (0 : ℝ) 1) :=
        isCompact_Icc.uniformContinuousOn_of_continuous
          (hcont g (List.mem_cons.mpr (Or.inl rfl))).continuousOn
      obtain ⟨δG, hδG0, hδG⟩ := Metric.uniformContinuousOn_iff_le.1 hucG ε hε
      obtain ⟨δ', hδ'0, hδ'⟩ :=
        exists_list_unif gs (fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf))) ε hε
      refine ⟨min δG δ', lt_min hδG0 hδ'0, fun f hf a ha b hb hab => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hf'
      · have := hδG a ha b hb (le_trans hab (min_le_left _ _))
        rwa [Real.dist_eq] at this
      · exact hδ' f hf' a ha b hb (le_trans hab (min_le_right _ _))

/-- At `t = 0`, `PsiK R gs 0 = nestedPhi gs 1` exactly (independent of `R`): for `gs = []` both are
`1`; for a cons the sum range `Icc 2 ⌊R^0⌋ = Icc 2 1 = ∅` and the integral over `[0,0]` both vanish. -/
lemma psiK_zero (R : ℕ) : ∀ (gs : List (ℝ → ℝ)), PsiK R gs 0 = nestedPhi gs 1
  | [] => by simp [PsiK, Real.rpow_zero]
  | g :: gs => by
      simp only [PsiK, Real.rpow_zero, Nat.floor_one, nestedLogSum_cons]
      rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from rfl]
      simp only [Finset.sum_empty, zero_div]
      rw [nestedPhi_cons, show (1 : ℝ) - 1 = 0 from by ring, intervalIntegral.integral_same]

open BoundedGaps.InnerUniformReduction (tendsto_logFloor_rpow_div) in
/-- **Generic pointwise scale-change** (the generic `psi3_pointwise`), MODULO the full `k`-D limit for
same-length lists (`hkd`). For `t ∈ [0,1]` and nonnegative continuous `gs`, `PsiK R gs t →
nestedPhi gs (1-t)`. Strategy (mirroring `psi3_pointwise` via the `evalNest`/`harmNest` drift
machinery): set `N = ⌊R^t⌋`, `c_R = log N/log R → t`, rescaled list `gss = gs.map (·∘(t·))`. Then
`PsiK R gs t = c_R^k · (nestedLogSum N gss N/(log N)^k + drift/(log N)^k)`, where the scaled Riemann
sum converges by `hkd gss` and the `c_R → t` drift `→ 0` (`evalNest_dist`, uniform continuity over the
finite list); the limit is `t^k · nestedPhi gss 0 = nestedPhi gs (1-t)` (`nestedPhi_scale`). -/
theorem psi_k_pointwise (gs : List (ℝ → ℝ))
    (hnn : ∀ g ∈ gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ gs, Continuous g)
    (hkd : ∀ (hs : List (ℝ → ℝ)), hs.length = gs.length → (∀ g ∈ hs, ∀ x, 0 ≤ g x) →
        (∀ g ∈ hs, Continuous g) →
        Tendsto (fun R : ℕ => nestedLogSum R hs R / (Real.log R) ^ hs.length) atTop
          (nhds (nestedPhi hs 0)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => PsiK R gs t) atTop (nhds (nestedPhi gs (1 - t))) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with hteq | htpos
  · -- `t = 0`: constant sequence `nestedPhi gs 1`.
    rw [← hteq]
    simp only [psiK_zero, sub_zero]
    exact tendsto_const_nhds
  · -- `t > 0`.
    set gss : List (ℝ → ℝ) := gs.map (fun g => fun u => g (t * u)) with hgss
    have hgss_len : gss.length = gs.length := by rw [hgss, List.length_map]
    have hgss_nn : ∀ f ∈ gss, ∀ x, 0 ≤ f x := by
      intro f hf x; rw [hgss, List.mem_map] at hf
      obtain ⟨g, hg, rfl⟩ := hf; exact hnn g hg (t * x)
    have hgss_cont : ∀ f ∈ gss, Continuous f := by
      intro f hf; rw [hgss, List.mem_map] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact (hcont g hg).comp (continuous_const.mul continuous_id)
    set N : ℕ → ℕ := fun R => ⌊(R : ℝ) ^ t⌋₊ with hN
    have hNtop : Tendsto N atTop atTop := by
      have : Tendsto (fun R : ℕ => (R : ℝ) ^ t) atTop atTop :=
        (tendsto_rpow_atTop htpos).comp tendsto_natCast_atTop_atTop
      exact tendsto_nat_floor_atTop.comp this
    have hcR : Tendsto (fun R : ℕ => Real.log (N R : ℝ) / Real.log (R : ℝ)) atTop (𝓝 t) :=
      tendsto_logFloor_rpow_div t htpos
    -- scaled Riemann sum at level `N` → `nestedPhi gss 0`.
    have hB : Tendsto (fun R : ℕ =>
        nestedLogSum (N R) gss (N R) / (Real.log (N R : ℝ)) ^ gs.length) atTop
        (𝓝 (nestedPhi gss 0)) := by
      have hlim := hkd gss hgss_len hgss_nn hgss_cont
      rw [hgss_len] at hlim
      exact hlim.comp hNtop
    -- list sup bound `M` and the nested-harmonic bound `C`.
    obtain ⟨M, hM0, hM⟩ := exists_list_bound gs hcont
    obtain ⟨C, hC0, hharm⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
        harmNest gs.length (N R) / (Real.log (N R : ℝ)) ^ gs.length ≤ C := by
      have hones_nn : ∀ g ∈ List.replicate gs.length (fun _ : ℝ => (1 : ℝ)), ∀ x, 0 ≤ g x := by
        intro g hg; rw [List.eq_of_mem_replicate hg]; intro x; norm_num
      have hones_cont : ∀ g ∈ List.replicate gs.length (fun _ : ℝ => (1 : ℝ)), Continuous g := by
        intro g hg; rw [List.eq_of_mem_replicate hg]; exact continuous_const
      have hlim := (hkd (List.replicate gs.length (fun _ : ℝ => (1 : ℝ)))
        (by rw [List.length_replicate]) hones_nn hones_cont).comp hNtop
      rw [List.length_replicate] at hlim
      refine ⟨|nestedPhi (List.replicate gs.length (fun _ : ℝ => (1 : ℝ))) 0| + 1, by positivity, ?_⟩
      have h1 := (Metric.tendsto_nhds.1 hlim) 1 one_pos
      filter_upwards [h1] with R hR
      simp only [Function.comp_apply] at hR
      rw [Real.dist_eq, ← harmNest_eq_nestedLogSum (N R) gs.length (N R)] at hR
      have h2 := (abs_lt.1 hR).2
      have h3 := le_abs_self (nestedPhi (List.replicate gs.length (fun _ : ℝ => (1 : ℝ))) 0)
      linarith
    -- drift `→ 0`.
    have hdrift : Tendsto (fun R : ℕ =>
        (nestedLogSum R gs (N R) - nestedLogSum (N R) gss (N R)) / (Real.log (N R : ℝ)) ^ gs.length)
        atTop (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      have hKp0 : (0 : ℝ) < (max M 1) ^ gs.length := by positivity
      have hkn : (0 : ℝ) ≤ (gs.length : ℝ) := Nat.cast_nonneg _
      have hP0 : (0 : ℝ) ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * C :=
        mul_nonneg (mul_nonneg hkn hKp0.le) hC0.le
      have hden0 : (0 : ℝ) < 2 * ((gs.length : ℝ) * (max M 1) ^ gs.length * C + 1) := by
        have := hP0; linarith
      set εpp : ℝ := ε / (2 * ((gs.length : ℝ) * (max M 1) ^ gs.length * C + 1)) with hεppdef
      have hεpp0 : 0 < εpp := by rw [hεppdef]; exact div_pos hε hden0
      have hεppfin : (gs.length : ℝ) * (max M 1) ^ gs.length * C * εpp < ε := by
        rw [hεppdef, ← mul_div_assoc, div_lt_iff₀ hden0]
        nlinarith [mul_nonneg hP0 hε.le, hε]
      obtain ⟨δ, hδ0, hδ⟩ := exists_list_unif gs hcont εpp hεpp0
      have hcRδ : ∀ᶠ R : ℕ in atTop, |Real.log (N R : ℝ) / Real.log (R : ℝ) - t| ≤ δ := by
        have := Metric.tendsto_nhds.1 hcR δ hδ0
        filter_upwards [this] with R hR; rw [Real.dist_eq] at hR; linarith
      filter_upwards [hcRδ, hharm, hNtop.eventually_ge_atTop 2, eventually_ge_atTop 2]
        with R hcRδR hharmR hNR2 hR2
      have hNR1 : (1 : ℝ) < (N R : ℝ) := by exact_mod_cast (by omega : 1 < N R)
      have hlogNpos : 0 < Real.log (N R : ℝ) := Real.log_pos hNR1
      have hlogNne : Real.log (N R : ℝ) ≠ 0 := ne_of_gt hlogNpos
      have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
      have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hR1
      have hNRleR : (N R : ℝ) ≤ (R : ℝ) := by
        have ha : (N R : ℝ) ≤ (R : ℝ) ^ t := Nat.floor_le (by positivity)
        have hb : (R : ℝ) ^ t ≤ (R : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1.le ht1
        rw [Real.rpow_one] at hb; linarith
      set cR : ℝ := Real.log (N R : ℝ) / Real.log (R : ℝ) with hcRdef
      have hcR0 : 0 ≤ cR := by rw [hcRdef]; positivity
      have hcR1 : cR ≤ 1 := by
        rw [hcRdef, div_le_one hlogRpos]; exact Real.log_le_log (by positivity) hNRleR
      have hmem : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ u : ℝ, 0 ≤ u → u ≤ 1 → c * u ∈ Set.Icc (0 : ℝ) 1 :=
        fun c hc0 hc1 u hu0 hu1 =>
          ⟨mul_nonneg hc0 hu0, by nlinarith [mul_le_mul hc1 hu1 hu0 (zero_le_one : (0:ℝ) ≤ 1)]⟩
      have hbdc : ∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (cR * u)| ≤ M :=
        fun g hg u hu0 hu1 => hM g hg (cR * u) (hmem cR hcR0 hcR1 u hu0 hu1)
      have hbdt : ∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (t * u)| ≤ M :=
        fun g hg u hu0 hu1 => hM g hg (t * u) (hmem t ht0 ht1 u hu0 hu1)
      have hclose : ∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (cR * u) - g (t * u)| ≤ εpp := by
        intro g hg u hu0 hu1
        refine hδ g hg (cR * u) (hmem cR hcR0 hcR1 u hu0 hu1) (t * u) (hmem t ht0 ht1 u hu0 hu1) ?_
        rw [show cR * u - t * u = (cR - t) * u from by ring, abs_mul, abs_of_nonneg hu0]
        calc |cR - t| * u ≤ δ * 1 := mul_le_mul hcRδR hu1 hu0 hδ0.le
          _ = δ := mul_one δ
      have hQL : ∀ m : ℕ, m ≤ N R → Real.log (m : ℝ) ≤ Real.log (N R : ℝ) := by
        intro m hm
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · rw [Nat.cast_zero, Real.log_zero]; exact hlogNpos.le
        · exact Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hm)
      have hdist := evalNest_dist (Real.log (N R : ℝ)) hlogNpos cR t M εpp hM0 hεpp0.le gs (N R)
        hbdc hbdt hclose hQL
      have hDeq : nestedLogSum R gs (N R) - nestedLogSum (N R) gss (N R)
          = evalNest (Real.log (N R : ℝ)) cR gs (N R)
            - evalNest (Real.log (N R : ℝ)) t gs (N R) := by
        rw [hcRdef, evalNest_eq_nestedLogSum_base R (N R) hlogNne gs (N R),
            evalNest_eq_nestedLogSum_scaled (N R) t gs (N R)]
      rw [← hDeq] at hdist
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogNpos gs.length)]
      have hlogNk : (0 : ℝ) < (Real.log (N R : ℝ)) ^ gs.length := pow_pos hlogNpos gs.length
      have hpre0 : 0 ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * εpp :=
        mul_nonneg (mul_nonneg hkn hKp0.le) hεpp0.le
      calc |nestedLogSum R gs (N R) - nestedLogSum (N R) gss (N R)|
              / (Real.log (N R : ℝ)) ^ gs.length
          ≤ ((gs.length : ℝ) * (max M 1) ^ gs.length * εpp * harmNest gs.length (N R))
              / (Real.log (N R : ℝ)) ^ gs.length := by
            apply div_le_div_of_nonneg_right hdist hlogNk.le
        _ = (gs.length : ℝ) * (max M 1) ^ gs.length * εpp
              * (harmNest gs.length (N R) / (Real.log (N R : ℝ)) ^ gs.length) := by ring
        _ ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * εpp * C :=
            mul_le_mul_of_nonneg_left hharmR hpre0
        _ = (gs.length : ℝ) * (max M 1) ^ gs.length * C * εpp := by ring
        _ < ε := hεppfin
    -- assemble: `PsiK = c_R^k · (B + drift)`, limit `t^k · nestedPhi gss 0 = nestedPhi gs (1-t)`.
    have hAk : Tendsto (fun R : ℕ => (Real.log (N R : ℝ) / Real.log (R : ℝ)) ^ gs.length) atTop
        (𝓝 (t ^ gs.length)) := hcR.pow gs.length
    have hcomb := hAk.mul (hB.add hdrift)
    rw [show nestedPhi gs (1 - t) = t ^ gs.length * (nestedPhi gss 0 + 0) from by
      rw [add_zero]; exact nestedPhi_scale gs t (ne_of_gt htpos)]
    refine hcomb.congr' ?_
    filter_upwards [hNtop.eventually_ge_atTop 2, eventually_ge_atTop 2] with R hNR2 hR2
    have hlogNne : Real.log (N R : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N R)))
    have hlogRne : Real.log (R : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < R)))
    show (Real.log (N R : ℝ) / Real.log (R : ℝ)) ^ gs.length
        * (nestedLogSum (N R) gss (N R) / (Real.log (N R : ℝ)) ^ gs.length
           + (nestedLogSum R gs (N R) - nestedLogSum (N R) gss (N R))
             / (Real.log (N R : ℝ)) ^ gs.length)
      = nestedLogSum R gs (N R) / (Real.log (R : ℝ)) ^ gs.length
    rw [div_pow]
    field_simp
    ring

/-- **The unconditional generic `k`-D weighted Riemann limit** (strong induction on the list length).
For every nonnegative continuous list `Gs`, the fully-coupled `k`-D log-weighted Riemann sum over
`∏ nᵢ ≤ R` converges to the iterated simplex integral `nestedPhi Gs 0 = ∫_{simplex} ∏ Gs`. The cons
step builds `psi_k_pointwise gs` (length `k`) from the IH (full limits for all length-`k` lists, the
scaled and all-ones lists in particular), then upgrades to inner-uniform and applies the engine. -/
theorem weighted_riemann_kd_aux : ∀ (n : ℕ) (Gs : List (ℝ → ℝ)), Gs.length = n →
    (∀ g ∈ Gs, ∀ x, 0 ≤ g x) → (∀ g ∈ Gs, Continuous g) →
    Tendsto (fun R : ℕ => nestedLogSum R Gs R / (Real.log R) ^ Gs.length) atTop
      (nhds (nestedPhi Gs 0)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Gs hlen hnn hcont
    cases Gs with
    | nil => exact weighted_riemann_kd_nil
    | cons g gs =>
        have htail_nn : ∀ f ∈ gs, ∀ x, 0 ≤ f x :=
          fun f hf => hnn f (List.mem_cons.mpr (Or.inr hf))
        have htail_cont : ∀ f ∈ gs, Continuous f :=
          fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf))
        have hgslt : gs.length < n := by rw [← hlen, List.length_cons]; omega
        have hkd_gs : ∀ (hs : List (ℝ → ℝ)), hs.length = gs.length → (∀ g ∈ hs, ∀ x, 0 ≤ g x) →
            (∀ g ∈ hs, Continuous g) →
            Tendsto (fun R : ℕ => nestedLogSum R hs R / (Real.log R) ^ hs.length) atTop
              (nhds (nestedPhi hs 0)) :=
          fun hs hhs hnn' hcont' => IH gs.length hgslt hs hhs hnn' hcont'
        refine weighted_riemann_cons_of_inner g gs
          (hcont g (List.mem_cons.mpr (Or.inl rfl))).continuousOn
          (nestedPhi_continuous gs htail_cont).continuousOn ?_
        exact inner_uniform_kd_of_pointwise gs htail_nn htail_cont
          (fun t ht => psi_k_pointwise gs htail_nn htail_cont hkd_gs t ht)

/-- **Generic `k`-D weighted Riemann limit** (the headline). `nestedLogSum R Gs R / (log R)^|Gs| →
nestedPhi Gs 0 = ∫_{simplex} ∏ Gs`, unconditional for every nonnegative continuous `Gs`. -/
theorem weighted_riemann_kd (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x)
    (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSum R Gs R / (Real.log R) ^ Gs.length) atTop
      (nhds (nestedPhi Gs 0)) :=
  weighted_riemann_kd_aux Gs.length Gs rfl hnn hcont

end BoundedGaps.WeightedRiemannKD
