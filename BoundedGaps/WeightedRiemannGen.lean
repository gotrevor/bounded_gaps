import BoundedGaps.WeightedRiemannKD

/-!
# Generic-weight `k`-D coupled Riemann limit (abstraction over the per-index weight).

`WeightedRiemannKD.weighted_riemann_kd` proves the `k`-D simplex limit for the **bare** harmonic
weight `1/n`. The GPY/Maynard `y_r`-space leaf (`s1`) needs the SAME ladder for the `(μ²/φ)` weight
(`SingularSeries.gMoebiusSqTotient`). Rather than copy the 850-line proof one weight over, this file
abstracts the **entire** ladder over an arbitrary nonnegative per-index weight `w : ℕ → ℝ`,
parametrised by a single analytic input — the 1-D weighted Riemann limit `Weighted1DLimit w`.

Key structural observation: the **limit side** (`nestedPhi`, `nestedPhi_scale`, `nestedPhi_continuous`,
`simplexPhi`, `exists_list_bound/unif`) is *weight-independent* and is reused verbatim from
`WeightedRiemannKD`. Only the **sum side** carries the weight; here every `/(n:ℝ)` of the bare ladder
becomes `* w n`, every `harmNest` becomes `harmNestW w`, and `0 ≤ 1/n` becomes the hypothesis
`0 ≤ w n`. The drift heart `evalNest_dist` and the strong-induction `psi_k_pointwise` port unchanged
in structure.

Instances:
- bare `w n = 1/n` recovers `weighted_riemann_kd` (via `riemann_sum_log_weight`);
- `w = gMoebiusSqTotient` gives the `μ²/φ` `y_r`-space ladder (via the continuous μ²/φ Mertens limit).

This file: definitions, basic lemmas, the factor step, the `perturbed_riemann_gen`-driven cons step,
the Pólya inner-uniform reduction and the assembly `weighted_riemann_kd_of_pointwise_w` (modulo the
generic pointwise heart `hpw`). The drift heart + headline live below.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace BoundedGaps.WeightedRiemannGen

open BoundedGaps.WeightedRiemannKD
open BoundedGaps.WeightedRiemann2D (perturbed_riemann_gen)

/-- **The 1-D weighted Riemann limit for weight `w`** (continuous form, weight-on-the-right). The
single analytic input the whole generic ladder rests on: for every continuous `G` on `[0,1]`,
`(∑_{2≤m≤N} G(log m/log N)·w m)/log N → ∫₀¹ G`. The bare weight `1/n` satisfies it via
`riemann_sum_log_weight`; the `μ²/φ` weight via the continuous μ²/φ Mertens limit. -/
def Weighted1DLimit (w : ℕ → ℝ) : Prop :=
  ∀ (G : ℝ → ℝ), ContinuousOn G (Set.Icc (0 : ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) * w m) / Real.log N)
      atTop (nhds (∫ x in (0 : ℝ)..1, G x))

/-- Generic nested truncated weighted sum: each level carries the weight `w n` (the bare ladder's
`1/n`). `nestedLogSumW w R (g::gs) Q = ∑_{2≤n≤Q} g(log n/log R)·w n·nestedLogSumW w R gs (Q/n)`. -/
noncomputable def nestedLogSumW (w : ℕ → ℝ) (R : ℕ) : List (ℝ → ℝ) → ℕ → ℝ
  | [], _ => 1
  | g :: gs, Q =>
      ∑ n ∈ Finset.Icc 2 Q, g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n)

@[simp] lemma nestedLogSumW_nil (w : ℕ → ℝ) (R Q : ℕ) : nestedLogSumW w R [] Q = 1 := rfl

@[simp] lemma nestedLogSumW_cons (w : ℕ → ℝ) (R : ℕ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (Q : ℕ) :
    nestedLogSumW w R (g :: gs) Q
      = ∑ n ∈ Finset.Icc 2 Q,
          g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n) :=
  rfl

/-- **`nestedLogSumW` is nonnegative** for nonnegative function lists and nonnegative weight. -/
lemma nestedLogSumW_nonneg (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (R : ℕ) :
    ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) → ∀ Q, 0 ≤ nestedLogSumW w R gs Q
  | [], _, _ => by rw [nestedLogSumW_nil]; norm_num
  | g :: gs, h, Q => by
      rw [nestedLogSumW_cons]
      refine Finset.sum_nonneg (fun n _ => ?_)
      have hg : ∀ x, 0 ≤ g x := h g (List.mem_cons.mpr (Or.inl rfl))
      have hgs : 0 ≤ nestedLogSumW w R gs (Q / n) :=
        nestedLogSumW_nonneg w hw0 R gs (fun f hf => h f (List.mem_cons.mpr (Or.inr hf))) (Q / n)
      exact mul_nonneg (mul_nonneg (hg _) (hw0 n)) hgs

/-- **`nestedLogSumW R gs` is monotone in the budget `Q`** for nonnegative lists and weight. -/
lemma nestedLogSumW_mono (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (R : ℕ) :
    ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) → Monotone (nestedLogSumW w R gs)
  | [], _ => by
      rw [show nestedLogSumW w R [] = fun _ => (1 : ℝ) from rfl]; exact monotone_const
  | g :: gs, h => by
      intro Q Q' hQ
      have hg : ∀ x, 0 ≤ g x := h g (List.mem_cons.mpr (Or.inl rfl))
      have htail := fun f hf => h f (List.mem_cons.mpr (Or.inr hf))
      have hgs_nn : ∀ Q, 0 ≤ nestedLogSumW w R gs Q := nestedLogSumW_nonneg w hw0 R gs htail
      have hgs_mono : Monotone (nestedLogSumW w R gs) := nestedLogSumW_mono w hw0 R gs htail
      rw [nestedLogSumW_cons, nestedLogSumW_cons]
      calc ∑ n ∈ Finset.Icc 2 Q,
              g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n)
          ≤ ∑ n ∈ Finset.Icc 2 Q,
              g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q' / n) :=
            Finset.sum_le_sum (fun n _ =>
              mul_le_mul_of_nonneg_left (hgs_mono (Nat.div_le_div_right hQ))
                (mul_nonneg (hg _) (hw0 n)))
        _ ≤ ∑ n ∈ Finset.Icc 2 Q',
              g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q' / n) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ)
              (fun n _ _ => mul_nonneg (mul_nonneg (hg _) (hw0 n)) (hgs_nn _))

/-- The reparametrised level-`k` nested weighted sum (outer truncation `⌊R^t⌋`), normalised. -/
noncomputable def PsiKW (w : ℕ → ℝ) (R : ℕ) (gs : List (ℝ → ℝ)) (t : ℝ) : ℝ :=
  nestedLogSumW w R gs ⌊(R : ℝ) ^ t⌋₊ / (Real.log R) ^ gs.length

/-- **`PsiKW R gs` is monotone in `t`** (for nonnegative `gs` and weight). -/
lemma psiKW_monotoneOn (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (R : ℕ) (gs : List (ℝ → ℝ))
    (h : ∀ g ∈ gs, ∀ x, 0 ≤ g x) :
    MonotoneOn (PsiKW w R gs) (Set.Icc (0 : ℝ) 1) := by
  rcases Nat.lt_or_ge R 2 with hRlt | hR2
  · have hlog0 : Real.log (R : ℝ) = 0 := by interval_cases R <;> simp
    intro a _ b _ _
    rcases gs with _ | ⟨g, gs'⟩
    · simp [PsiKW]
    · simp [PsiKW, hlog0, List.length_cons, zero_pow]
  · have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    intro a _ b _ hab
    have hpow : (R : ℝ) ^ a ≤ (R : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le hR1' hab
    have hfloor : ⌊(R : ℝ) ^ a⌋₊ ≤ ⌊(R : ℝ) ^ b⌋₊ := Nat.floor_mono hpow
    exact div_le_div_of_nonneg_right (nestedLogSumW_mono w hw0 R gs h hfloor) (by positivity)

/-- At `t = 0`, `PsiKW R gs 0 = nestedPhi gs 1` (independent of `R`). -/
lemma psiKW_zero (w : ℕ → ℝ) (R : ℕ) : ∀ (gs : List (ℝ → ℝ)), PsiKW w R gs 0 = nestedPhi gs 1
  | [] => by simp [PsiKW, Real.rpow_zero]
  | g :: gs => by
      simp only [PsiKW, Real.rpow_zero, Nat.floor_one, nestedLogSumW_cons]
      rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from rfl]
      simp only [Finset.sum_empty, zero_div]
      rw [nestedPhi_cons, show (1 : ℝ) - 1 = 0 from by ring, intervalIntegral.integral_same]

/-- **Generic factor step.** The level-`k+1` nested weighted sum, normalised by `(log R)^(k+1)`,
factors over the outer index into the `perturbed_riemann_gen` shape (`F·a·w`). -/
lemma nestedLogSumW_factor (w : ℕ → ℝ) (R : ℕ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) :
    nestedLogSumW w R (g :: gs) R / (Real.log R) ^ (gs.length + 1)
      = (∑ n ∈ Finset.Icc 2 R, g (Real.log n / Real.log R)
          * (nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length) * w n) / Real.log R := by
  rw [nestedLogSumW_cons]
  rw [show (∑ n ∈ Finset.Icc 2 R, g (Real.log n / Real.log R)
            * (nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length) * w n)
        = (∑ n ∈ Finset.Icc 2 R,
              g (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (R / n))
            / (Real.log R) ^ gs.length from by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun n _ => by ring)]
  rw [div_div, ← pow_succ]

/-- **Generic inductive cons step** (driven by `perturbed_riemann_gen`). Given the inner-uniform
convergence of the tail and the 1-D weighted limit `hW1D`, the level-`k` simplex limit holds. -/
theorem weighted_riemann_cons_of_inner_w (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hW1D : Weighted1DLimit w) (g : ℝ → ℝ) (gs : List (ℝ → ℝ))
    (hg : Continuous g) (hgs_cont : ∀ f ∈ gs, Continuous f)
    (huni : ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ n ∈ Finset.Icc 2 R,
        |nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length
          - nestedPhi gs (Real.log n / Real.log R)| ≤ ε) :
    Tendsto (fun R : ℕ => nestedLogSumW w R (g :: gs) R / (Real.log R) ^ (g :: gs).length)
      atTop (nhds (nestedPhi (g :: gs) 0)) := by
  have hΦcont : Continuous (nestedPhi gs) := nestedPhi_continuous gs hgs_cont
  have hlim : nestedPhi (g :: gs) 0 = ∫ x in (0 : ℝ)..1, g x * nestedPhi gs x := by
    rw [nestedPhi_cons]; simp only [sub_zero, zero_add]
  rw [hlim, List.length_cons, funext (fun R => nestedLogSumW_factor w R g gs)]
  refine perturbed_riemann_gen g (nestedPhi gs)
    (fun R n => nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length)
    (fun _ m => w m) (∫ x in (0 : ℝ)..1, |g x|) (fun R m _ => hw0 m) ?_ ?_
    (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)) huni
  · exact hW1D (fun x => g x * nestedPhi gs x) (hg.continuousOn.mul hΦcont.continuousOn)
  · exact hW1D (fun x => |g x|) hg.continuousOn.abs

/-- **Reparametrisation:** at `t = 1 - log n/log R`, `PsiKW` is the tail term of the factor lemma. -/
lemma psiKW_reparam (w : ℕ → ℝ) (R : ℕ) (gs : List (ℝ → ℝ)) (n : ℕ) (hR2 : 2 ≤ R) (hn1 : 1 ≤ n) :
    PsiKW w R gs (1 - Real.log n / Real.log R)
      = nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length := by
  unfold PsiKW
  rw [BoundedGaps.InnerUniformReduction.floor_rpow_one_sub R n hR2 hn1]

/-- **Generic inner-uniform from the pointwise scale-change** (Pólya). -/
theorem inner_uniform_kd_of_pointwise_w (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (gs : List (ℝ → ℝ))
    (hnn : ∀ g ∈ gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ gs, Continuous g)
    (hptw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun R : ℕ => PsiKW w R gs t) atTop (nhds (nestedPhi gs (1 - t)))) :
    ∀ ε > 0, ∀ᶠ R : ℕ in atTop, ∀ n ∈ Finset.Icc 2 R,
      |nestedLogSumW w R gs (R / n) / (Real.log R) ^ gs.length
        - nestedPhi gs (Real.log n / Real.log R)| ≤ ε := by
  have hΦcont : ContinuousOn (fun t => nestedPhi gs (1 - t)) (Set.Icc (0 : ℝ) 1) :=
    ((nestedPhi_continuous gs hcont).comp (continuous_const.sub continuous_id)).continuousOn
  have hpoly := BoundedGaps.PolyaUniform.polya_uniform
    (fun t => nestedPhi gs (1 - t)) (fun R => PsiKW w R gs) hΦcont
    (fun R => psiKW_monotoneOn w hw0 R gs hnn) hptw
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
  have hreparam := psiKW_reparam w R gs n hR2 hn1
  have hphi_eq : nestedPhi gs (1 - (1 - Real.log n / Real.log R))
      = nestedPhi gs (Real.log n / Real.log R) := by congr 1; ring
  have hb := hR (1 - Real.log n / Real.log R) htn_mem
  rw [hreparam, hphi_eq] at hb
  exact hb

/-- **Generic k-D simplex limit — modulo the pointwise heart `hpw`.** -/
theorem weighted_riemann_kd_of_pointwise_w (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hW1D : Weighted1DLimit w)
    (hpw : ∀ (gs : List (ℝ → ℝ)), (∀ g ∈ gs, ∀ x, 0 ≤ g x) → (∀ g ∈ gs, Continuous g) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Tendsto (fun R : ℕ => PsiKW w R gs t) atTop (nhds (nestedPhi gs (1 - t))))
    (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSumW w R Gs R / (Real.log R) ^ Gs.length)
      atTop (nhds (nestedPhi Gs 0)) := by
  cases Gs with
  | nil =>
      simp only [nestedLogSumW_nil, List.length_nil, pow_zero, div_one, nestedPhi_nil]
      exact tendsto_const_nhds
  | cons g gs =>
      have htail_nn : ∀ f ∈ gs, ∀ x, 0 ≤ f x := fun f hf => hnn f (List.mem_cons.mpr (Or.inr hf))
      have htail_cont : ∀ f ∈ gs, Continuous f :=
        fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf))
      refine weighted_riemann_cons_of_inner_w w hw0 hW1D g gs
        (hcont g (List.mem_cons.mpr (Or.inl rfl))) htail_cont ?_
      exact inner_uniform_kd_of_pointwise_w w hw0 gs htail_nn htail_cont
        (hpw gs htail_nn htail_cont)

/-! ### The generic pointwise scale-change `psi_k_pointwise_w` (the drift heart).

The bare `evalNest`/`harmNest` drift machinery ports with `/(n:ℝ) ↦ * w n` and `harmNest ↦
harmNestW w` (requiring `0 ≤ w n`). The strong-induction `psi_k_pointwise_w` is then identical in
shape to the bare proof, feeding the generic `k`-D limit back in at smaller list length. -/

/-- Generic nested weighted sum with effective log-base `L` and scale factor `c` (drift comparison
shape). Both `nestedLogSumW w R gs N` (base `R`) and `nestedLogSumW w N (t-scaled gs) N` (base `N`)
are instances at `L = log N`. -/
noncomputable def evalNestW (w : ℕ → ℝ) (L c : ℝ) : List (ℝ → ℝ) → ℕ → ℝ
  | [], _ => 1
  | g :: gs, Q =>
      ∑ n ∈ Finset.Icc 2 Q, g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n)

/-- The generic nested weighted-harmonic sum (all functions `≡ 1`): the drift bound's right factor. -/
noncomputable def harmNestW (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (k + 1), Q => ∑ n ∈ Finset.Icc 2 Q, w n * harmNestW w k (Q / n)

@[simp] lemma evalNestW_nil (w : ℕ → ℝ) (L c : ℝ) (Q : ℕ) : evalNestW w L c [] Q = 1 := rfl

@[simp] lemma evalNestW_cons (w : ℕ → ℝ) (L c : ℝ) (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (Q : ℕ) :
    evalNestW w L c (g :: gs) Q
      = ∑ n ∈ Finset.Icc 2 Q, g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n) := rfl

@[simp] lemma harmNestW_zero (w : ℕ → ℝ) (Q : ℕ) : harmNestW w 0 Q = 1 := rfl

@[simp] lemma harmNestW_succ (w : ℕ → ℝ) (k Q : ℕ) :
    harmNestW w (k + 1) Q = ∑ n ∈ Finset.Icc 2 Q, w n * harmNestW w k (Q / n) := rfl

/-- `harmNestW` is nonnegative for nonnegative weight. -/
lemma harmNestW_nonneg (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) : ∀ (k Q : ℕ), 0 ≤ harmNestW w k Q
  | 0, _ => by simp
  | (k + 1), Q => by
      rw [harmNestW_succ]
      exact Finset.sum_nonneg (fun n _ => mul_nonneg (hw0 n) (harmNestW_nonneg w hw0 k (Q / n)))

/-- **Bridge 1.** Effective base `L = log N`, scale `c = log N/log R`: `evalNestW` reproduces
`nestedLogSumW w R gs Q`. Needs `log N ≠ 0`. -/
lemma evalNestW_eq_nestedLogSumW_base (w : ℕ → ℝ) (R N : ℕ) (hN : Real.log (N : ℝ) ≠ 0) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      evalNestW w (Real.log (N : ℝ)) (Real.log (N : ℝ) / Real.log (R : ℝ)) gs Q
        = nestedLogSumW w R gs Q
  | [], _ => by simp
  | g :: gs, Q => by
      rw [evalNestW_cons, nestedLogSumW_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [evalNestW_eq_nestedLogSumW_base w R N hN gs (Q / n)]
      congr 3
      field_simp

/-- **Bridge 2.** Effective base `L = log N`, scale `c = t`: `evalNestW` reproduces the rescaled
sum `nestedLogSumW w N (gs.map (·∘(t*·))) Q`. -/
lemma evalNestW_eq_nestedLogSumW_scaled (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      evalNestW w (Real.log (N : ℝ)) t gs Q
        = nestedLogSumW w N (gs.map (fun g => fun u => g (t * u))) Q
  | [], _ => by simp
  | g :: gs, Q => by
      rw [evalNestW_cons, List.map_cons, nestedLogSumW_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [evalNestW_eq_nestedLogSumW_scaled w N t gs (Q / n)]

/-- `harmNestW w k Q = nestedLogSumW w N (replicate k 1) Q`. -/
lemma harmNestW_eq_nestedLogSumW (w : ℕ → ℝ) (N : ℕ) :
    ∀ (k Q : ℕ), harmNestW w k Q = nestedLogSumW w N (List.replicate k (fun _ : ℝ => (1 : ℝ))) Q
  | 0, _ => by simp
  | (k + 1), Q => by
      rw [harmNestW_succ, List.replicate_succ, nestedLogSumW_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [harmNestW_eq_nestedLogSumW w N k (Q / n)]
      show w n * nestedLogSumW w N (List.replicate k (fun _ : ℝ => (1 : ℝ))) (Q / n)
        = (1 : ℝ) * w n * nestedLogSumW w N (List.replicate k (fun _ : ℝ => (1 : ℝ))) (Q / n)
      ring

/-- **Sup bound for `evalNestW`.** If each `g ∈ gs` satisfies `|g (c·u)| ≤ M` on `[0,1]` and the
log-ratios stay `≤ 1`, then `|evalNestW L c gs Q| ≤ (max M 1)^|gs| · harmNestW |gs| Q`. -/
lemma evalNestW_abs_le (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (L : ℝ) (hL : 0 < L) (c M : ℝ) (hM : 0 ≤ M) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u)| ≤ M) →
      (∀ m : ℕ, m ≤ Q → Real.log (m : ℝ) ≤ L) →
      |evalNestW w L c gs Q| ≤ (max M 1) ^ gs.length * harmNestW w gs.length Q
  | [], Q, _, _ => by simp
  | g :: gs, Q, hbd, hQL => by
      set K := max M 1 with hKdef
      have hMK : M ≤ K := le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
      have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      rw [evalNestW_cons]
      calc |∑ n ∈ Finset.Icc 2 Q,
                g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n)|
          ≤ ∑ n ∈ Finset.Icc 2 Q,
                |g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 2 Q,
                K ^ (g :: gs).length * (w n * harmNestW w gs.length (Q / n)) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            obtain ⟨hn2, hnQ⟩ := Finset.mem_Icc.mp hn
            have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
            have hu0 : 0 ≤ Real.log (n : ℝ) / L := div_nonneg hlogn0 hL.le
            have hu1 : Real.log (n : ℝ) / L ≤ 1 := by
              rw [div_le_one hL]; exact hQL n hnQ
            have hgbd : |g (c * (Real.log n / L))| ≤ M :=
              hbd g (List.mem_cons.mpr (Or.inl rfl)) _ hu0 hu1
            have hQL' : ∀ m : ℕ, m ≤ Q / n → Real.log (m : ℝ) ≤ L :=
              fun m hm => hQL m (le_trans hm (Nat.div_le_self Q n))
            have hIH := evalNestW_abs_le w hw0 L hL c M hM gs (Q / n)
              (fun f hf => hbd f (List.mem_cons.mpr (Or.inr hf))) hQL'
            have hharm0 : 0 ≤ harmNestW w gs.length (Q / n) := harmNestW_nonneg w hw0 _ _
            have hKgs0 : 0 ≤ K ^ gs.length := pow_nonneg hK0 _
            rw [abs_mul, abs_mul, abs_of_nonneg (hw0 n)]
            calc |g (c * (Real.log n / L))| * w n * |evalNestW w L c gs (Q / n)|
                ≤ M * w n * (K ^ gs.length * harmNestW w gs.length (Q / n)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right hgbd (hw0 n)) hIH (abs_nonneg _)
                    (mul_nonneg hM (hw0 n))
              _ ≤ K ^ (g :: gs).length * (w n * harmNestW w gs.length (Q / n)) := by
                  rw [List.length_cons, pow_succ]
                  rw [show M * w n * (K ^ gs.length * harmNestW w gs.length (Q / n))
                        = M * (K ^ gs.length * harmNestW w gs.length (Q / n)) * w n from by ring,
                      show K ^ gs.length * K * (w n * harmNestW w gs.length (Q / n))
                        = K * (K ^ gs.length * harmNestW w gs.length (Q / n)) * w n from by ring]
                  apply mul_le_mul_of_nonneg_right _ (hw0 n)
                  exact mul_le_mul_of_nonneg_right hMK (by positivity)
        _ = K ^ (g :: gs).length * ∑ n ∈ Finset.Icc 2 Q,
                (w n * harmNestW w gs.length (Q / n)) := by rw [Finset.mul_sum]
        _ = K ^ (g :: gs).length * harmNestW w (g :: gs).length Q := by
            rw [List.length_cons, harmNestW_succ]

/-- **Drift bound for `evalNestW`.** If each `g ∈ gs` is bounded by `M` under both scales `c, c'` and
the two scaled evaluations differ by `≤ ε` on `[0,1]`, the nested sums differ by `≤ |gs| · (max M
1)^|gs| · ε · harmNestW |gs| Q`. The generic heart of `psi_k_pointwise_w`. -/
lemma evalNestW_dist (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (L : ℝ) (hL : 0 < L) (c c' M ε : ℝ)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u)| ≤ M) →
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c' * u)| ≤ M) →
      (∀ g ∈ gs, ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |g (c * u) - g (c' * u)| ≤ ε) →
      (∀ m : ℕ, m ≤ Q → Real.log (m : ℝ) ≤ L) →
      |evalNestW w L c gs Q - evalNestW w L c' gs Q|
        ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * ε * harmNestW w gs.length Q
  | [], Q, _, _, _, _ => by simp
  | g :: gs, Q, hbd, hbd', hclose, hQL => by
      set K := max M 1 with hKdef
      have hMK : M ≤ K := le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
      have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      rw [evalNestW_cons, evalNestW_cons, ← Finset.sum_sub_distrib]
      calc |∑ n ∈ Finset.Icc 2 Q,
                (g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n)
                  - g (c' * (Real.log n / L)) * w n * evalNestW w L c' gs (Q / n))|
          ≤ ∑ n ∈ Finset.Icc 2 Q,
                |g (c * (Real.log n / L)) * w n * evalNestW w L c gs (Q / n)
                  - g (c' * (Real.log n / L)) * w n * evalNestW w L c' gs (Q / n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 2 Q,
                (((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε)
                  * (w n * harmNestW w gs.length (Q / n)) := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            obtain ⟨hn2, hnQ⟩ := Finset.mem_Icc.mp hn
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
            have hAB := evalNestW_dist w hw0 L hL c c' M ε hM hε gs (Q / n)
              (fun f hf => hbd f (List.mem_cons.mpr (Or.inr hf)))
              (fun f hf => hbd' f (List.mem_cons.mpr (Or.inr hf)))
              (fun f hf => hclose f (List.mem_cons.mpr (Or.inr hf))) hQL'
            have hB := evalNestW_abs_le w hw0 L hL c' M hM gs (Q / n)
              (fun f hf => hbd' f (List.mem_cons.mpr (Or.inr hf))) hQL'
            set A := evalNestW w L c gs (Q / n) with hAdef
            set B := evalNestW w L c' gs (Q / n) with hBdef
            set hh := harmNestW w gs.length (Q / n) with hhdef
            have hh0 : 0 ≤ hh := harmNestW_nonneg w hw0 _ _
            have hKgs0 : 0 ≤ K ^ gs.length := pow_nonneg hK0 _
            have hg0 : (0 : ℝ) ≤ (gs.length : ℝ) := Nat.cast_nonneg _
            rw [show g (c * (Real.log n / L)) * w n * A
                    - g (c' * (Real.log n / L)) * w n * B
                  = w n
                      * (g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B) from by ring,
                abs_mul, abs_of_nonneg (hw0 n)]
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
            have hbase : (0 : ℝ) ≤ w n * hh * K ^ gs.length * ε :=
              mul_nonneg (mul_nonneg (mul_nonneg (hw0 n) hh0) hKgs0) hε
            have hscalar : (gs.length : ℝ) * M + 1 ≤ ((gs.length : ℝ) + 1) * K := by
              nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hMK), hK1]
            calc w n * |g (c * (Real.log n / L)) * A - g (c' * (Real.log n / L)) * B|
                ≤ w n
                    * (M * ((gs.length : ℝ) * K ^ gs.length * ε * hh) + ε * (K ^ gs.length * hh)) :=
                  mul_le_mul_of_nonneg_left hbound (hw0 n)
              _ = (w n * hh * K ^ gs.length * ε) * ((gs.length : ℝ) * M + 1) := by ring
              _ ≤ (w n * hh * K ^ gs.length * ε) * (((gs.length : ℝ) + 1) * K) :=
                  mul_le_mul_of_nonneg_left hscalar hbase
              _ = ((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε
                    * (w n * hh) := by ring
        _ = (((gs.length : ℝ) + 1) * (K ^ gs.length * K) * ε)
              * ∑ n ∈ Finset.Icc 2 Q, (w n * harmNestW w gs.length (Q / n)) := by
            rw [Finset.mul_sum]
        _ = ((g :: gs).length : ℝ) * K ^ (g :: gs).length * ε * harmNestW w (g :: gs).length Q := by
            rw [List.length_cons, harmNestW_succ, pow_succ]; push_cast; ring

open BoundedGaps.InnerUniformReduction (tendsto_logFloor_rpow_div) in
/-- **Generic pointwise scale-change** (the generic `psi_k_pointwise`), modulo the full generic `k`-D
limit for same-length lists (`hkd`). For `t ∈ [0,1]` and nonnegative continuous `gs`,
`PsiKW w R gs t → nestedPhi gs (1-t)`. Strong-induction-ready (mirrors the bare proof; the drift uses
`evalNestW_dist`, `harmNestW` and the change-of-variables `nestedPhi_scale`). -/
theorem psi_k_pointwise_w (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (gs : List (ℝ → ℝ))
    (hnn : ∀ g ∈ gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ gs, Continuous g)
    (hkd : ∀ (hs : List (ℝ → ℝ)), hs.length = gs.length → (∀ g ∈ hs, ∀ x, 0 ≤ g x) →
        (∀ g ∈ hs, Continuous g) →
        Tendsto (fun R : ℕ => nestedLogSumW w R hs R / (Real.log R) ^ hs.length) atTop
          (nhds (nestedPhi hs 0)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => PsiKW w R gs t) atTop (nhds (nestedPhi gs (1 - t))) := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with hteq | htpos
  · rw [← hteq]
    simp only [psiKW_zero, sub_zero]
    exact tendsto_const_nhds
  · set gss : List (ℝ → ℝ) := gs.map (fun g => fun u => g (t * u)) with hgss
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
    have hB : Tendsto (fun R : ℕ =>
        nestedLogSumW w (N R) gss (N R) / (Real.log (N R : ℝ)) ^ gs.length) atTop
        (𝓝 (nestedPhi gss 0)) := by
      have hlim := hkd gss hgss_len hgss_nn hgss_cont
      rw [hgss_len] at hlim
      exact hlim.comp hNtop
    obtain ⟨M, hM0, hM⟩ := exists_list_bound gs hcont
    obtain ⟨C, hC0, hharm⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
        harmNestW w gs.length (N R) / (Real.log (N R : ℝ)) ^ gs.length ≤ C := by
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
      rw [Real.dist_eq, ← harmNestW_eq_nestedLogSumW w (N R) gs.length (N R)] at hR
      have h2 := (abs_lt.1 hR).2
      have h3 := le_abs_self (nestedPhi (List.replicate gs.length (fun _ : ℝ => (1 : ℝ))) 0)
      linarith
    have hdrift : Tendsto (fun R : ℕ =>
        (nestedLogSumW w R gs (N R) - nestedLogSumW w (N R) gss (N R))
          / (Real.log (N R : ℝ)) ^ gs.length)
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
      have hdist := evalNestW_dist w hw0 (Real.log (N R : ℝ)) hlogNpos cR t M εpp hM0 hεpp0.le gs (N R)
        hbdc hbdt hclose hQL
      have hDeq : nestedLogSumW w R gs (N R) - nestedLogSumW w (N R) gss (N R)
          = evalNestW w (Real.log (N R : ℝ)) cR gs (N R)
            - evalNestW w (Real.log (N R : ℝ)) t gs (N R) := by
        rw [hcRdef, evalNestW_eq_nestedLogSumW_base w R (N R) hlogNne gs (N R),
            evalNestW_eq_nestedLogSumW_scaled w (N R) t gs (N R)]
      rw [← hDeq] at hdist
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogNpos gs.length)]
      have hlogNk : (0 : ℝ) < (Real.log (N R : ℝ)) ^ gs.length := pow_pos hlogNpos gs.length
      have hpre0 : 0 ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * εpp :=
        mul_nonneg (mul_nonneg hkn hKp0.le) hεpp0.le
      calc |nestedLogSumW w R gs (N R) - nestedLogSumW w (N R) gss (N R)|
              / (Real.log (N R : ℝ)) ^ gs.length
          ≤ ((gs.length : ℝ) * (max M 1) ^ gs.length * εpp * harmNestW w gs.length (N R))
              / (Real.log (N R : ℝ)) ^ gs.length := by
            apply div_le_div_of_nonneg_right hdist hlogNk.le
        _ = (gs.length : ℝ) * (max M 1) ^ gs.length * εpp
              * (harmNestW w gs.length (N R) / (Real.log (N R : ℝ)) ^ gs.length) := by ring
        _ ≤ (gs.length : ℝ) * (max M 1) ^ gs.length * εpp * C :=
            mul_le_mul_of_nonneg_left hharmR hpre0
        _ = (gs.length : ℝ) * (max M 1) ^ gs.length * C * εpp := by ring
        _ < ε := hεppfin
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
        * (nestedLogSumW w (N R) gss (N R) / (Real.log (N R : ℝ)) ^ gs.length
           + (nestedLogSumW w R gs (N R) - nestedLogSumW w (N R) gss (N R))
             / (Real.log (N R : ℝ)) ^ gs.length)
      = nestedLogSumW w R gs (N R) / (Real.log (R : ℝ)) ^ gs.length
    rw [div_pow]
    field_simp
    ring

/-- **The unconditional generic-weight `k`-D Riemann limit** (strong induction on list length). -/
theorem weighted_riemann_kd_w_aux (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hW1D : Weighted1DLimit w) :
    ∀ (n : ℕ) (Gs : List (ℝ → ℝ)), Gs.length = n →
    (∀ g ∈ Gs, ∀ x, 0 ≤ g x) → (∀ g ∈ Gs, Continuous g) →
    Tendsto (fun R : ℕ => nestedLogSumW w R Gs R / (Real.log R) ^ Gs.length) atTop
      (nhds (nestedPhi Gs 0)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Gs hlen hnn hcont
    cases Gs with
    | nil =>
        simp only [nestedLogSumW_nil, List.length_nil, pow_zero, div_one, nestedPhi_nil]
        exact tendsto_const_nhds
    | cons g gs =>
        have htail_nn : ∀ f ∈ gs, ∀ x, 0 ≤ f x :=
          fun f hf => hnn f (List.mem_cons.mpr (Or.inr hf))
        have htail_cont : ∀ f ∈ gs, Continuous f :=
          fun f hf => hcont f (List.mem_cons.mpr (Or.inr hf))
        have hgslt : gs.length < n := by rw [← hlen, List.length_cons]; omega
        have hkd_gs : ∀ (hs : List (ℝ → ℝ)), hs.length = gs.length → (∀ g ∈ hs, ∀ x, 0 ≤ g x) →
            (∀ g ∈ hs, Continuous g) →
            Tendsto (fun R : ℕ => nestedLogSumW w R hs R / (Real.log R) ^ hs.length) atTop
              (nhds (nestedPhi hs 0)) :=
          fun hs hhs hnn' hcont' => IH gs.length hgslt hs hhs hnn' hcont'
        refine weighted_riemann_cons_of_inner_w w hw0 hW1D g gs
          (hcont g (List.mem_cons.mpr (Or.inl rfl))) htail_cont ?_
        exact inner_uniform_kd_of_pointwise_w w hw0 gs htail_nn htail_cont
          (fun t ht => psi_k_pointwise_w w hw0 gs htail_nn htail_cont hkd_gs t ht)

/-- **Generic-weight `k`-D Riemann limit** (the headline). For any nonnegative weight `w` satisfying
the 1-D weighted limit `Weighted1DLimit w`, and every nonnegative continuous list `Gs`,
`nestedLogSumW w R Gs R / (log R)^|Gs| → nestedPhi Gs 0 = ∫_{simplex} ∏ Gs`. -/
theorem weighted_riemann_kd_w (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hW1D : Weighted1DLimit w)
    (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x) (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSumW w R Gs R / (Real.log R) ^ Gs.length) atTop
      (nhds (nestedPhi Gs 0)) :=
  weighted_riemann_kd_w_aux w hw0 hW1D Gs.length Gs rfl hnn hcont

/-- **Generic-weight `k`-D Riemann limit with a relaxed head** (the outer function needs only
continuity; the inner `gs` need nonnegativity for Pólya). -/
theorem weighted_riemann_kd_w_head (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hW1D : Weighted1DLimit w)
    (g : ℝ → ℝ) (gs : List (ℝ → ℝ)) (hg : Continuous g) (hgs_nn : ∀ f ∈ gs, ∀ x, 0 ≤ f x)
    (hgs_cont : ∀ f ∈ gs, Continuous f) :
    Tendsto (fun R : ℕ => nestedLogSumW w R (g :: gs) R / (Real.log R) ^ (g :: gs).length) atTop
      (nhds (nestedPhi (g :: gs) 0)) := by
  refine weighted_riemann_cons_of_inner_w w hw0 hW1D g gs hg hgs_cont ?_
  exact inner_uniform_kd_of_pointwise_w w hw0 gs hgs_nn hgs_cont
    (fun t ht => psi_k_pointwise_w w hw0 gs hgs_nn hgs_cont
      (fun hs _ hnn' hcont' => weighted_riemann_kd_w w hw0 hW1D hs hnn' hcont') t ht)

/-! ### Instantiation: the `(μ²/φ)` `y_r`-space ladder.

The GPY/Maynard leaf-1 (`s1`, Path Y) `y_r`-space main term is exactly the generic ladder at the
weight `w = gMoebiusSqTotient = μ²/φ`. The two instance obligations — nonnegativity and the 1-D
weighted limit — are discharged: nonnegativity from `gMoebiusSqTotient_apply`, and the 1-D limit
(continuous form, weight-on-the-right, over `Icc 2`) from `WeightedMertens.weighted_mertens_continuous`
by dropping the `n=1` term and commuting. -/

open BoundedGaps.WeightedMertens BoundedGaps.SingularSeries in
/-- `μ²/φ ≥ 0`. -/
lemma gMoebiusSqTotient_nonneg (n : ℕ) : 0 ≤ gMoebiusSqTotient n := by
  rw [gMoebiusSqTotient_apply]; positivity

open BoundedGaps.WeightedMertens BoundedGaps.SingularSeries in
/-- **The `μ²/φ` weight satisfies `Weighted1DLimit`** (continuous form). For every continuous `G` on
`[0,1]`, `(∑_{2≤m≤N} G(log m/log N)·(μ²/φ)(m))/log N → ∫₀¹ G`. Built from
`weighted_mertens_continuous` (`Icc 1`, weight-on-left) by dropping the `n=1` term (`= G 0`, whose
`/log N → 0`) and commuting the product. -/
theorem weighted1DLimit_muphi : Weighted1DLimit (fun n => gMoebiusSqTotient n) := by
  intro G hG
  have hwm := weighted_mertens_continuous (F := G) hG
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => G 0 / Real.log N) atTop (nhds 0) :=
    (tendsto_const_nhds (x := G 0)).div_atTop hlog
  have hcomb := hwm.sub hconst
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hins : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : gMoebiusSqTotient 1 * G (Real.log ((1 : ℕ) : ℝ) / Real.log N) = G 0 := by
    rw [gMoebiusSqTotient_apply]; simp
  have hcomm : (∑ m ∈ Finset.Icc 2 N, gMoebiusSqTotient m * G (Real.log m / Real.log N))
      = ∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) * gMoebiusSqTotient m :=
    Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  rw [hins, Finset.sum_insert (by simp), h1, hcomm]
  ring

open BoundedGaps.SingularSeries in
/-- **`(μ²/φ)` `y_r`-space `k`-D Riemann limit** (GPY/Maynard leaf-1, Path Y). For every nonnegative
continuous list `Gs`, the fully-coupled simplex sum with the `μ²/φ` weight converges to the iterated
simplex integral:
`(∑_{∏ rᵢ ≤ R} ∏ Gs_i(log rᵢ/log R) · ∏ (μ²/φ)(rᵢ)) / (log R)^|Gs| → ∫_{simplex} ∏ Gs`.
The unconditional `μ²/φ` analog of `WeightedRiemannKD.weighted_riemann_kd`, obtained as the generic
ladder `weighted_riemann_kd_w` at `w = gMoebiusSqTotient`. -/
theorem weighted_riemann_kd_muphi (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x)
    (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSumW (fun n => gMoebiusSqTotient n) R Gs R / (Real.log R) ^ Gs.length)
      atTop (nhds (nestedPhi Gs 0)) :=
  weighted_riemann_kd_w (fun n => gMoebiusSqTotient n) gMoebiusSqTotient_nonneg
    weighted1DLimit_muphi Gs hnn hcont

open BoundedGaps.SingularSeries in
/-- **Separable `(μ²/φ)` `y_r`-space main term** (the GPY/Maynard `s1` diagonal constant, Path Y).
For continuous coordinate functions `Fs : Fin k → ℝ → ℝ`, the fully-coupled simplex sum of the
**squared** weights converges to the iterated simplex integral of `∏ᵢ (Fs i)²`:
`(∑_{∏rᵢ≤R} ∏ᵢ (μ²/φ)(rᵢ)·Fs i (log rᵢ/log R)²) / (log R)^k → nestedPhi [Fs₀²,…] 0`.
For a separable cutoff `F t = ∏ᵢ Fs i (t i)`, the limit `nestedPhi (ofFn Fs²) 0 = ∫_{simplex} ∏ᵢ Fs
i² = ∫_{simplex} F² = mkF_denominator k F` (the last equality is the simplex-Fubini bridge
`∫_{simplex k} ∏ gᵢ = nestedPhi (ofFn g) 0`, the next connection step). This is the exact analytic
input `s1_holds_from_nonprime_asym` needs in `y_r`-space. -/
theorem weighted_riemann_kd_muphi_sep (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (hcont : ∀ i, Continuous (Fs i)) :
    Tendsto (fun R : ℕ =>
        nestedLogSumW (fun n => gMoebiusSqTotient n) R
            (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)) R
          / (Real.log R) ^ k)
      atTop (nhds (nestedPhi (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)) 0)) := by
  have hlen : (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)).length = k := List.length_ofFn
  have hnn : ∀ g ∈ List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2), ∀ x, 0 ≤ g x := by
    intro g hg x
    rw [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact sq_nonneg _
  have hgcont : ∀ g ∈ List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2), Continuous g := by
    intro g hg
    rw [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact (hcont i).pow 2
  have h := weighted_riemann_kd_muphi (List.ofFn (fun i : Fin k => fun x => (Fs i x) ^ 2)) hnn hgcont
  rw [hlen] at h
  exact h

/-! ### Validation: the bare `1/n` ladder is the generic ladder at `w = 1/n`.

Recovering `WeightedRiemannKD.weighted_riemann_kd` as the instance `w n = 1/n` is kernel-checked
evidence that the generic ladder is correct: the two `nestedLogSum` shapes agree
(`nestedLogSumW_harmonic_eq`), the bare 1-D Riemann limit gives `Weighted1DLimit (1/·)`, and the
resulting limit statement is *identical* to the established bare theorem. -/

/-- The `1/n` weight satisfies `Weighted1DLimit` (via the bare `riemann_sum_log_weight`). -/
theorem weighted1DLimit_harmonic : Weighted1DLimit (fun n => 1 / (n : ℝ)) := by
  intro G hG
  have h := BoundedGaps.WeightedMertens.riemann_sum_log_weight G hG
  have heq : (fun N : ℕ =>
        (∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) * (1 / (m : ℝ))) / Real.log N)
      = (fun N : ℕ =>
        (∑ m ∈ Finset.Icc 2 N, G (Real.log m / Real.log N) / (m : ℝ)) / Real.log N) := by
    funext N; congr 1
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_one_div])
  rw [heq]; exact h

/-- The generic `nestedLogSumW` at `w = 1/n` is the bare `nestedLogSum`. -/
lemma nestedLogSumW_harmonic_eq (R : ℕ) :
    ∀ (gs : List (ℝ → ℝ)) (Q : ℕ),
      nestedLogSumW (fun n => 1 / (n : ℝ)) R gs Q = nestedLogSum R gs Q
  | [], _ => rfl
  | g :: gs, Q => by
      rw [nestedLogSumW_cons, nestedLogSum_cons]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [nestedLogSumW_harmonic_eq R gs (Q / n)]; ring

/-- **Bare `k`-D Riemann limit recovered from the generic ladder** (identical statement to
`WeightedRiemannKD.weighted_riemann_kd`). -/
theorem weighted_riemann_kd_harmonic (Gs : List (ℝ → ℝ)) (hnn : ∀ g ∈ Gs, ∀ x, 0 ≤ g x)
    (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ => nestedLogSum R Gs R / (Real.log R) ^ Gs.length) atTop
      (nhds (nestedPhi Gs 0)) := by
  have h := weighted_riemann_kd_w (fun n => 1 / (n : ℝ)) (fun n => by positivity)
    weighted1DLimit_harmonic Gs hnn hcont
  simpa only [nestedLogSumW_harmonic_eq] using h

end BoundedGaps.WeightedRiemannGen
