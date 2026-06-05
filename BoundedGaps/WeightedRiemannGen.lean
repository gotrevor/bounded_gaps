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

end BoundedGaps.WeightedRiemannGen
