import BoundedGaps.SievePolynomial
import BoundedGaps.WeightedRiemannKD

/-!
# The simplex-Fubini bridge: `∫_{simplex k} ∏ᵢ gᵢ = nestedPhi (ofFn g) 0`

This file closes the **only remaining analytic gap** in the GPY/Maynard `s1` Path-Y main term:
the identity

  `∫_{simplex k} ∏ᵢ gᵢ(tᵢ) = nestedPhi (List.ofFn g) 0`     (`simplex_integral_prod_eq_nestedPhi`)

for continuous `g : Fin k → ℝ → ℝ`. It is the precise hypothesis `hFubini` taken on faith in
`S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep`; landing it discharges that hypothesis and
proves the k-D `s1` analytic main term end-to-end.

## The order-swap

`nestedPhi` / `simplexPhi` (`WeightedRiemannKD`) are **head-recursive**: they peel the integrated
coordinate as the *outer* integral. The repo's `SievePolynomial.simplex_fubini` peels a coordinate
with that coordinate *inner* (the rest of the simplex outer). Bridging the two is a genuine Fubini
order-swap. We avoid re-deriving `simplex_fubini` in indicator form by instead proving a **head-outer**
fibration `simplex_scaled_fubini_head` directly from `integral_insertNth_eq'` (the `integral_prod`
sibling of `Sieve.integral_insertNth_eq`), over the **budget simplex** `simplex_scaled k a`
(`= {t | (∀i, 0 ≤ tᵢ) ∧ ∑ tᵢ ≤ a}`, already in `Sieve.lean`). The budget recursion exactly matches
`simplexPhi`'s, so the connection is a clean induction with no leftover swap.

The chain:
* `simplex_scaled_fubini_head` — peel coordinate `0` *outer*: `∫_{simplex_scaled (n+1) a} G
  = ∫_{ti∈[0,a]} ∫_{simplex_scaled n (a-ti)} G(insertNth 0 ti ·)`.
* `simplexInt` — the budget-form iterated integral (head-recursive, `Fin k → ℝ → ℝ` shaped).
* `simplex_scaled_integral_prod_eq_simplexInt` — `∫_{simplex_scaled k a} ∏ gᵢ = simplexInt k g a`
  (induction on `k`, peeling with `simplex_scaled_fubini_head`).
* `simplexInt_eq_simplexPhi_ofFn` — `simplexInt k g a = simplexPhi (ofFn g) a` (structural).
* `simplex_integral_prod_eq_nestedPhi` — specialise to `a = 1` (`simplex = simplex_scaled · 1`) and
  use `nestedPhi_eq_simplexPhi` at budget `1`.
-/

open MeasureTheory
open scoped BigOperators

namespace BoundedGaps.S1Fubini

/-! ## Topology of the budget simplex `simplex_scaled k a` -/

/-- The budget simplex is closed (intersection of closed half-spaces). -/
theorem isClosed_simplex_scaled (k : ℕ) (r : ℝ) : IsClosed (Sieve.simplex_scaled k r) := by
  have heq : Sieve.simplex_scaled k r =
      (⋂ i : Fin k, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t | ∑ i, t i ≤ r} := by
    ext t; simp only [Sieve.simplex_scaled, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
  · exact isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const

/-- For a nonneg budget `r ≥ 0`, the budget simplex is compact (closed and bounded by `r`). -/
theorem isCompact_simplex_scaled (k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    IsCompact (Sieve.simplex_scaled k r) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_simplex_scaled k r
  · apply (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := r)).subset
    intro t ht
    simp only [Sieve.simplex_scaled, Set.mem_setOf_eq] at ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg hr]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    calc t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)
      _ ≤ r := ht.2

/-- Membership of an `insertNth 0` in the budget simplex factors through the reduced budget:
`insertNth 0 ti s ∈ simplex_scaled (n+1) a ↔ (0 ≤ ti ∧ s ∈ simplex_scaled n (a - ti))`. -/
lemma insertNth_zero_mem_simplex_scaled {n : ℕ} (ti a : ℝ) (s : Fin n → ℝ) :
    (0 : Fin (n + 1)).insertNth ti s ∈ Sieve.simplex_scaled (n + 1) a
      ↔ (0 ≤ ti ∧ s ∈ Sieve.simplex_scaled n (a - ti)) := by
  simp only [Sieve.simplex_scaled, Set.mem_setOf_eq, SievePolynomial.insertNth_sum]
  constructor
  · rintro ⟨hnn, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · have := hnn 0; rwa [Fin.insertNth_apply_same] at this
    · intro j
      have h := hnn ((0 : Fin (n + 1)).succAbove j)
      rwa [Fin.insertNth_apply_succAbove] at h
    · linarith
  · rintro ⟨h0, hnn, hsum⟩
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hj : j = 0
      · subst hj; rwa [Fin.insertNth_apply_same]
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Fin.insertNth_apply_succAbove]; exact hnn j'
    · linarith

/-! ## Head-outer fibration -/

/-- The `integral_prod` (head-outer) sibling of `Sieve.integral_insertNth_eq`. -/
theorem integral_insertNth_eq' {n : ℕ} (i : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ)
    (hG : Integrable G) :
    (∫ t, G t) = ∫ ti : ℝ, ∫ s : Fin n → ℝ, G (i.insertNth ti s) := by
  have mp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hint : Integrable
      (fun p : ℝ × (Fin n → ℝ) =>
        G ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm p))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact mp.symm.integrable_comp_of_integrable hG
  rw [← mp.symm.integral_comp' G, Measure.volume_eq_prod ℝ (Fin n → ℝ),
      integral_prod _ hint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]

/-- **Head-outer simplex fibration.** Peel coordinate `0` of a budget-simplex integral, integrating
that coordinate as the *outer* variable: `∫_{simplex_scaled (n+1) a} G
= ∫_{ti∈[0,a]} ∫_{simplex_scaled n (a-ti)} G(insertNth 0 ti ·)`. The budget of the inner simplex
shrinks by `ti`. This is the order-swap matching `simplexPhi`'s head recursion. -/
theorem simplex_scaled_fubini_head {n : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (G : (Fin (n + 1) → ℝ) → ℝ) (hG : Continuous G) :
    (∫ t in Sieve.simplex_scaled (n + 1) a, G t)
      = ∫ ti in Set.Icc (0:ℝ) a,
          ∫ s in Sieve.simplex_scaled n (a - ti), G ((0 : Fin (n + 1)).insertNth ti s) := by
  classical
  have hSmeas : MeasurableSet (Sieve.simplex_scaled (n + 1) a) :=
    (isClosed_simplex_scaled (n + 1) a).measurableSet
  have hIntOn : IntegrableOn G (Sieve.simplex_scaled (n + 1) a) :=
    hG.continuousOn.integrableOn_compact (isCompact_simplex_scaled (n + 1) a ha)
  have hint : Integrable ((Sieve.simplex_scaled (n + 1) a).indicator G) :=
    hIntOn.integrable_indicator hSmeas
  rw [← MeasureTheory.integral_indicator hSmeas,
      integral_insertNth_eq' (0 : Fin (n + 1)) _ hint]
  have hinner : ∀ ti : ℝ,
      (∫ s, (Sieve.simplex_scaled (n + 1) a).indicator G ((0 : Fin (n + 1)).insertNth ti s))
        = (Set.Icc (0:ℝ) a).indicator
            (fun ti => ∫ s in Sieve.simplex_scaled n (a - ti),
              G ((0 : Fin (n + 1)).insertNth ti s)) ti := by
    intro ti
    by_cases hti : ti ∈ Set.Icc (0:ℝ) a
    · rw [Set.indicator_of_mem hti]
      have hfun : (fun s => (Sieve.simplex_scaled (n + 1) a).indicator G
              ((0 : Fin (n + 1)).insertNth ti s))
          = (Sieve.simplex_scaled n (a - ti)).indicator
              (fun s => G ((0 : Fin (n + 1)).insertNth ti s)) := by
        funext s
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hs : s ∈ Sieve.simplex_scaled n (a - ti)
        · rw [if_pos ((insertNth_zero_mem_simplex_scaled ti a s).mpr ⟨hti.1, hs⟩), if_pos hs]
        · rw [if_neg (fun hm => hs ((insertNth_zero_mem_simplex_scaled ti a s).mp hm).2),
              if_neg hs]
      rw [hfun, MeasureTheory.integral_indicator (isClosed_simplex_scaled n (a - ti)).measurableSet]
    · rw [Set.indicator_of_notMem hti]
      have hz : ∀ s, (Sieve.simplex_scaled (n + 1) a).indicator G
          ((0 : Fin (n + 1)).insertNth ti s) = 0 := by
        intro s
        rw [Set.indicator_apply, if_neg]
        intro hm
        obtain ⟨h0, hsmem⟩ := (insertNth_zero_mem_simplex_scaled ti a s).mp hm
        have hsum0 : (0:ℝ) ≤ ∑ j, s j := Finset.sum_nonneg (fun j _ => hsmem.1 j)
        exact hti ⟨h0, by have := hsmem.2; linarith⟩
      simp only [hz, integral_zero]
  simp_rw [hinner]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-! ## Budget-form iterated integral and the bridge -/

/-- The budget-form iterated simplex integral, `Fin k → ℝ → ℝ` shaped and head-recursive. By
construction `simplexInt k g a = simplexPhi (ofFn g) a`. -/
noncomputable def simplexInt : (k : ℕ) → (Fin k → ℝ → ℝ) → ℝ → ℝ
  | 0, _, _ => 1
  | (k + 1), g, a => ∫ y in (0:ℝ)..a, g 0 y * simplexInt k (fun j => g j.succ) (a - y)

/-- **The budget simplex integral of a product is the iterated integral.** Induction on `k`,
peeling coordinate `0` outer via `simplex_scaled_fubini_head`. -/
theorem simplex_scaled_integral_prod_eq_simplexInt :
    ∀ (k : ℕ) (g : Fin k → ℝ → ℝ), (∀ i, Continuous (g i)) → ∀ (a : ℝ), 0 ≤ a →
      (∫ t in Sieve.simplex_scaled k a, ∏ i, g i (t i)) = simplexInt k g a
  | 0, g, _, a, ha => by
      have hsimp0 : Sieve.simplex_scaled 0 a = (Set.univ : Set (Fin 0 → ℝ)) := by
        ext t; simp [Sieve.simplex_scaled, ha]
      rw [hsimp0, Measure.restrict_univ, MeasureTheory.integral_unique]
      have hvol : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [measureReal_def, MeasureTheory.volume_pi]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, smul_eq_mul, hvol, one_mul]
      rfl
  | (k + 1), g, hg, a, ha => by
      have hGcont : Continuous (fun t : Fin (k + 1) → ℝ => ∏ i, g i (t i)) :=
        continuous_finset_prod Finset.univ (fun i _ => (hg i).comp (continuous_apply i))
      rw [simplex_scaled_fubini_head a ha (fun t => ∏ i, g i (t i)) hGcont]
      have hrhs : simplexInt (k + 1) g a
          = ∫ ti in Set.Icc (0:ℝ) a, g 0 ti * simplexInt k (fun j => g j.succ) (a - ti) := by
        rw [simplexInt, intervalIntegral.integral_of_le ha,
            ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [hrhs]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun ti hti => ?_)
      have hage : 0 ≤ a - ti := by have := hti.2; linarith
      have hprodeq : ∀ s : Fin k → ℝ,
          (fun t : Fin (k + 1) → ℝ => ∏ i, g i (t i)) ((0 : Fin (k + 1)).insertNth ti s)
            = g 0 ti * ∏ j, g j.succ (s j) := by
        intro s
        dsimp only
        rw [Fin.prod_univ_succ, Fin.insertNth_apply_same]
        congr 1
      rw [MeasureTheory.setIntegral_congr_fun (isClosed_simplex_scaled k (a - ti)).measurableSet
            (fun s _ => hprodeq s),
          MeasureTheory.integral_const_mul,
          simplex_scaled_integral_prod_eq_simplexInt k (fun j => g j.succ)
            (fun j => hg j.succ) (a - ti) hage]

/-- `simplexInt k g a = simplexPhi (ofFn g) a` (structural; both are head-recursive). -/
lemma simplexInt_eq_simplexPhi_ofFn :
    ∀ (k : ℕ) (g : Fin k → ℝ → ℝ) (a : ℝ),
      simplexInt k g a = WeightedRiemannKD.simplexPhi (List.ofFn g) a
  | 0, g, a => by
      simp [simplexInt, List.ofFn_zero]
  | (k + 1), g, a => by
      rw [simplexInt, List.ofFn_succ, WeightedRiemannKD.simplexPhi_cons]
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      rw [simplexInt_eq_simplexPhi_ofFn k (fun j => g j.succ) (a - y)]

/-- **The simplex-Fubini bridge** (axiom-clean): for continuous `g : Fin k → ℝ → ℝ`,
`∫_{simplex k} ∏ᵢ gᵢ(tᵢ) = nestedPhi (List.ofFn g) 0`. This is exactly the `hFubini` hypothesis of
`S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep`. -/
theorem simplex_integral_prod_eq_nestedPhi (k : ℕ) (g : Fin k → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) :
    (∫ t in Sieve.simplex k, ∏ i, g i (t i)) = WeightedRiemannKD.nestedPhi (List.ofFn g) 0 := by
  have h1 : Sieve.simplex k = Sieve.simplex_scaled k 1 := by
    ext t; simp [Sieve.simplex, Sieve.simplex_scaled]
  rw [h1, simplex_scaled_integral_prod_eq_simplexInt k g hg 1 zero_le_one,
      simplexInt_eq_simplexPhi_ofFn k g 1,
      ← WeightedRiemannKD.nestedPhi_eq_simplexPhi (List.ofFn g) 1]
  norm_num

end BoundedGaps.S1Fubini
