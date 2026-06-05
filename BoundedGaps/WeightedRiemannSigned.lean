import BoundedGaps.WeightedRiemannGen

/-!
# The signed `(μ²/φ)` `y_r`-space ladder

`WeightedRiemannGen.weighted_riemann_kd_muphi` proves the k-D Riemann limit
`nestedLogSumW (μ²/φ) R Gs R / (log R)^k → nestedPhi Gs 0` only for **nonnegative** function lists
(the abstract ladder is built with a sandwiching argument that needs `0 ≤ g`). The GPY `s1`
quadratic form `(∑_j c_j ∏_i Fs_{j,i})²` expands into **signed** cross terms
`∏_i (Fs_{j,i}·Fs_{j',i})`, so the separable-square ladder is not enough.

This file removes the nonnegativity hypothesis. The key observation: at **fixed** `R, Q` the sum
`nestedLogSumW w R · Q` is multilinear in the list entries, and `nestedPhi · s` is multilinear too —
and these identities hold at **all** truncations `Q` (resp. offsets `s`) **simultaneously**, so the
positive/negative-part split `g = g⁺ - g⁻` composes cleanly through the head recursion. The result is
`signed_expand`: every continuous list is, termwise and at every truncation, a finite signed
combination of **nonnegative** lists of the same length. Feeding each nonneg term to the nonneg
ladder and recombining gives `weighted_riemann_kd_muphi_signed`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators
open BoundedGaps.WeightedRiemannKD (nestedPhi nestedPhi_cons nestedPhi_continuous)
open BoundedGaps.WeightedRiemannGen (nestedLogSumW nestedLogSumW_cons weighted_riemann_kd_muphi)
open BoundedGaps.SingularSeries (gMoebiusSqTotient)

namespace BoundedGaps.WeightedRiemannSigned

/-! ## List-sum plumbing -/

/-- List-sum / Finset-sum interchange. -/
lemma list_map_finset_sum_comm {α β : Type*} (L : List α) (s : Finset β) (F : α → β → ℝ) :
    (L.map (fun a => ∑ b ∈ s, F a b)).sum = ∑ b ∈ s, (L.map (fun a => F a b)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]

/-- Division distributes over a list sum. -/
lemma list_sum_div {α : Type*} (L : List α) (F : α → ℝ) (D : ℝ) :
    (L.map F).sum / D = (L.map (fun a => F a / D)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, add_div, ih]

/-- A constant factors out of a list sum. -/
lemma list_sum_const_mul {α : Type*} (c : ℝ) (L : List α) (F : α → ℝ) :
    c * (L.map F).sum = (L.map (fun a => c * F a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- Negation distributes over a list sum (termwise). -/
lemma list_sum_neg {α : Type*} (L : List α) (F : α → ℝ) :
    (L.map (fun a => -(F a))).sum = -(L.map F).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, neg_add, ih]

/-- A finite list-sum of convergent sequences converges to the list-sum of the limits. -/
lemma tendsto_list_sum {α : Type*} (L : List α) (f : α → ℕ → ℝ) (l : α → ℝ)
    (h : ∀ a ∈ L, Tendsto (f a) atTop (nhds (l a))) :
    Tendsto (fun R : ℕ => (L.map (fun a => f a R)).sum) atTop (nhds ((L.map l).sum)) := by
  induction L with
  | nil => simpa using tendsto_const_nhds
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (h a (List.mem_cons_self ..)).add (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- A finite list-sum of interval-integrable functions is interval-integrable. -/
lemma intervalIntegrable_list_sum {α : Type*} (L : List α) (a b : ℝ) (F : α → ℝ → ℝ)
    (hF : ∀ p ∈ L, IntervalIntegrable (F p) volume a b) :
    IntervalIntegrable (fun y => (L.map (fun p => F p y)).sum) volume a b := by
  induction L with
  | nil => simpa using (intervalIntegrable_const (c := (0 : ℝ)))
  | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hF p (List.mem_cons_self ..)).add
        (ih (fun q hq => hF q (List.mem_cons_of_mem _ hq)))

/-- An interval integral of a finite list-sum of integrable functions is the list-sum of the
integrals. -/
lemma intervalIntegral_list_sum {α : Type*} (L : List α) (a b : ℝ) (F : α → ℝ → ℝ)
    (hF : ∀ p ∈ L, IntervalIntegrable (F p) volume a b) :
    (∫ y in a..b, (L.map (fun p => F p y)).sum) = (L.map (fun p => ∫ y in a..b, F p y)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hp := hF p (List.mem_cons_self ..)
      have htail : ∀ q ∈ L, IntervalIntegrable (F q) volume a b :=
        fun q hq => hF q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add hp (intervalIntegrable_list_sum L a b F htail), ih htail]

/-! ## Signed expansion and the signed ladder -/

/-- **Signed multilinear expansion.** Every continuous list `Gs` decomposes, at every truncation `Q`
and every offset `s` simultaneously, into a finite signed combination of **nonnegative** continuous
lists of the same length. Proof by induction on `Gs`, splitting the head `g = g⁺ - g⁻`. -/
theorem signed_expand (w : ℕ → ℝ) :
    ∀ (Gs : List (ℝ → ℝ)), (∀ g ∈ Gs, Continuous g) →
      ∃ fam : List (List (ℝ → ℝ) × ℝ),
        (∀ p ∈ fam, p.1.length = Gs.length ∧ (∀ g ∈ p.1, Continuous g)
          ∧ (∀ g ∈ p.1, ∀ x, 0 ≤ g x)) ∧
        (∀ R Q, nestedLogSumW w R Gs Q
          = (fam.map (fun p => p.2 * nestedLogSumW w R p.1 Q)).sum) ∧
        (∀ s, nestedPhi Gs s = (fam.map (fun p => p.2 * nestedPhi p.1 s)).sum)
  | [], _ => ⟨[([], 1)], by simp, fun R Q => by simp, fun s => by simp⟩
  | g :: gs, hcont => by
      have hg : Continuous g := hcont g (List.mem_cons_self ..)
      have hgs : ∀ g' ∈ gs, Continuous g' := fun g' hg' => hcont g' (List.mem_cons_of_mem _ hg')
      obtain ⟨fam', hfam', hLS', hPhi'⟩ := signed_expand w gs hgs
      set gp : ℝ → ℝ := fun x => max (g x) 0 with hgp_def
      set gn : ℝ → ℝ := fun x => max (-(g x)) 0 with hgn_def
      have hgp_cont : Continuous gp := hg.max continuous_const
      have hgn_cont : Continuous gn := hg.neg.max continuous_const
      have hgp_nn : ∀ x, 0 ≤ gp x := fun x => le_max_right _ _
      have hgn_nn : ∀ x, 0 ≤ gn x := fun x => le_max_right _ _
      have hsplit : ∀ x, g x = gp x - gn x := by
        intro x
        simp only [hgp_def, hgn_def]
        rcases le_total 0 (g x) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
        · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
      refine ⟨fam'.map (fun p => (gp :: p.1, p.2)) ++ fam'.map (fun p => (gn :: p.1, -p.2)),
        ?_, ?_, ?_⟩
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp <;> rw [List.mem_map] at hp <;> obtain ⟨q, hq, rfl⟩ := hp <;>
          obtain ⟨hl, hc, hn⟩ := hfam' q hq
        · refine ⟨by simp [List.length_cons, hl], ?_, ?_⟩
          · intro g' hg'; rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hgp_cont
            · exact hc g' hg'
          · intro g' hg' x; rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hgp_nn x
            · exact hn g' hg' x
        · refine ⟨by simp [List.length_cons, hl], ?_, ?_⟩
          · intro g' hg'; rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hgn_cont
            · exact hc g' hg'
          · intro g' hg' x; rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hgn_nn x
            · exact hn g' hg' x
      · intro R Q
        have key : ∀ (h : ℝ → ℝ),
            (fam'.map (fun p => p.2 * nestedLogSumW w R (h :: p.1) Q)).sum
              = ∑ n ∈ Finset.Icc 2 Q,
                  h (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n) := by
          intro h
          simp_rw [nestedLogSumW_cons, Finset.mul_sum]
          rw [list_map_finset_sum_comm]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [hLS' R (Q / n), list_sum_const_mul]
          exact congrArg List.sum (List.map_congr_left (fun p _ => by ring))
        have hS1 : (List.map (fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedLogSumW w R q.1 Q)
              (fam'.map (fun p => (gp :: p.1, p.2)))).sum
            = ∑ n ∈ Finset.Icc 2 Q,
                gp (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n) := by
          rw [List.map_map, ← key gp]
          exact congrArg List.sum (List.map_congr_left (fun p _ => rfl))
        have hS2 : (List.map (fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedLogSumW w R q.1 Q)
              (fam'.map (fun p => (gn :: p.1, -p.2)))).sum
            = -∑ n ∈ Finset.Icc 2 Q,
                gn (Real.log n / Real.log R) * w n * nestedLogSumW w R gs (Q / n) := by
          rw [List.map_map,
              show (fam'.map ((fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedLogSumW w R q.1 Q)
                    ∘ (fun p => (gn :: p.1, -p.2))))
                  = (fam'.map (fun p => -(p.2 * nestedLogSumW w R (gn :: p.1) Q))) from
                List.map_congr_left (fun p _ => by dsimp only [Function.comp]; ring),
              show (fam'.map (fun p => -(p.2 * nestedLogSumW w R (gn :: p.1) Q))).sum
                  = -(fam'.map (fun p => p.2 * nestedLogSumW w R (gn :: p.1) Q)).sum from
                list_sum_neg fam' _,
              key gn]
        rw [nestedLogSumW_cons, List.map_append, List.sum_append, hS1, hS2,
            ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hsplit]; ring
      · intro s
        have key : ∀ (h : ℝ → ℝ), Continuous h →
            (fam'.map (fun p => p.2 * nestedPhi (h :: p.1) s)).sum
              = ∫ y in (0:ℝ)..(1 - s), h y * nestedPhi gs (s + y) := by
          intro h hh
          have hintb : ∀ p ∈ fam',
              IntervalIntegrable (fun y => p.2 * (h y * nestedPhi p.1 (s + y))) volume 0 (1 - s) := by
            intro p hp
            refine Continuous.intervalIntegrable ?_ _ _
            exact continuous_const.mul (hh.mul
              ((nestedPhi_continuous p.1 (hfam' p hp).2.1).comp (continuous_const.add continuous_id)))
          have e1 : (fam'.map (fun p => p.2 * nestedPhi (h :: p.1) s)).sum
              = (fam'.map (fun p => ∫ y in (0:ℝ)..(1 - s),
                  p.2 * (h y * nestedPhi p.1 (s + y)))).sum := by
            refine congrArg List.sum (List.map_congr_left (fun p _ => ?_))
            rw [nestedPhi_cons, intervalIntegral.integral_const_mul]
          rw [e1, ← intervalIntegral_list_sum _ _ _ _ hintb]
          refine intervalIntegral.integral_congr (fun y _ => ?_)
          rw [hPhi' (s + y), list_sum_const_mul]
          exact congrArg List.sum (List.map_congr_left (fun p _ => by ring))
        have hgp_int : IntervalIntegrable (fun y => gp y * nestedPhi gs (s + y)) volume 0 (1 - s) :=
          (hgp_cont.mul ((nestedPhi_continuous gs hgs).comp
            (continuous_const.add continuous_id))).intervalIntegrable _ _
        have hgn_int : IntervalIntegrable (fun y => gn y * nestedPhi gs (s + y)) volume 0 (1 - s) :=
          (hgn_cont.mul ((nestedPhi_continuous gs hgs).comp
            (continuous_const.add continuous_id))).intervalIntegrable _ _
        have hS1 : (List.map (fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedPhi q.1 s)
              (fam'.map (fun p => (gp :: p.1, p.2)))).sum
            = ∫ y in (0:ℝ)..(1 - s), gp y * nestedPhi gs (s + y) := by
          rw [List.map_map, ← key gp hgp_cont]
          exact congrArg List.sum (List.map_congr_left (fun p _ => rfl))
        have hS2 : (List.map (fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedPhi q.1 s)
              (fam'.map (fun p => (gn :: p.1, -p.2)))).sum
            = -(∫ y in (0:ℝ)..(1 - s), gn y * nestedPhi gs (s + y)) := by
          rw [List.map_map,
              show (fam'.map ((fun q : List (ℝ → ℝ) × ℝ => q.2 * nestedPhi q.1 s)
                    ∘ (fun p => (gn :: p.1, -p.2))))
                  = (fam'.map (fun p => -(p.2 * nestedPhi (gn :: p.1) s))) from
                List.map_congr_left (fun p _ => by dsimp only [Function.comp]; ring),
              show (fam'.map (fun p => -(p.2 * nestedPhi (gn :: p.1) s))).sum
                  = -(fam'.map (fun p => p.2 * nestedPhi (gn :: p.1) s)).sum from
                list_sum_neg fam' _,
              key gn hgn_cont]
        rw [nestedPhi_cons, List.map_append, List.sum_append, hS1, hS2,
            ← sub_eq_add_neg, ← intervalIntegral.integral_sub hgp_int hgn_int]
        refine intervalIntegral.integral_congr (fun y _ => ?_)
        rw [hsplit y]; ring

/-- **Signed `(μ²/φ)` ladder.** The k-D Riemann limit, with no nonnegativity hypothesis: for any list
of continuous functions, `nestedLogSumW (μ²/φ) R Gs R / (log R)^k → nestedPhi Gs 0`. -/
theorem weighted_riemann_kd_muphi_signed (Gs : List (ℝ → ℝ)) (hcont : ∀ g ∈ Gs, Continuous g) :
    Tendsto (fun R : ℕ =>
        nestedLogSumW (fun n => gMoebiusSqTotient n) R Gs R / (Real.log R) ^ Gs.length)
      atTop (nhds (nestedPhi Gs 0)) := by
  obtain ⟨fam, hfam, hLS, hPhi⟩ := signed_expand (fun n => gMoebiusSqTotient n) Gs hcont
  have hnum : ∀ R : ℕ,
      nestedLogSumW (fun n => gMoebiusSqTotient n) R Gs R / (Real.log R) ^ Gs.length
        = (fam.map (fun p => p.2 *
            (nestedLogSumW (fun n => gMoebiusSqTotient n) R p.1 R / (Real.log R) ^ Gs.length))).sum := by
    intro R
    rw [hLS R R, list_sum_div]
    exact congrArg List.sum (List.map_congr_left (fun p _ => by ring))
  rw [hPhi 0, tendsto_congr hnum]
  refine tendsto_list_sum fam _ _ (fun p hp => ?_)
  have hbase := weighted_riemann_kd_muphi p.1 (hfam p hp).2.2 (hfam p hp).2.1
  rw [(hfam p hp).1] at hbase
  exact hbase.const_mul p.2

end BoundedGaps.WeightedRiemannSigned
