/-
# ε-enlarged simplex: the homothety scaling law (foundation for the `Mk_eps` polynomial bridge)

The unconditional flagship (`H₁ ≤ 246`) routes through `Sieve.Mk_eps 50 ε` — the ε-trick /
enlarged-simplex functional — for which `SievePolynomial`'s plain-`Mk` polynomial bridge does
*not* apply (`Mk_ge_polynomialMkF` is plain-`Mk` only; see `tools/mk/SYMMETRIC_REDUCTION.md`,
"What it would actually discharge"). Building a polynomial bridge for `Mk_eps` means re-running
the `SievePolynomial` Dirichlet/Fubini/DCT machinery over the **(1+ε)-enlarged** simplex
`Sieve.simplex_eps k ε = (1+ε)·R_k`.

The one genuinely *new* ingredient (everything else mirrors the plain case) is the homothety
**scaling law**: the monomial integral over the enlarged simplex is the plain one times a
`(1+ε)`-power. That is what this file establishes, axiom-clean:

  ∫_{simplex_eps k ε} ∏ tᵢ^{αᵢ}  =  (1+ε)^{k + |α|} · monomialIntegral α.

`k` powers from the volume Jacobian of the dilation, `|α|` from pulling the scalar through the
monomial. It is proved from `MeasureTheory.setIntegral_comp_smul_of_pos` (linear change of
variables for a Haar measure) plus the geometric identity `simplex_eps k ε = (1+ε) • simplex k`.

Remaining for the full `Mk_eps` bridge (NOT in this file): the slack-Dirichlet analog over the
shrunken inner simplex `simplex_shrunk`, the two-layer numerator/denominator bridges, and the
cutoff/DCT `Mk_eps_ge_polynomialMkF_eps` — i.e. the `SievePolynomial` development re-run with
this scaling law supplying the closed forms.
-/
import BoundedGaps.SievePolynomial

namespace BoundedGaps.EpsScaling

open BoundedGaps BoundedGaps.SievePolynomial
open MeasureTheory Sieve
open scoped Pointwise

/-- The (1+ε)-enlarged simplex is the dilation of the standard simplex by `(1+ε)`
(for `ε ≥ 0`, so `1+ε > 0` is invertible). -/
theorem simplex_eps_eq_smul (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    simplex_eps k ε = (1 + ε) • simplex k := by
  have hR : (0:ℝ) < 1 + ε := by linarith
  ext t
  simp only [simplex_eps, simplex, Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨hnn, hsum⟩
    refine ⟨(1 + ε)⁻¹ • t, ⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hnn i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [inv_mul_eq_div, div_le_one hR]; exact hsum
    · simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  · rintro ⟨s, ⟨hnn, hsum⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hR.le (hnn i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      calc (1 + ε) * ∑ i, s i ≤ (1 + ε) * 1 := by gcongr
        _ = 1 + ε := mul_one _

/-- **Homothety scaling law for the monomial integral.** The monomial integral over the
(1+ε)-enlarged simplex equals `(1+ε)^{k+|α|}` times the plain monomial integral. This is the
new ingredient the `Mk_eps` polynomial bridge needs; the rest mirrors `SievePolynomial`. -/
theorem monomialIntegral_eps (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (α : Fin k → ℕ) :
    (∫ t in simplex_eps k ε, ∏ i, t i ^ α i)
      = (1 + ε) ^ (k + ∑ i, α i) * (monomialIntegral α : ℝ) := by
  have hR : (0:ℝ) < 1 + ε := by linarith
  have hc : ((1 + ε) ^ k : ℝ) ≠ 0 := by positivity
  have hfr : Module.finrank ℝ (Fin k → ℝ) = k := by rw [Module.finrank_pi, Fintype.card_fin]
  have key := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin k → ℝ))
      (fun t => ∏ i, t i ^ α i) (simplex k) hR
  rw [hfr] at key
  simp only [smul_eq_mul] at key
  -- key : ∫ x in simplex k, ∏ i, ((1+ε) • x) i ^ α i = ((1+ε)^k)⁻¹ * ∫ x in (1+ε)•simplex k, ∏ x^α
  have hcomp : (∫ x in simplex k, ∏ i, ((1 + ε) • x) i ^ α i)
      = (1 + ε) ^ (∑ i, α i) * (monomialIntegral α : ℝ) := by
    rw [← monomialIntegral_eq α, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun (isClosed_simplex k).measurableSet (fun x _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hcomp] at key
  -- key : (1+ε)^∑α * monoInt = ((1+ε)^k)⁻¹ * ∫ x in (1+ε)•simplex k, ∏ x^α
  rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hc] at key
  -- key : ∫ x in (1+ε)•simplex k, ∏ x^α = (1+ε)^k * ((1+ε)^∑α * monoInt)
  rw [simplex_eps_eq_smul k hε, key, pow_add]
  ring

/-! ## The `Mk_eps` denominator closed form

The denominator of `Mk_eps` is `∫_{(1+ε)R_k} F²` — a *pure dilation* of the plain
denominator, so `monomialIntegral_eps` collapses it termwise exactly as `denom_bridge` does for
the plain case. (The `Mk_eps` *numerator* is genuinely different — outer integration over the
*shrunken* `simplex_shrunk` with inner bound `1+ε-∑s` — and needs a separate generalized
incomplete-Dirichlet keystone over that mixed `(1-ε)/(1+ε)` geometry; not here.)

Note the closed form is real-valued: `(1+ε)` is real, so for an irrational ε it is not
rational. The eventual `native_decide` step picks a *rational* ε, at which point every factor
is rational again. -/

/-- Each monomial term is integrable on the (compact) enlarged simplex. -/
lemma monomial_integrableOn_eps {k : ℕ} (ε : ℝ) (α : Fin k → ℕ) (c : ℝ) :
    Integrable (fun t : Fin k → ℝ => c * ∏ i, t i ^ α i) (volume.restrict (simplex_eps k ε)) :=
  (Continuous.continuousOn (by fun_prop)).integrableOn_compact (isCompact_simplex_eps k ε)

/-- **Denominator bridge for `Mk_eps`.** For a polynomial sieve weight `P` and `ε ≥ 0`, the
`Mk_eps` denominator `∫_{(1+ε)R_k} P²` has the closed form `Σ_{p,q} c_p c_q ·
(1+ε)^{k+|p+q|} · monomialIntegral(p+q)` — the plain `denom_bridge` with each
`monomialIntegral` dilated by its `monomialIntegral_eps` factor. -/
theorem mkF_eps_denominator_poly {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (P : PolynomialSieveWeight k) :
    mkF_eps_denominator k ε P.toFun
      = ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          (p.2 : ℝ) * (q.2 : ℝ)
            * ((1 + ε) ^ (k + ∑ i, (p.1 + q.1) i) * (monomialIntegral (p.1 + q.1) : ℝ)) := by
  rw [mkF_eps_denominator]
  have hsq : ∀ t : Fin k → ℝ, P.toFun t ^ 2
      = ∑ p ∈ P.terms, ∑ q ∈ P.terms,
          ((p.2 : ℝ) * (q.2 : ℝ)) * ∏ i, t i ^ ((p.1 + q.1) i) := by
    intro t
    rw [sq, PolynomialSieveWeight.toFun, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [show (∏ i, t i ^ ((p.1 + q.1) i)) = (∏ i, t i ^ p.1 i) * ∏ i, t i ^ q.1 i from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [Pi.add_apply, pow_add])]
    ring
  simp_rw [hsq]
  rw [MeasureTheory.integral_finset_sum _ (fun p _ =>
    MeasureTheory.integrable_finset_sum _ (fun q _ =>
      monomial_integrableOn_eps ε (p.1 + q.1) ((p.2 : ℝ) * (q.2 : ℝ))))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [MeasureTheory.integral_finset_sum _ (fun q _ =>
    monomial_integrableOn_eps ε (p.1 + q.1) ((p.2 : ℝ) * (q.2 : ℝ)))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [MeasureTheory.integral_const_mul, monomialIntegral_eps k hε (p.1 + q.1)]

/-! ## The `Mk_eps` numerator keystone: an affine-slack Dirichlet integral

The `Mk_eps` numerator's marginal `J_{i,1-ε}` integrates the squared inner antiderivative over
the **shrunken** simplex `simplex_shrunk n ε = (1-ε)R_n`, with the inner `ti`-integral running to
`1+ε-∑s`. Squaring the antiderivative produces a power of `(1+ε-∑s)`, so the marginal reduces to
the **affine-slack** integral

  ∫_{(1-ε)R_n} (∏ⱼ sⱼ^{aⱼ}) · (1+ε - ∑ⱼ sⱼ)^β  ds.

Unlike the plain slack `(1-∑s)^β`, the slack base `1+ε` and the domain bound `1-ε` differ, so this
is *not* a single standard Dirichlet integral. The trick: rescale `s = (1-ε)σ` to the standard
simplex, then `1+ε-(1-ε)∑σ = 2ε + (1-ε)(1-∑σ)`, and `add_pow` expands the `β`-th power into a
binomial sum of **standard** slack-Dirichlet integrals `dirichletIntegralWithSlack a (β-m)` — each
already in closed form. This is the genuine ε-numerator kernel (the analog of `dirichlet_slack`). -/

/-- The standard-simplex affine-slack integral, binomially expanded into standard slack-Dirichlet
integrals via `1+ε-(1-ε)∑σ = 2ε + (1-ε)(1-∑σ)` and `add_pow`. -/
theorem dirichlet_affine_slack_std {n : ℕ} (a : Fin n → ℕ) (β : ℕ) (ε : ℝ) :
    (∫ σ in simplex n, (∏ j, σ j ^ a j) * (1 + ε - (1 - ε) * ∑ j, σ j) ^ β)
      = ∑ m ∈ Finset.range (β + 1),
          (2 * ε) ^ m * (1 - ε) ^ (β - m) * (β.choose m : ℝ)
            * (dirichletIntegralWithSlack a (β - m) : ℝ) := by
  have hexp : Set.EqOn
      (fun σ : Fin n → ℝ => (∏ j, σ j ^ a j) * (1 + ε - (1 - ε) * ∑ j, σ j) ^ β)
      (fun σ => ∑ m ∈ Finset.range (β + 1),
          ((2 * ε) ^ m * (1 - ε) ^ (β - m) * (β.choose m : ℝ))
            * ((∏ j, σ j ^ a j) * (1 - ∑ j, σ j) ^ (β - m)))
      (simplex n) := by
    intro σ _
    dsimp only
    rw [show (1 + ε - (1 - ε) * ∑ j, σ j) = 2 * ε + (1 - ε) * (1 - ∑ j, σ j) from by ring,
        add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [mul_pow]; ring
  rw [MeasureTheory.setIntegral_congr_fun (isClosed_simplex n).measurableSet hexp,
      MeasureTheory.integral_finset_sum _ (fun m _ => simplexIntegrable (by fun_prop))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MeasureTheory.integral_const_mul, dirichletSlack_eq a (β - m)]

/-- The (1-ε)-shrunken simplex is the dilation of the standard simplex by `(1-ε)`
(for `0 ≤ ε < 1`, so `1-ε > 0` is invertible). -/
theorem simplex_shrunk_eq_smul (n : ℕ) {ε : ℝ} (hε1 : ε < 1) :
    simplex_shrunk n ε = (1 - ε) • simplex n := by
  have hR : (0:ℝ) < 1 - ε := by linarith
  ext t
  simp only [simplex_shrunk, simplex, Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · rintro ⟨hnn, hsum⟩
    refine ⟨(1 - ε)⁻¹ • t, ⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hnn i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [inv_mul_eq_div, div_le_one hR]; exact hsum
    · simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  · rintro ⟨s, ⟨hnn, hsum⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hR.le (hnn i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      calc (1 - ε) * ∑ i, s i ≤ (1 - ε) * 1 := by gcongr
        _ = 1 - ε := mul_one _

/-- **The `Mk_eps` numerator keystone.** The affine-slack Dirichlet integral over the shrunken
simplex has the closed form `(1-ε)^{n+|a|} · Σ_m C(β,m) (2ε)^m (1-ε)^{β-m} ·
monomialIntegralWithSlack(a, β-m)` — the dilation Jacobian `(1-ε)^{n+|a|}` times the binomial
sum from `dirichlet_affine_slack_std`. This is the closed form the polynomial `Mk_eps` numerator
bridge needs. -/
theorem dirichlet_affine_slack {n : ℕ} (a : Fin n → ℕ) (β : ℕ) {ε : ℝ} (hε1 : ε < 1) :
    (∫ s in simplex_shrunk n ε, (∏ j, s j ^ a j) * (1 + ε - ∑ j, s j) ^ β)
      = (1 - ε) ^ (n + ∑ j, a j)
          * ∑ m ∈ Finset.range (β + 1),
              (2 * ε) ^ m * (1 - ε) ^ (β - m) * (β.choose m : ℝ)
                * (dirichletIntegralWithSlack a (β - m) : ℝ) := by
  have hR : (0:ℝ) < 1 - ε := by linarith
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by rw [Module.finrank_pi, Fintype.card_fin]
  have key := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin n → ℝ))
      (fun s => (∏ j, s j ^ a j) * (1 + ε - ∑ j, s j) ^ β) (simplex n) hR
  rw [hfr] at key
  simp only [smul_eq_mul] at key
  have hcomp : (∫ σ in simplex n,
        (∏ j, ((1 - ε) • σ) j ^ a j) * (1 + ε - ∑ j, ((1 - ε) • σ) j) ^ β)
      = (1 - ε) ^ (∑ j, a j) * ∑ m ∈ Finset.range (β + 1),
          (2 * ε) ^ m * (1 - ε) ^ (β - m) * (β.choose m : ℝ)
            * (dirichletIntegralWithSlack a (β - m) : ℝ) := by
    rw [← dirichlet_affine_slack_std a β ε, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun (isClosed_simplex n).measurableSet (fun σ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, (1 - ε) * σ j) = (1 - ε) * ∑ j, σ j from by rw [← Finset.mul_sum],
        show (∏ j, ((1 - ε) * σ j) ^ a j) = (1 - ε) ^ (∑ j, a j) * ∏ j, σ j ^ a j from by
          simp only [mul_pow]; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]]
    ring
  rw [hcomp] at key
  rw [eq_comm, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero n hR.ne')] at key
  rw [simplex_shrunk_eq_smul n hε1, key, pow_add]
  ring

end BoundedGaps.EpsScaling
