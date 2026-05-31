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

end BoundedGaps.EpsScaling
