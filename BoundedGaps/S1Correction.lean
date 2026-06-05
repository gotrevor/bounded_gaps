/-
# The y-space S1 correction decomposition (towards `correction = o(main)`, UNCONDITIONAL)

Per the lap-6 strategic correction (`PENDING_WORK.md`): the s1 correction is **NOT** BV-gated — only
s2 (the prime weight) needs EH/BV; s1 (non-prime) is elementary. This file begins the unconditional
discharge of `hcorr` (the sole remaining analytic input to `S1FullLimit.yspace_s1_sieveSum_div_tendsto`).

## The decomposition (roadmap)
The correction (`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`) is
`∑_P (∏ᵢ yLambda(dᵢ)yLambda(eᵢ))·(count_P − M/∏ᵢ[dᵢ,eᵢ])`. Via `SieveExpansion.correction_abs_bound_offdiag`
(with `diag P := the moduli lcm(dᵢ,eᵢ) pairwise coprime across coords`) it bounds by
`∑_{diag}|∏λλ| + ∑_{¬diag}|∏λλ|·M/∏[dᵢ,eᵢ]`, given:
* **`hvanish`** (`¬diag ⟹ count_P = 0`): `SieveExpansion.lattice_count_offdiag_vanish_Wtrick` —
  two coords sharing a prime `p>D₀` have incompatible shifts under the W-trick;
* **`herr`** (`diag ⟹ |count_P − M/∏[dᵢ,eᵢ]| ≤ 1`): `SieveExpansion.lattice_count_main_term` (CRT);
* **`hmain`** (`¬diag ⟹ 0 ≤ M/∏[dᵢ,eᵢ]`): `M ≥ 0`.

Both `lattice_count_*` are stated for a **single** modulus `q i ∣ (m+hᵢ)`; the sieve count uses the
**two** moduli `(P i).1, (P i).2`. `sieve_count_eq_lcm_count` (below) bridges them via
`q i = lcm (P i).1 (P i).2`. The remaining two size bounds are then elementary (no BV):
* diagonal `∑_{diag}|∏λλ| = o(M·(log R)^k)` — the count side is `S1DiagonalSize` (DONE); needs the
  y-space coefficient bound `|∏ yLambda²| ≤ C²·(count weight)`;
* off-diagonal `∑_{¬diag}|∏λλ|·M/∏[dᵢ,eᵢ] = o(M·(log R)^k)` — the shared-prime restriction yields a
  `∑_{p>D₀} 1/p² → 0` factor (Mertens, in mathlib).
-/
import BoundedGaps.S1YSpace

open scoped BigOperators

namespace BoundedGaps.S1Correction

/-- **Sieve count = lcm-divisibility count** (the bridge to the lattice-count framework). The
per-`P` joint-divisibility count appearing in the y-space correction
(`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`) — counting `m` with
`(P i).1 ∣ (m+hᵢ)` AND `(P i).2 ∣ (m+hᵢ)` for every coordinate — equals the count with the single
modulus `lcm (P i).1 (P i).2 ∣ (m+hᵢ)`. Pure `Nat.lcm_dvd_iff`, per coordinate. This is the first
step of instantiating `SieveExpansion.lattice_count_main_term` / `lattice_count_offdiag_vanish_Wtrick`
(both stated for a single modulus `q i = lcm (P i).1 (P i).2`) on the sieve's correction count. -/
theorem sieve_count_eq_lcm_count (k : ℕ) (H : List ℕ) (b W : ℕ) (x : ℝ) (P : Fin k → ℕ × ℕ) :
    (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ i : Fin k,
          (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
      = (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ i : Fin k, Nat.lcm (P i).1 (P i).2 ∣ (m + H.getD i.val 0))).card := by
  congr 1
  apply Finset.filter_congr
  intro m _
  apply forall_congr'
  intro i
  rw [Nat.lcm_dvd_iff]

end BoundedGaps.S1Correction
