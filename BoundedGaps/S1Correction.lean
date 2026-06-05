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

/-- **Sieve count = lattice-count framework count** (the full bridge). Composing
`sieve_count_eq_lcm_count` with the `Icc → Ioc` index shift (`A = ⌈x⌉₊-1`, `B = ⌊2x⌋₊`; valid since
`x>0 ⟹ ⌈x⌉₊≥1`) and the filter merge, the sieve's correction count is put in the **exact** shape
`SieveExpansion.lattice_count_main_term` / `lattice_count_offdiag_vanish_Wtrick` consume:
`#{m ∈ Ioc A B : m ≡ b [MOD W] ∧ ∀ i ∈ finRange k, q i ∣ (m+hᵢ)}` with the single modulus
`q i = lcm (P i).1 (P i).2`, index list `l = List.finRange k`, shifts `h i = H.getD i.val 0`. Feeds
`herr` (`lattice_count_main_term`, given pairwise-coprime `q` + `W`-coprimality) and `hvanish`
(`lattice_count_offdiag_vanish_Wtrick`) of `correction_abs_bound_offdiag`. -/
theorem sieve_count_eq_lattice_count (k : ℕ) (H : List ℕ) (b W : ℕ) (x : ℝ) (hx : 0 < x)
    (P : Fin k → ℕ × ℕ) :
    (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ i : Fin k,
          (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
      = ((Finset.Ioc (⌈x⌉₊ - 1) ⌊2 * x⌋₊).filter
          (fun m => m ≡ b [MOD W] ∧ ∀ i ∈ List.finRange k,
            Nat.lcm (P i).1 (P i).2 ∣ (m + H.getD i.val 0))).card := by
  rw [sieve_count_eq_lcm_count, Finset.filter_filter]
  have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  have hIcc : Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ = Finset.Ioc (⌈x⌉₊ - 1) ⌊2 * x⌋₊ := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  congr 1
  apply Finset.filter_congr
  intro m _
  constructor
  · rintro ⟨hmod, hdvd⟩
    exact ⟨hmod, fun i _ => hdvd i⟩
  · rintro ⟨hmod, hdvd⟩
    exact ⟨hmod, fun i => hdvd i (List.mem_finRange i)⟩

/-- **W-trick pair-form off-diagonal vanishing.** The pair-divisibility count appearing in the
y-space correction (`#{m ∈ S : ∀t, (P t).1 ∣ (m+hₜ) ∧ (P t).2 ∣ (m+hₜ)}`) is exactly `0` whenever
two coordinates `i ≠ j` have *non-coprime* moduli `lcm(P i)`, `lcm(P j)`, *provided* the W-trick
setup holds: every prime `≤ D₀` divides `W`, the `i`-th modulus is `W`-coprime, and the shifts are
`≤ D₀` and distinct. Reason: a shared prime `p ∣ lcm(P i), lcm(P j)` cannot divide `W` (else
`p ∣ gcd(lcm(P i), W) = 1`), so `p > D₀ ≥ hᵢ, hⱼ`; with `hᵢ ≠ hⱼ` this gives `hᵢ ≢ hⱼ [MOD p]`, and
`lattice_count_pair_offdiag_vanish` fires. This is the pair-divisibility analog of
`SieveExpansion.lattice_count_offdiag_vanish_Wtrick`, and discharges the `hvanish` leg of the
correction bound (`yspace_correction_abs_bound`) UNCONDITIONALLY (no BV — only admissibility + the
W-trick). -/
theorem lattice_count_pair_offdiag_vanish_Wtrick {k : ℕ} (H : List ℕ) (S : Finset ℕ)
    (P : Fin k → ℕ × ℕ) {i j : Fin k} (D₀ W : ℕ)
    (hWdvd : ∀ p, p.Prime → p ≤ D₀ → p ∣ W)
    (hcopi : Nat.Coprime (Nat.lcm (P i).1 (P i).2) W)
    (hncop : ¬ Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2))
    (hbi : H.getD i.val 0 ≤ D₀) (hbj : H.getD j.val 0 ≤ D₀)
    (hij : H.getD i.val 0 ≠ H.getD j.val 0) :
    (S.filter (fun m => ∀ t : Fin k,
        (P t).1 ∣ (m + H.getD t.val 0) ∧ (P t).2 ∣ (m + H.getD t.val 0))).card = 0 := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hncop
  have hpi : p ∣ Nat.lcm (P i).1 (P i).2 := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpj : p ∣ Nat.lcm (P j).1 (P j).2 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpD : D₀ < p := by
    by_contra hle
    have hpW : p ∣ W := hWdvd p hp (not_lt.mp hle)
    have hcontra : p ∣ Nat.gcd (Nat.lcm (P i).1 (P i).2) W := Nat.dvd_gcd hpi hpW
    rw [hcopi] at hcontra
    exact hp.ne_one (Nat.dvd_one.mp hcontra)
  refine BoundedGaps.Sieve.lattice_count_pair_offdiag_vanish H S P hpi hpj (fun hcon => hij ?_)
  rw [Nat.ModEq, Nat.mod_eq_of_lt (lt_of_le_of_lt hbi hpD),
      Nat.mod_eq_of_lt (lt_of_le_of_lt hbj hpD)] at hcon
  exact hcon

/-- **Restrict a pair-product weighted sum to the divisor-closed support.** When the per-coordinate
coefficient `lam i` vanishes off `R i` (e.g. `yLambda` off its divisor-closed candidate set), the
double-product weighted sum over the full lattice `T i ×ˢ T i` collapses to the support `R i ×ˢ R i`
(the extra terms have a zero factor in `∏ᵢ lam i (P i).1 · lam i (P i).2`). The structural step that
restricts the y-space correction from `sieveDivisors` to the squarefree `W`-coprime candidate set
`Rset` — on which every modulus is `W`-coprime (so the W-trick applies). -/
theorem piFinset_prod_pair_sum_restrict {k : ℕ} (R T : Fin k → Finset ℕ)
    (hRT : ∀ i, R i ⊆ T i) (lam : Fin k → ℕ → ℝ)
    (hlam : ∀ i, ∀ d, d ∉ R i → lam i d = 0) (g : (Fin k → ℕ × ℕ) → ℝ) :
    ∑ P ∈ Fintype.piFinset (fun i => T i ×ˢ T i),
        (∏ i : Fin k, lam i (P i).1 * lam i (P i).2) * g P
      = ∑ P ∈ Fintype.piFinset (fun i => R i ×ˢ R i),
        (∏ i : Fin k, lam i (P i).1 * lam i (P i).2) * g P := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · exact Fintype.piFinset_subset _ _ (fun i => Finset.product_subset_product (hRT i) (hRT i))
  · intro P hPbig hPsmall
    have hprod : (∏ i : Fin k, lam i (P i).1 * lam i (P i).2) = 0 := by
      rw [Fintype.mem_piFinset] at hPbig
      simp only [Fintype.mem_piFinset, not_forall] at hPsmall
      obtain ⟨i, hi⟩ := hPsmall
      rw [Finset.mem_product, not_and_or] at hi
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rcases hi with h1 | h2
      · rw [hlam i (P i).1 h1, zero_mul]
      · rw [hlam i (P i).2 h2, mul_zero]
    rw [hprod, zero_mul]

/-- Lcm of two `W`-coprime numbers is `W`-coprime. -/
theorem coprime_lcm_of_coprime {a b W : ℕ} (ha : Nat.Coprime a W) (hb : Nat.Coprime b W) :
    Nat.Coprime (Nat.lcm a b) W :=
  Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))
    (Nat.Coprime.mul_left ha hb)

/-- **The y-space S1 correction, bounded by the diagonal + off-diagonal size sums (the `hcorr`
reduction).** Instantiates `SieveExpansion.correction_abs_bound_offdiag` on the *actual* y-space
correction (the numerator of `S1FullLimit.yspace_s1_sieveSum_div_tendsto`'s `hcorr`). After
restricting to the divisor-closed candidate set `Rset` (`piFinset_prod_pair_sum_restrict`, the off-
`Rset` terms vanish), every modulus `lcm(P i)` is `W`-coprime, so the off-diagonal count vanishes
UNCONDITIONALLY via the W-trick (`lattice_count_pair_offdiag_vanish_Wtrick` — no BV); the diagonal
`O(1)` error `herr` (the `M`-normalisation-dependent leg, fed by `lattice_count_main_term` after
`sieve_count_eq_lattice_count`) is taken as a hypothesis. Output: the correction is bounded by the
diagonal total weight `∑_{diag}|∏λλ|` plus the off-diagonal weighted-main `∑_{¬diag}|∏λλ|·M/∏[dᵢ,eᵢ]`
— the exact shape the two remaining elementary SIZE estimates attack (diagonal via `S1DiagonalSize`
+ a y-space coeff bound; off-diagonal via the shared-prime `∑_{p>D₀}1/p²` tail). -/
theorem yspace_correction_abs_bound {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (x R M : ℝ) (D₀ : ℕ) (hMnonneg : 0 ≤ M)
    (hWdvd : ∀ p, p.Prime → p ≤ D₀ → p ∣ W)
    (hshift_le : ∀ i : Fin k, H.getD i.val 0 ≤ D₀)
    (hshift_ne : ∀ i j : Fin k, i ≠ j → H.getD i.val 0 ≠ H.getD j.val 0)
    (herr : ∀ P ∈ (Fintype.piFinset (fun i : Fin k =>
        ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W))
          ×ˢ ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
            (fun r => Squarefree r ∧ Nat.Coprime r W)))).filter
        (fun P => ∀ i j : Fin k, i ≠ j →
          Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)),
        |((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card : ℝ)
            - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)| ≤ 1) :
    |∑ P ∈ Fintype.piFinset (fun i : Fin k =>
          BoundedGaps.Sieve.sieveDivisors H i.val b W x
            ×ˢ BoundedGaps.Sieve.sieveDivisors H i.val b W x),
        (∏ i : Fin k,
          S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).1
            * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
              (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).2)
          * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                (fun m => ∀ i : Fin k,
                  (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
              - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))|
      ≤ (∑ P ∈ (Fintype.piFinset (fun i : Fin k =>
            ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W))
              ×ˢ ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)))).filter
            (fun P => ∀ i j : Fin k, i ≠ j →
              Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)),
          |∏ i : Fin k,
            S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).1
              * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).2|)
        + ∑ P ∈ (Fintype.piFinset (fun i : Fin k =>
            ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W))
              ×ˢ ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)))).filter
            (fun P => ¬ ∀ i j : Fin k, i ≠ j →
              Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)),
          |∏ i : Fin k,
            S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).1
              * S1YSpace.yLambda ((BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
                (fun r => Squarefree r ∧ Nat.Coprime r W)) (Fs i) (Real.log R) (P i).2|
            * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)) := by
  classical
  set Rset : Fin k → Finset ℕ := fun i =>
    (BoundedGaps.Sieve.sieveDivisors H i.val b W x).filter
      (fun r => Squarefree r ∧ Nat.Coprime r W) with hRsetdef
  set lam : Fin k → ℕ → ℝ := fun i =>
    S1YSpace.yLambda (Rset i) (Fs i) (Real.log R) with hlamdef
  set cnt : (Fin k → ℕ × ℕ) → ℝ := fun P =>
    ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ i : Fin k,
          (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card : ℝ) with hcntdef
  set mn : (Fin k → ℕ × ℕ) → ℝ := fun P =>
    M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ) with hmndef
  set w : (Fin k → ℕ × ℕ) → ℝ := fun P =>
    ∏ i : Fin k, lam i (P i).1 * lam i (P i).2 with hwdef
  set diag : (Fin k → ℕ × ℕ) → Prop := fun P => ∀ i j : Fin k, i ≠ j →
    Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2) with hdiagdef
  have hdc : ∀ i, ∀ s ∈ Rset i, ∀ d, d ∣ s → d ∈ Rset i := fun i =>
    (BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x).2.2
  have hlamvan : ∀ i, ∀ d, d ∉ Rset i → lam i d = 0 := fun i d hd =>
    S1YSpace.yLambda_eq_zero_of_not_mem (Rset i) (hdc i) (Fs i) (Real.log R) hd
  rw [piFinset_prod_pair_sum_restrict Rset
      (fun i => BoundedGaps.Sieve.sieveDivisors H i.val b W x)
      (fun i => Finset.filter_subset _ _) lam hlamvan (fun P => cnt P - mn P)]
  refine BoundedGaps.Sieve.correction_abs_bound_offdiag
    (Fintype.piFinset (fun i => Rset i ×ˢ Rset i)) w cnt mn diag ?_ herr ?_
  · intro P hP hndiag
    have hmem := Fintype.mem_piFinset.mp hP
    have hcop : ∀ i, Nat.Coprime (Nat.lcm (P i).1 (P i).2) W := by
      intro i
      have h2 := Finset.mem_product.mp (hmem i)
      have hc1 := (Finset.mem_filter.mp h2.1).2.2
      have hc2 := (Finset.mem_filter.mp h2.2).2.2
      exact coprime_lcm_of_coprime hc1 hc2
    simp only [hdiagdef, not_forall] at hndiag
    obtain ⟨i, j, hne, hncop⟩ := hndiag
    have hzero : (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ t : Fin k,
          (P t).1 ∣ (m + H.getD t.val 0) ∧ (P t).2 ∣ (m + H.getD t.val 0))).card = 0 :=
      lattice_count_pair_offdiag_vanish_Wtrick H _ P D₀ W hWdvd (hcop i) hncop
        (hshift_le i) (hshift_le j) (hshift_ne i j hne)
    rw [hcntdef]; simp only [hzero, Nat.cast_zero]
  · intro P _
    rw [hmndef]
    exact div_nonneg hMnonneg (Finset.prod_nonneg (fun i _ => by positivity))

end BoundedGaps.S1Correction
