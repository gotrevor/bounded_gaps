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
open ArithmeticFunction (moebius)

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

/-- **Smoothing, elementary step: factor out the multiplicative `d/φ(d)` prefactor.** For `R`
consisting of squarefree integers and `d ≥ 1`,
`yLambda R F L d = (d/φ(d)) · ∑_{s∈R, d∣s} μ(s/d)·F(log s/L)/φ(s/d)`.
This is Maynard's first reduction (`PartialSummation`): squarefreeness gives `φ(s) = φ(d)·φ(s/d)`
for `d ∣ s`, so the `d/φ(d)` multiplicative factor splits off cleanly. The residual sum (reindexed
`t = s/d`) is `∑_{t} μ(t)·F(log(dt)/L)/φ(t)`, whose `≈ −F′(·)/log R` asymptotic is the
genuinely-deep Möbius-mean / PNT-strength step (no in-kernel route in this mathlib). This lemma
ISOLATES the elementary multiplicative factor from that deep residual — narrowing the smoothing. -/
theorem yLambda_factor (R : Finset ℕ) (F : ℝ → ℝ) (L : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hRsf : ∀ s ∈ R, Squarefree s) :
    S1YSpace.yLambda R F L d = ((d : ℝ) / (Nat.totient d : ℝ))
      * ∑ s ∈ R.filter (fun s => d ∣ s),
          (moebius (s / d) : ℝ) * F (Real.log s / L) / (Nat.totient (s / d) : ℝ) := by
  unfold S1YSpace.yLambda
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_filter] at hs
  have hsf : Squarefree s := hRsf s hs.1
  have hds : d ∣ s := hs.2
  have hsne : s ≠ 0 := hsf.ne_zero
  have hcop : Nat.Coprime d (s / d) := by
    have hs' : d * (s / d) = s := Nat.mul_div_cancel' hds
    rw [← hs'] at hsf
    exact (Nat.squarefree_mul_iff.mp hsf).1
  have hphi : Nat.totient s = Nat.totient d * Nat.totient (s / d) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hds]
    exact Nat.totient_mul hcop
  have hφd : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hsd1 : 1 ≤ s / d := Nat.one_le_div_iff hd |>.mpr (Nat.le_of_dvd (by omega) hds)
  have hφsd : (0 : ℝ) < (Nat.totient (s / d) : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hsd1
  rw [hphi]
  push_cast
  field_simp

/-- **Closed-form bound on the y-space coefficient.** With `|F| ≤ C` and `R` consisting of positive
integers, the y-space sieve coefficient is bounded by `|yLambda R F L d| ≤ d·C·∑_{s∈R, d∣s} 1/φ(s)`
(triangle inequality + `|μ| ≤ 1` + `|F| ≤ C`). The first reduction toward the diagonal SIZE bound
(`∑_{diag}|∏λλ| = o(M(log R)^k)`, the diagonal leg of `yspace_correction_abs_bound`): `yLambda` is
NOT uniformly `O(1)`, but its magnitude is controlled by `d` and the `1/φ` tail of its support.
[Fully controlling the diagonal size further needs the smoothing `yLambda ≈ (d/φ(d))·C/log R`
(Maynard `PartialSummation`, the `brick_smooth` content) to beat the naive `d`-factor.] -/
theorem abs_yLambda_le (R : Finset ℕ) (F : ℝ → ℝ) (L : ℝ) (d : ℕ) (C : ℝ)
    (hC : ∀ t, |F t| ≤ C) (hR1 : ∀ s ∈ R, 1 ≤ s) :
    |S1YSpace.yLambda R F L d|
      ≤ (d : ℝ) * C * ∑ s ∈ R.filter (fun s => d ∣ s), 1 / (Nat.totient s : ℝ) := by
  unfold S1YSpace.yLambda
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ s ∈ R.filter (fun s => d ∣ s),
            (moebius (s / d) : ℝ) * (F (Real.log s / L) / (Nat.totient s : ℝ))|
      ≤ ∑ s ∈ R.filter (fun s => d ∣ s),
            |(moebius (s / d) : ℝ) * (F (Real.log s / L) / (Nat.totient s : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ R.filter (fun s => d ∣ s), C / (Nat.totient s : ℝ) := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        have hs1 : 1 ≤ s := hR1 s (Finset.mem_filter.mp hs).1
        have hφpos : (0:ℝ) < (Nat.totient s : ℝ) := by
          have := Nat.totient_pos.mpr (by omega : 0 < s); exact_mod_cast this
        rw [abs_mul, abs_div]
        have hmu : |(moebius (s / d) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hFC : |F (Real.log s / L)| ≤ C := hC _
        rw [abs_of_pos hφpos]
        calc |(moebius (s / d) : ℝ)| * (|F (Real.log s / L)| / (Nat.totient s : ℝ))
            ≤ 1 * (C / (Nat.totient s : ℝ)) := by gcongr
          _ = C / (Nat.totient s : ℝ) := one_mul _
    _ = C * ∑ s ∈ R.filter (fun s => d ∣ s), 1 / (Nat.totient s : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ => ?_); ring

/-- **x-independent polynomial bound on the y-space coefficient.** With the test function `F` cut
off above `1` (`F t = 0` for `t > 1`) and `|F| ≤ C`, the y-space coefficient at level `N`
(`L = log N`, `N ≥ 2`) is bounded by `|yLambda R F (log N) d| ≤ d·C·N`, **independent of the size of
`R`** (hence of the sieve scale `x`): the support cutoff kills every `s > N`, so at most `N` terms
survive, each `≤ C`. This is the elementary (PNT-free) ingredient for the *diagonal* leg of the s1
correction — combined with a large scale `x` it forces the diagonal error `o(main)` with no Möbius
cancellation. -/
theorem abs_yLambda_le_level (R : Finset ℕ) (F : ℝ → ℝ) (N d : ℕ) (C : ℝ)
    (hN : 2 ≤ N) (hC : ∀ t, |F t| ≤ C) (hFcut : ∀ t, 1 < t → F t = 0)
    (hR1 : ∀ s ∈ R, 1 ≤ s) :
    |S1YSpace.yLambda R F (Real.log N) d| ≤ (d : ℝ) * C * (N : ℝ) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  unfold S1YSpace.yLambda
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  classical
  -- termwise bound by `if s ≤ N then C else 0`
  have key : ∀ s ∈ R.filter (fun s => d ∣ s),
      |(moebius (s / d) : ℝ) * (F (Real.log s / Real.log N) / (Nat.totient s : ℝ))|
        ≤ (if s ≤ N then C else 0) := by
    intro s hs
    have hsR : s ∈ R := (Finset.mem_filter.mp hs).1
    have hs1 : 1 ≤ s := hR1 s hsR
    have hφpos : (0:ℝ) < (Nat.totient s : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < s); exact_mod_cast this
    by_cases hsN : s ≤ N
    · rw [if_pos hsN, abs_mul, abs_div, abs_of_pos hφpos]
      have hmu : |(moebius (s / d) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hφ1 : (1:ℝ) ≤ (Nat.totient s : ℝ) := by
        have := Nat.totient_pos.mpr (by omega : 0 < s); exact_mod_cast this
      calc |(moebius (s / d) : ℝ)| * (|F (Real.log s / Real.log N)| / (Nat.totient s : ℝ))
          ≤ 1 * (C / 1) := by
            gcongr
            · exact hC _
        _ = C := by ring
    · -- s > N : log s / log N > 1, so F = 0
      rw [if_neg hsN]
      have hsgt : (N : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : N < s)
      have hlogs : Real.log N < Real.log s :=
        Real.log_lt_log (by exact_mod_cast (by omega : 0 < N)) hsgt
      have hgt1 : 1 < Real.log s / Real.log N := by
        rw [lt_div_iff₀ hlogN]; linarith
      rw [hFcut _ hgt1]
      simp
  calc |∑ s ∈ R.filter (fun s => d ∣ s),
            (moebius (s / d) : ℝ) * (F (Real.log s / Real.log N) / (Nat.totient s : ℝ))|
      ≤ ∑ s ∈ R.filter (fun s => d ∣ s),
            |(moebius (s / d) : ℝ) * (F (Real.log s / Real.log N) / (Nat.totient s : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ R.filter (fun s => d ∣ s), (if s ≤ N then C else 0) := Finset.sum_le_sum key
    _ = ∑ s ∈ (R.filter (fun s => d ∣ s)).filter (fun s => s ≤ N), C := (Finset.sum_filter _ _).symm
    _ = ((R.filter (fun s => d ∣ s)).filter (fun s => s ≤ N)).card • C := Finset.sum_const C
    _ ≤ (N : ℝ) * C := by
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hC0
        have hsub : (R.filter (fun s => d ∣ s)).filter (fun s => s ≤ N) ⊆ Finset.Icc 1 N := by
          intro s hs
          rw [Finset.mem_filter] at hs
          have hsR : s ∈ R := (Finset.mem_filter.mp hs.1).1
          exact Finset.mem_Icc.mpr ⟨hR1 s hsR, hs.2⟩
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        have : ((R.filter (fun s => d ∣ s)).filter (fun s => s ≤ N)).card ≤ N := by omega
        exact_mod_cast this
    _ = C * (N : ℝ) := by ring

/-- **The y-space coefficient vanishes above the level.** For `d > N` (and `N ≥ 2`), the support
cutoff forces every surviving divisor `s` (with `d ∣ s`, `s ≥ d > N`) to have `F (log s/log N) = 0`,
so `yLambda R F (log N) d = 0`. Combined with `abs_yLambda_le_level` this confines the coefficient's
support to `d ≤ N`. -/
theorem yLambda_eq_zero_of_gt_level (R : Finset ℕ) (F : ℝ → ℝ) (N d : ℕ)
    (hN : 2 ≤ N) (hd : N < d) (hFcut : ∀ t, 1 < t → F t = 0) (hR1 : ∀ s ∈ R, 1 ≤ s) :
    S1YSpace.yLambda R F (Real.log N) d = 0 := by
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  unfold S1YSpace.yLambda
  rw [Finset.sum_eq_zero, mul_zero]
  intro s hs
  rw [Finset.mem_filter] at hs
  have hsR : s ∈ R := hs.1
  have hds : d ∣ s := hs.2
  have hs1 : 1 ≤ s := hR1 s hsR
  have hsd : d ≤ s := Nat.le_of_dvd (by omega) hds
  have hsgt : (N : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : N < s)
  have hlogs : Real.log N < Real.log s :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < N)) hsgt
  have hgt1 : 1 < Real.log s / Real.log N := by rw [lt_div_iff₀ hlogN]; linarith
  rw [hFcut _ hgt1]; simp

/-- **x-independent polynomial bound on the y-space coefficient `ℓ¹`-mass.** Summed over the whole
(arbitrarily large) candidate set `R`, the absolute y-space coefficients satisfy
`∑_{d∈R} |yLambda R F (log N) d| ≤ C·N³` — a fixed polynomial in the level `N`, **independent of the
sieve scale `x`** (which controls `|R|`). The coefficient vanishes for `d > N`
(`yLambda_eq_zero_of_gt_level`) and is `≤ d·C·N ≤ C·N²` for `d ≤ N` (`abs_yLambda_le_level`), and at
most `N` values of `d ≤ N` occur. This is the elementary, PNT-free `λ_max`-type control that — with a
scale `x` taken polynomially large in `N` — drives the *diagonal* leg of the s1 correction to
`o(B^{+k}·M)` with NO Möbius cancellation / no PNT. The expensive cancellation (the lap-8 "smoothing"
estimate) is only needed for the *off-diagonal* leg, where the `M` factor cancels against the main
term and the scale trick does not apply. -/
theorem sum_abs_yLambda_le_level (R : Finset ℕ) (F : ℝ → ℝ) (N : ℕ) (C : ℝ)
    (hN : 2 ≤ N) (hC : ∀ t, |F t| ≤ C) (hFcut : ∀ t, 1 < t → F t = 0)
    (hR1 : ∀ s ∈ R, 1 ≤ s) :
    ∑ d ∈ R, |S1YSpace.yLambda R F (Real.log N) d| ≤ C * (N : ℝ) ^ 3 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  classical
  have key : ∀ d ∈ R, |S1YSpace.yLambda R F (Real.log N) d|
      ≤ (if d ≤ N then C * (N : ℝ) ^ 2 else 0) := by
    intro d hd
    by_cases hdN : d ≤ N
    · rw [if_pos hdN]
      refine le_trans (abs_yLambda_le_level R F N d C hN hC hFcut hR1) ?_
      have hdNr : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      calc (d : ℝ) * C * (N : ℝ) ≤ (N : ℝ) * C * (N : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hdNr hC0
        _ = C * (N : ℝ) ^ 2 := by ring
    · rw [if_neg hdN, yLambda_eq_zero_of_gt_level R F N d hN (by omega) hFcut hR1, abs_zero]
  calc ∑ d ∈ R, |S1YSpace.yLambda R F (Real.log N) d|
      ≤ ∑ d ∈ R, (if d ≤ N then C * (N : ℝ) ^ 2 else 0) := Finset.sum_le_sum key
    _ = ∑ d ∈ R.filter (fun d => d ≤ N), C * (N : ℝ) ^ 2 := (Finset.sum_filter _ _).symm
    _ = (R.filter (fun d => d ≤ N)).card • (C * (N : ℝ) ^ 2) := Finset.sum_const _
    _ ≤ (N : ℝ) * (C * (N : ℝ) ^ 2) := by
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hsub : R.filter (fun d => d ≤ N) ⊆ Finset.Icc 1 N := by
          intro d hd
          rw [Finset.mem_filter] at hd
          exact Finset.mem_Icc.mpr ⟨hR1 d hd.1, hd.2⟩
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Icc] at hcard
        have : (R.filter (fun d => d ≤ N)).card ≤ N := by omega
        exact_mod_cast this
    _ = C * (N : ℝ) ^ 3 := by ring

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

/-- **Diagonal `O(1)` count error (the `herr` leg, UNCONDITIONAL).** For a diagonal tuple `P`
(pairwise-coprime moduli `lcm(P i)`, each positive and `W`-coprime), the sieve count differs from
the lattice main density `M/∏[dᵢ,eᵢ]` — with `M = (⌊2x⌋−(⌈x⌉−1))/W` the exact lattice density — by at
most `1`. Composes `sieve_count_eq_lattice_count` (Icc→Ioc, two moduli → lcm) with
`SieveExpansion.lattice_count_main_term` (CRT count, single modulus). This is the `herr` hypothesis of
`yspace_correction_abs_bound`, now discharged from natural diagonal hypotheses — pure lattice
geometry, **no BV**. (The cross-coordinate coprimality `hdiag` ⟹ pairwise-coprime moduli via
`List.Nodup.pairwise_of_forall_ne`; the `W`-coprimality and positivity come from the candidate set.) -/
theorem yspace_diag_count_err (k : ℕ) (H : List ℕ) (b W : ℕ) (x : ℝ) (hx : 0 < x) (hW : 0 < W)
    (hAB : ⌈x⌉₊ - 1 ≤ ⌊2 * x⌋₊) (P : Fin k → ℕ × ℕ)
    (hpos : ∀ i, 0 < Nat.lcm (P i).1 (P i).2)
    (hcopW : ∀ i, Nat.Coprime (Nat.lcm (P i).1 (P i).2) W)
    (hdiag : ∀ i j : Fin k, i ≠ j →
      Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)) :
    |((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
        (fun m => ∀ i : Fin k,
          (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card : ℝ)
      - ((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)
          / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)| ≤ 1 := by
  rw [sieve_count_eq_lattice_count k H b W x hx P]
  have hco : (List.finRange k).Pairwise
      (fun i j => Nat.Coprime (Nat.lcm (P i).1 (P i).2) (Nat.lcm (P j).1 (P j).2)) :=
    (List.nodup_finRange k).pairwise_of_forall_ne (fun a _ b _ hab => hdiag a b hab)
  have hqpos : ∀ i ∈ List.finRange k, 0 < Nat.lcm (P i).1 (P i).2 := fun i _ => hpos i
  have hlistprod :
      ((List.finRange k).map (fun i => Nat.lcm (P i).1 (P i).2)).prod
        = ∏ i : Fin k, Nat.lcm (P i).1 (P i).2 := by
    rw [← List.ofFn_eq_map, List.prod_ofFn]
  have hWcop : Nat.Coprime W
      (((List.finRange k).map (fun i => Nat.lcm (P i).1 (P i).2)).prod) := by
    rw [hlistprod]
    exact Nat.Coprime.prod_right (fun i _ => (hcopW i).symm)
  have hmaineq : ((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)
        / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)
      = ((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ))
          / ((W * ((List.finRange k).map (fun i => Nat.lcm (P i).1 (P i).2)).prod : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hlistprod, Nat.cast_prod, div_div]
  rw [hmaineq]
  have hmain := BoundedGaps.Sieve.lattice_count_main_term (List.finRange k)
    (fun i => Nat.lcm (P i).1 (P i).2) (fun i => H.getD i.val 0) W b
    (⌈x⌉₊ - 1) ⌊2 * x⌋₊ hco hqpos hWcop hW hAB
  convert hmain using 6

/-- **The y-space S1 correction bound with the diagonal error DISCHARGED (no `herr` hypothesis).**
Specialises `yspace_correction_abs_bound` to the exact lattice density `M = (⌊2x⌋−(⌈x⌉−1))/W` and
discharges `herr` internally via `yspace_diag_count_err` (positivity + `W`-coprimality of the diagonal
moduli come from the candidate set; the diagonal pairwise-coprimality is the filter predicate). So the
y-space correction is bounded, **with no BV and no count-side hypothesis** (only the W-trick
admissibility `hWdvd`/`hshift_le`/`hshift_ne` + `hAB`), by
`∑_{diag}|∏λλ| + ∑_{¬diag}|∏λλ|·(M/∏[dᵢ,eᵢ])`. Both count-side obligations of the s1 off-diagonal
correction (the off-diagonal vanishing AND the diagonal `O(1)` error) are now machine-checked
unconditionally. The remaining work to `hcorr` (`correction = o(main)`) is the two purely-analytic SIZE
estimates on the RHS sums (diagonal via `abs_yLambda_le` + `S1DiagonalSize`; off-diagonal via the
`∑_{p>D₀}1/p²` tail of `S1OffDiagSize`). -/
theorem yspace_correction_abs_bound_explicit {k : ℕ} (Fs : Fin k → ℝ → ℝ) (H : List ℕ)
    (b W : ℕ) (x R : ℝ) (D₀ : ℕ) (hx : 0 < x) (hW : 0 < W)
    (hAB : ⌈x⌉₊ - 1 ≤ ⌊2 * x⌋₊)
    (hWdvd : ∀ p, p.Prime → p ≤ D₀ → p ∣ W)
    (hshift_le : ∀ i : Fin k, H.getD i.val 0 ≤ D₀)
    (hshift_ne : ∀ i j : Fin k, i ≠ j → H.getD i.val 0 ≠ H.getD j.val 0) :
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
              - (((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
                  / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))|
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
            * ((((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ))
                / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)) := by
  have hMnonneg : (0:ℝ) ≤ ((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ) := by
    apply div_nonneg _ (by positivity)
    have : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast hAB
    linarith
  refine yspace_correction_abs_bound Fs H b W x R
    (((⌊2 * x⌋₊ : ℝ) - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) / (W : ℝ)) D₀ hMnonneg hWdvd hshift_le hshift_ne ?_
  intro P hP
  rw [Finset.mem_filter] at hP
  obtain ⟨hPmem, hdiagP⟩ := hP
  have hmem := Fintype.mem_piFinset.mp hPmem
  have hyhyp := fun (i : Fin k) => BoundedGaps.Sieve.sieveDivisors_yspace_hyps H i.val b W x
  have hpos : ∀ i, 0 < Nat.lcm (P i).1 (P i).2 := by
    intro i
    have h2 := Finset.mem_product.mp (hmem i)
    have h1a : 1 ≤ (P i).1 := (hyhyp i).1 (P i).1 h2.1
    have h1b : 1 ≤ (P i).2 := (hyhyp i).1 (P i).2 h2.2
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hcopW : ∀ i, Nat.Coprime (Nat.lcm (P i).1 (P i).2) W := by
    intro i
    have h2 := Finset.mem_product.mp (hmem i)
    have hc1 := (Finset.mem_filter.mp h2.1).2.2
    have hc2 := (Finset.mem_filter.mp h2.2).2.2
    exact coprime_lcm_of_coprime hc1 hc2
  exact yspace_diag_count_err k H b W x hx hW hAB P hpos hcopW hdiagP

end BoundedGaps.S1Correction
