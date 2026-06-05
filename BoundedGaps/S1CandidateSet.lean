/-
# Candidate-set inclusion for the count→`M` reconciliation (the "delicate bit")

The separable y-space sieve weight `selberg_nu_yr_sep` diagonalises (after the count→`M` density step)
to a coordinate sum over `Rset_i = sieveDivisors_i.filter (sf ∧ (·,W)=1)` — the squarefree
`W`-coprime divisors that *actually appear* in the sieve interval `[⌈x⌉, ⌊2x⌋]`. The contour-free
limit `S1YSpace.yspace_sieve_quadform_tendsto`, by contrast, sums over the clean index set
`{r ≤ N : sf ∧ (r,W)=1}`. Reconciling them needs: every small squarefree `W`-coprime `r` (those `≤ R`
with `W·r` no larger than the interval) genuinely appears as a divisor — i.e.
`{r : sf ∧ (r,W)=1 ∧ W·r ≤ |interval|} ⊆ Rset_i`.

This file proves that inclusion. The crux is a Chinese-remainder existence: for `(W,r)=1` the joint
congruence `n ≡ b (mod W)`, `n ≡ -hᵢ (mod r)` has a solution mod `W·r`, and any interval at least
`W·r` long contains a representative — so `r ∣ (n+hᵢ)` for some `n` in the residue class of the
interval. Pure combinatorics / number theory: unconditional, no BV, no analysis. It is the
candidate-set inclusion half of the count→`M` obligation (the off-diagonal `o(main)` correction is
the separate, BV-gated half).
-/
import BoundedGaps.SieveExpansion

open scoped BigOperators
open ArithmeticFunction (moebius)

namespace BoundedGaps.S1CandidateSet

/-- **Candidate-set existence (CRT).** If `(W,r)=1` and the interval `[A,B]` is at least `W·r` long,
then it contains an `n` in the residue class `b (mod W)` with `r ∣ n+h`. Chinese remainder gives a
solution mod `W·r`; the representative `k + W·r·⌊(B-k)/(W·r)⌋` lands in `[A,B]`. -/
theorem exists_n_interval_crt (A B W r h b : ℕ) (hW : 1 ≤ W) (hr : 1 ≤ r)
    (hcop : Nat.Coprime W r) (hAB : A ≤ B) (hlen : W * r ≤ B - A + 1) :
    ∃ n, A ≤ n ∧ n ≤ B ∧ n % W = b % W ∧ r ∣ (n + h) := by
  have hm_pos : 0 < W * r := Nat.mul_pos hW hr
  have hk_lt : (Nat.chineseRemainder hcop b ((r - h % r) % r) : ℕ) < W * r :=
    Nat.chineseRemainder_lt_mul hcop _ _ (by omega) (by omega)
  have hkW := (Nat.chineseRemainder hcop b ((r - h % r) % r)).prop.1
  have hkr := (Nat.chineseRemainder hcop b ((r - h % r) % r)).prop.2
  set k := (Nat.chineseRemainder hcop b ((r - h % r) % r) : ℕ) with hk
  set wr := W * r with hwr
  refine ⟨k + wr * ((B - k) / wr), ?_, ?_, ?_, ?_⟩
  · -- A ≤ n
    have hdm := Nat.div_add_mod (B - k) wr
    have hmod : (B - k) % wr < wr := Nat.mod_lt _ hm_pos
    set P := wr * ((B - k) / wr) with hP
    omega
  · -- n ≤ B
    have hle : wr * ((B - k) / wr) ≤ B - k := Nat.mul_div_le (B - k) wr
    omega
  · -- n % W = b % W
    have hmod : (k + wr * ((B - k) / wr)) % W = k % W := by
      rw [hwr, mul_assoc, Nat.add_mul_mod_self_left]
    rw [hmod]; exact hkW
  · -- r ∣ n + h
    have hnr : (k + wr * ((B - k) / wr)) % r = k % r := by
      rw [hwr, show W * r = r * W from Nat.mul_comm W r, mul_assoc, Nat.add_mul_mod_self_left]
    have hmr : h % r ≤ r := le_of_lt (Nat.mod_lt _ (by omega))
    have key : (k + wr * ((B - k) / wr)) + h ≡ 0 [MOD r] := by
      calc (k + wr * ((B - k) / wr)) + h
          ≡ k + h [MOD r] := Nat.ModEq.add_right h hnr
        _ ≡ ((r - h % r) % r) + h [MOD r] := Nat.ModEq.add_right h hkr
        _ ≡ (r - h % r) + h [MOD r] := Nat.ModEq.add_right h (Nat.mod_modEq _ _)
        _ ≡ (r - h % r) + h % r [MOD r] := Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
        _ = r := Nat.sub_add_cancel hmr
        _ ≡ 0 [MOD r] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
    exact (Nat.modEq_zero_iff_dvd).mp key

/-- **Candidate-set membership.** Every `r ≥ 1` coprime to `W`, with `W·r` no larger than the
interval length `⌊2x⌋ - ⌈x⌉ + 1`, divides some `n+hᵢ` in the residue class `b (mod W)` of the sieve
interval `[⌈x⌉, ⌊2x⌋]` — hence `r ∈ sieveDivisors H i b W x`. So every small modulus genuinely
appears in the y-space sieve: it is the candidate-set inclusion half of the
count→`M` reconciliation). -/
theorem mem_sieveDivisors_of_coprime (H : List ℕ) (i b W : ℕ) (x : ℝ) (r : ℕ)
    (hx : 0 < x) (hr : 1 ≤ r) (hW : 1 ≤ W) (hcop : Nat.Coprime r W)
    (hAB : ⌈x⌉₊ ≤ ⌊2 * x⌋₊) (hlen : W * r ≤ ⌊2 * x⌋₊ - ⌈x⌉₊ + 1) :
    r ∈ BoundedGaps.Sieve.sieveDivisors H i b W x := by
  obtain ⟨n, hAn, hnB, hnW, hdvd⟩ :=
    exists_n_interval_crt ⌈x⌉₊ ⌊2 * x⌋₊ W r (H.getD i 0) b hW hr hcop.symm hAB hlen
  have hxceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
  rw [BoundedGaps.Sieve.sieveDivisors, Finset.mem_biUnion]
  refine ⟨n, ?_, ?_⟩
  · rw [Finset.mem_filter]; exact ⟨Finset.mem_Icc.mpr ⟨hAn, hnB⟩, hnW⟩
  · rw [Nat.mem_divisors]; exact ⟨hdvd, by omega⟩

/-- **Candidate-set inclusion (subset form).** When the sieve interval is at least `W·N` long, the
clean diagonalisation index `{r ≤ N : sf ∧ (r,W)=1}` is contained in the actual candidate set
`Rset_i = sieveDivisors_i.filter (sf ∧ (·,W)=1)`. This is the inclusion the count→`M` reconciliation
consumes: it lets the y-space coordinate sum over the appearing divisors be compared term-by-term to
the contour-free limit's sum over all small `r` (`S1YSpace.yspace_sieve_quadform_tendsto`). -/
theorem filter_Icc_subset_filter_sieveDivisors (H : List ℕ) (i b W N : ℕ) (x : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hAB : ⌈x⌉₊ ≤ ⌊2 * x⌋₊)
    (hlenN : W * N ≤ ⌊2 * x⌋₊ - ⌈x⌉₊ + 1) :
    ((Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W))
      ⊆ (BoundedGaps.Sieve.sieveDivisors H i b W x).filter
          (fun r => Squarefree r ∧ Nat.Coprime r W) := by
  intro r hr
  rw [Finset.mem_filter, Finset.mem_Icc] at hr
  obtain ⟨⟨hr1, hrN⟩, hsf, hcop⟩ := hr
  rw [Finset.mem_filter]
  refine ⟨mem_sieveDivisors_of_coprime H i b W x r hx hr1 hW hcop hAB ?_, hsf, hcop⟩
  calc W * r ≤ W * N := by gcongr
    _ ≤ ⌊2 * x⌋₊ - ⌈x⌉₊ + 1 := hlenN

/-- **Sieve interval length bound.** For `x ≥ 2`, the sieve interval `[⌈x⌉, ⌊2x⌋]` is nonempty and at
least `x - 2` long (`⌈x⌉ < x+1`, `2x < ⌊2x⌋+1`). -/
theorem sieve_interval_lower_bound (x : ℝ) (hx : 2 ≤ x) :
    ⌈x⌉₊ ≤ ⌊2 * x⌋₊ ∧ x - 2 ≤ (⌊2 * x⌋₊ : ℝ) - ⌈x⌉₊ := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hfloor : 2 * x < (⌊2 * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 * x)
  have hlt : (⌈x⌉₊ : ℝ) < (⌊2 * x⌋₊ : ℝ) := by linarith
  refine ⟨?_, by linarith⟩
  exact_mod_cast le_of_lt hlt

/-- **Sieve interval covers `[1,N]` for `x` large.** For `x ≥ W·N + 2`, the interval `[⌈x⌉, ⌊2x⌋]` is
nonempty and `≥ W·N` long — exactly the `(hAB, hlenN)` hypotheses of
`filter_Icc_subset_filter_sieveDivisors`. So for `x` large the clean diagonalisation index
`{r ≤ N : sf ∧ (r,W)=1}` sits inside `Rset_i`; this ties the candidate-set inclusion to the `x→∞`
regime the sieve asymptotic runs in (with the sieve level `N = R(x)`). -/
theorem sieve_interval_covers (x : ℝ) (W N : ℕ) (hx : (W * N : ℝ) + 2 ≤ x) :
    ⌈x⌉₊ ≤ ⌊2 * x⌋₊ ∧ W * N ≤ ⌊2 * x⌋₊ - ⌈x⌉₊ + 1 := by
  have hWN : (0:ℝ) ≤ (W * N : ℕ) := by positivity
  have hx2 : (2:ℝ) ≤ x := by
    have : ((W * N : ℕ) : ℝ) = (W * N : ℝ) := by push_cast; ring
    linarith [hx, hWN]
  obtain ⟨hAB, hlen⟩ := sieve_interval_lower_bound x hx2
  refine ⟨hAB, ?_⟩
  have hcast : ((⌊2 * x⌋₊ - ⌈x⌉₊ : ℕ) : ℝ) = (⌊2 * x⌋₊ : ℝ) - ⌈x⌉₊ := by
    rw [Nat.cast_sub hAB]
  have hreal : ((W * N : ℕ) : ℝ) ≤ ((⌊2 * x⌋₊ - ⌈x⌉₊ : ℕ) : ℝ) := by
    rw [hcast]
    have : ((W * N : ℕ) : ℝ) = (W * N : ℝ) := by push_cast; ring
    linarith [hx, hlen]
  have hN : W * N ≤ ⌊2 * x⌋₊ - ⌈x⌉₊ := by exact_mod_cast hreal
  omega

/-- **Coordinate-sum restriction to the clean index.** The y-space coordinate diagonal sum over the
candidate set `Rset` (the divisors that appear) equals the sum over the clean index
`{r ≤ N : sf ∧ (r,W)=1}`, provided (i) `{r≤N: sf∧(r,W)=1} ⊆ Rset` (every small `r` appears —
`filter_Icc_subset_filter_sieveDivisors`), (ii) `Rset` carries the `sf∧(r,W)=1` predicate, and
(iii) `F` vanishes above `1` with `N ≥ ⌊R⌋` (so divisors `r > N`, i.e. `r > R`, give
`F(log r/log R) = 0`). This bridges `S1YSpace.yr_coord_factor_eq_muphi` (sum over `Rset_i`) to the
contour-free limit `S1YSpace.yspace_sieve_quadform_tendsto` (sum over `{r≤N: sf∧(r,W)=1}`). -/
theorem coord_sum_restrict_to_Icc {W : ℕ} (Rset : Finset ℕ) (F : ℝ → ℝ) (R : ℝ) (N : ℕ)
    (hR : 1 < R) (hNR : R < (N : ℝ) + 1)
    (hFsupp : ∀ t : ℝ, 1 < t → F t = 0)
    (hsub : (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W) ⊆ Rset)
    (hRsf : ∀ r ∈ Rset, Squarefree r ∧ Nat.Coprime r W) :
    (∑ r ∈ Rset, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / Real.log R) ^ 2)
      = ∑ r ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / Real.log R) ^ 2 := by
  symm
  apply Finset.sum_subset hsub
  intro r hrRset hrnotIcc
  obtain ⟨hsf, hcop⟩ := hRsf r hrRset
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hsf.ne_zero
  have hrN : N < r := by
    by_contra h
    exact hrnotIcc
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, Nat.le_of_not_lt h⟩, hsf, hcop⟩)
  have hrR : R < (r : ℝ) := by
    have : (N : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hrN
    linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlogr : Real.log R < Real.log r := Real.log_lt_log (by linarith) hrR
  have hgt1 : 1 < Real.log r / Real.log R := by
    rw [lt_div_iff₀ hlogR]; linarith
  rw [hFsupp _ hgt1]; ring

end BoundedGaps.S1CandidateSet
