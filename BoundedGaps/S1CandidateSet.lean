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
interval `[⌈x⌉, ⌊2x⌋]` — hence `r ∈ sieveDivisors H i b W x`. So `{r : sf ∧ (r,W)=1 ∧ small} ⊆ Rset`:
every small modulus genuinely appears in the y-space sieve (the candidate-set inclusion half of the
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

end BoundedGaps.S1CandidateSet
