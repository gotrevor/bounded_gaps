import Mathlib

open scoped BigOperators

/-!
# Sub-step (b) of the GPY/Maynard sieve `s1` asymptotic: the CRT interval count.

Goal: count the integers `m` in an interval `[A, B]` lying in a residue class
`m ≡ b (mod W)` AND satisfying a shifted divisibility `Q ∣ (m + h)`, when
`W` and `Q` are coprime. By CRT this is a single residue class mod `W*Q`, so the
count is the interval length over `W*Q`, up to an O(1) boundary error.

Two targets. `crt_combine` is the pure CRT step (likely the harder lemma);
`crt_interval_count_bound` is the count estimate it feeds. Mathlib HAS the
ingredients: `Nat.chineseRemainder`, `Nat.modEq_and_modEq_iff_modEq_mul`,
`Nat.Ico_filter_modEq_card` / `Nat.Ioc_filter_modEq_card`
(`Mathlib/Data/Int/CardIntervalMod.lean`,`Mathlib/Data/Nat/ModEq.lean`).
Prove BOTH `sorry`s. Keep everything `#print axioms`-clean (no new axioms).
-/

/-- **CRT combination.** For coprime `W, Q`, the simultaneous condition
`m ≡ b [MOD W] ∧ Q ∣ (m + h)` is a single residue class mod `W*Q`. -/
theorem crt_combine {W Q : ℕ} (hcop : Nat.Coprime W Q) (hW : 0 < W) (hQ : 0 < Q)
    (b h : ℕ) :
    ∃ r, ∀ m : ℕ, (m ≡ b [MOD W] ∧ Q ∣ (m + h)) ↔ m ≡ r [MOD (W * Q)] := by
  sorry

/-- **CRT interval count with O(1) error.** For coprime `W, Q` and `A ≤ B`, the
number of `m ∈ [A, B]` with `m ≡ b [MOD W]` and `Q ∣ (m + h)` is within `1` of
the expected `(B + 1 - A)/(W*Q)`. -/
theorem crt_interval_count_bound {W Q : ℕ} (hcop : Nat.Coprime W Q)
    (hW : 0 < W) (hQ : 0 < Q) (b h A B : ℕ) (hAB : A ≤ B) :
    |(((Finset.Icc A B).filter
        (fun m => m ≡ b [MOD W] ∧ Q ∣ (m + h))).card : ℝ)
      - (B + 1 - A : ℝ) / (W * Q)| ≤ 1 := by
  sorry
