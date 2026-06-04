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

/-
**CRT combination.** For coprime `W, Q`, the simultaneous condition
`m ≡ b [MOD W] ∧ Q ∣ (m + h)` is a single residue class mod `W*Q`.
-/
theorem crt_combine {W Q : ℕ} (hcop : Nat.Coprime W Q) (hW : 0 < W) (hQ : 0 < Q)
    (b h : ℕ) :
    ∃ r, ∀ m : ℕ, (m ≡ b [MOD W] ∧ Q ∣ (m + h)) ↔ m ≡ r [MOD (W * Q)] := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r ≡ b [MOD W] ∧ r ≡ (Q - h % Q) % Q [MOD Q] := by
    have := Nat.chineseRemainder hcop b ( ( Q - h % Q ) % Q ) ; aesop;
  use r;
  intro m; rw [ ← Nat.modEq_and_modEq_iff_modEq_mul hcop ] ; simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ] ;
  intro hm; constructor <;> intro <;> simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero] ;
  · refine Nat.modEq_of_dvd ?_;
    obtain ⟨ k, hk ⟩ := ‹Q ∣ m + h›; use -k + ( h / Q + 1 ) ; rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ hQ ) ] ; push_cast ; linarith [ Nat.mod_add_div h Q ] ;
  · rw [ Nat.dvd_iff_mod_eq_zero ] ; simp +decide [ *, Nat.add_mod ] ;
    simp +decide [ Nat.add_comm, Nat.add_sub_of_le ( Nat.mod_lt _ hQ |> Nat.le_of_lt ) ]

/-
**CRT interval count with O(1) error.** For coprime `W, Q` and `A ≤ B`, the
number of `m ∈ [A, B]` with `m ≡ b [MOD W]` and `Q ∣ (m + h)` is within `1` of
the expected `(B + 1 - A)/(W*Q)`.
-/
theorem crt_interval_count_bound {W Q : ℕ} (hcop : Nat.Coprime W Q)
    (hW : 0 < W) (hQ : 0 < Q) (b h A B : ℕ) (hAB : A ≤ B) :
    |(((Finset.Icc A B).filter
        (fun m => m ≡ b [MOD W] ∧ Q ∣ (m + h))).card : ℝ)
      - (B + 1 - A : ℝ) / (W * Q)| ≤ 1 := by
  rw [ abs_le ];
  obtain ⟨ r, hr ⟩ := crt_combine hcop hW hQ b h;
  -- Let's count the number of elements in the set {m ∈ Finset.Icc A B | m ≡ r [MOD (W * Q)]}.
  have h_count : Finset.card (Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.Icc A B)) = Finset.card (Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range (B + 1))) - Finset.card (Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range A)) := by
    have h_count : Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.Icc A B) = Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range (B + 1)) \ Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range A) := by
      grind;
    grind;
  -- Let's count the number of elements in the set {m ∈ Finset.range n | m ≡ r [MOD (W * Q)]}.
  have h_count_range : ∀ n : ℕ, Finset.card (Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range n)) = (n + (W * Q - r % (W * Q) - 1)) / (W * Q) := by
    intro n
    have h_count_range : Finset.filter (fun m => m ≡ r [MOD (W * Q)]) (Finset.range n) = Finset.image (fun m => m * (W * Q) + (r % (W * Q))) (Finset.range ((n + (W * Q - r % (W * Q) - 1)) / (W * Q))) := by
      ext m; simp [Finset.mem_image];
      constructor;
      · intro hm
        obtain ⟨a, ha⟩ : ∃ a, m = a * (W * Q) + (r % (W * Q)) := by
          exact ⟨ m / ( W * Q ), by linarith [ Nat.mod_add_div m ( W * Q ), show m % ( W * Q ) = r % ( W * Q ) from hm.2 ] ⟩;
        refine' ⟨ a, _, ha.symm ⟩;
        rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ] <;> nlinarith [ Nat.sub_add_cancel ( show r % ( W * Q ) ≤ W * Q from Nat.le_of_lt ( Nat.mod_lt _ ( by positivity ) ) ), Nat.sub_add_cancel ( show 1 ≤ W * Q - r % ( W * Q ) from Nat.sub_pos_of_lt ( Nat.mod_lt _ ( by positivity ) ) ) ];
      · rintro ⟨ a, ha, rfl ⟩;
        rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ] at ha <;> try nlinarith;
        exact ⟨ by nlinarith [ Nat.sub_add_cancel ( show r % ( W * Q ) ≤ W * Q from Nat.le_of_lt ( Nat.mod_lt _ ( by positivity ) ) ), Nat.sub_add_cancel ( show 1 ≤ W * Q - r % ( W * Q ) from Nat.sub_pos_of_lt ( Nat.mod_lt _ ( by positivity ) ) ) ], by simp +decide [ Nat.ModEq, Nat.add_mod, Nat.mod_eq_of_lt ( show r % ( W * Q ) < W * Q from Nat.mod_lt _ ( by positivity ) ) ] ⟩;
    rw [ h_count_range, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hW.ne', hQ.ne' ];
  simp_all +decide;
  rw [ Nat.cast_sub ];
  · rw [ div_le_iff₀, le_iff_lt_or_eq ];
    · constructor;
      · refine' lt_or_eq_of_le ( _ : _ ≤ _ );
        norm_cast;
        rw [ Int.subNatNat_eq_coe, Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.div_add_mod ( B + 1 + ( W * Q - r % ( W * Q ) - 1 ) ) ( W * Q ), Nat.mod_lt ( B + 1 + ( W * Q - r % ( W * Q ) - 1 ) ) ( by positivity : 0 < ( W * Q ) ), Nat.div_mul_le_self ( A + ( W * Q - r % ( W * Q ) - 1 ) ) ( W * Q ) ];
      · rw [ add_div', le_div_iff₀ ] <;> norm_cast <;> try positivity;
        rw [ Int.subNatNat_eq_coe, Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.div_mul_le_self ( B + 1 + ( W * Q - r % ( W * Q ) - 1 ) ) ( W * Q ), Nat.div_add_mod ( A + ( W * Q - r % ( W * Q ) - 1 ) ) ( W * Q ), Nat.mod_lt ( A + ( W * Q - r % ( W * Q ) - 1 ) ) ( by positivity : 0 < ( W * Q ) ), Nat.sub_add_cancel ( show 1 ≤ W * Q - r % ( W * Q ) from Nat.sub_pos_of_lt ( Nat.mod_lt _ ( by positivity ) ) ) ];
    · positivity;
  · exact Nat.div_le_div_right ( by linarith )