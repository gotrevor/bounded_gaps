/-
# Basic definitions for the bounded-gaps project.

Admissible k-tuples, narrowness $H(k)$, $\liminf$ prime-gap notation $H_m$,
the DHL[k, j] predicate, and bridge lemmas between the literature's
$\liminf$-style statements and our set-infinite encoding.

Literature notation: $H_m \coloneqq \liminf_{n \to \infty} (p_{n+m} - p_n)$.

See [../papers/README.md](../papers/README.md) for source PDFs and LaTeX.
-/
import Mathlib

namespace BoundedGaps

open Filter

/-! ### Admissible k-tuples (Polymath8b §3 / Maynard §2) -/

/-- A list $\mathcal{H} = (h_1, \ldots, h_k)$ of strictly increasing integers
is **admissible** iff for every prime $p$, the offsets miss at least one
residue class mod $p$. Equivalently, no prime $p$ is forced to divide one of
the shifted primes $n + h_i$. -/
def Admissible (H : List ℕ) : Prop :=
  H.Pairwise (· < ·) ∧
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The "shifted set" $\{n + h : h \in \mathcal{H}\}$. -/
def shiftedSet (n : ℕ) (H : List ℕ) : Set ℕ := { m | ∃ h ∈ H, m = n + h }

/-- The diameter $h_k - h_1$ of a $k$-tuple. Defined to be 0 on lists with
fewer than two elements; meaningful only for admissible k-tuples with $k \ge 2$. -/
def diameter (H : List ℕ) : ℕ :=
  H.foldr max 0 - H.foldr min (H.foldr max 0)

/-- **Narrowness $H(k)$** (Polymath8b §3): the minimal diameter over all
admissible $k$-tuples. Polymath8b Theorem 3.2 establishes:
- $H(3) = 6$
- $H(50) = 246$, $H(51) = 252$, $H(54) = 270$
- $H(k) \le k \log k + k \log\log k - k + o(k)$ as $k \to \infty$
- (Brun-Titchmarsh) $H(k) \ge (\tfrac12 + o(1)) k \log k$ -/
noncomputable def narrowness (k : ℕ) : ℕ :=
  sInf { d | ∃ H : List ℕ, Admissible H ∧ H.length = k ∧ diameter H = d }

/-! ### Pigeonhole reduction: admissibility on finitely many primes is enough -/

/-- **Pigeonhole**: if $H$ has fewer offsets than $p$, then the offsets cannot
hit every residue class mod $p$. Witness: a class not in the image of $H$. -/
theorem admissible_pigeonhole {H : List ℕ} {p : ℕ} (hp : p.Prime)
    (hp_gt : H.length < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  let cast_p : ℕ → ZMod p := fun n => (n : ZMod p)
  let S : Finset (ZMod p) := H.toFinset.image cast_p
  have hS_card : S.card ≤ H.length := by
    calc S.card
        ≤ H.toFinset.card := Finset.card_image_le
      _ ≤ H.length := List.toFinset_card_le H
  have hS_lt : S.card < Fintype.card (ZMod p) := by
    rw [ZMod.card]; omega
  have hne : S ≠ Finset.univ := by
    intro heq; rw [heq, Finset.card_univ] at hS_lt; exact lt_irrefl _ hS_lt
  rw [Ne, Finset.eq_univ_iff_forall, not_forall] at hne
  obtain ⟨r, hr⟩ := hne
  refine ⟨r, fun h hmem hcontra => hr ?_⟩
  show r ∈ S
  simp only [S, cast_p, Finset.mem_image, List.mem_toFinset]
  exact ⟨h, hmem, hcontra⟩

/-- **Reduction lemma**: a sorted list $H$ is admissible iff some witness
class is missed for every prime $p \le |H|$. The primes $p > |H|$ come for
free by pigeonhole. -/
theorem admissible_of_check_small_primes {H : List ℕ}
    (hsort : H.Pairwise (· < ·))
    (hcheck : ∀ p : ℕ, p.Prime → p ≤ H.length →
              ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) :
    Admissible H := by
  refine ⟨hsort, fun p hp => ?_⟩
  by_cases hpk : p ≤ H.length
  · exact hcheck p hp hpk
  · exact admissible_pigeonhole hp (by omega)

/-- A concrete admissible tuple of size $k$.

Hard-coded for small $k$ (the values we actually reference in named theorems);
falls back to a placeholder `[0]` for larger $k$ so the function is total. -/
def admissibleTuple : ℕ → List ℕ
  | 0     => []
  | 1     => [0]
  | 2     => [0, 2]      -- diameter 2; admissible
  | 3     => [0, 2, 6]   -- the optimal $H(3) = 6$ tuple
  | _ + 4 => [0]         -- placeholder for k ≥ 4

@[simp] theorem admissibleTuple_length_0 : (admissibleTuple 0).length = 0 := rfl
@[simp] theorem admissibleTuple_length_1 : (admissibleTuple 1).length = 1 := rfl
@[simp] theorem admissibleTuple_length_2 : (admissibleTuple 2).length = 2 := rfl
@[simp] theorem admissibleTuple_length_3 : (admissibleTuple 3).length = 3 := rfl

/-- Length result: true for $k \le 3$ (by `rfl` on each case), but the
fallback definition for $k \ge 4$ has length 1, so the unconditional `=k`
statement holds only on $\{0,1,2,3\}$. -/
theorem admissibleTuple_length (k : ℕ) (hk : k ≤ 3) :
    (admissibleTuple k).length = k := by
  interval_cases k <;> rfl

/-- The tuple $(0, 2, 6)$ is admissible: misses class 1 mod 2, class 1 mod 3,
class 3 mod 5. For $p \ge 7$, pigeonhole closes it (3 offsets, $\ge 7$ classes). -/
theorem admissibleTuple_3_admissible : Admissible (admissibleTuple 3) := by
  apply admissible_of_check_small_primes
  · change List.Pairwise (· < ·) [0, 2, 6]
    decide
  · -- Check primes ≤ 3 (i.e., p = 2, 3): finite check by decide.
    intro p hp hple
    have : (admissibleTuple 3).length = 3 := admissibleTuple_length_3
    rw [this] at hple
    have hp2 := hp.two_le
    interval_cases p
    · refine ⟨1, ?_⟩; decide
    · refine ⟨1, ?_⟩; decide

/-- Generic admissibility for all $k$. The function `admissibleTuple` returns
either the optimal small tuple ($k \in \{0,1,2,3\}$) or the fallback `[0]`
($k \ge 4$); both are admissible. Single-element and empty lists are
admissible by pigeonhole (length $<$ every prime); $[0, 2]$ needs an
explicit mod-2 check (residues $\{0,0\}$ miss class 1). -/
theorem admissibleTuple_admissible : ∀ k : ℕ, Admissible (admissibleTuple k)
  | 0 => by
      refine ⟨List.Pairwise.nil, ?_⟩
      intro p _hp
      exact ⟨0, fun _ h => nomatch h⟩
  | 1 => by
      refine admissible_of_check_small_primes (by decide) ?_
      intro p hp hple
      exfalso
      have hp2 := hp.two_le
      have hlen : (admissibleTuple 1).length = 1 := rfl
      omega
  | 2 => by
      refine admissible_of_check_small_primes (by decide) ?_
      intro p hp hple
      have hlen : (admissibleTuple 2).length = 2 := rfl
      rw [hlen] at hple
      have hp2 := hp.two_le
      interval_cases p
      refine ⟨1, ?_⟩; decide
  | 3 => admissibleTuple_3_admissible
  | n + 4 => by
      change Admissible [0]
      refine admissible_of_check_small_primes (by decide) ?_
      intro p hp hple
      exfalso
      have hp2 := hp.two_le
      simp at hple
      omega

/-- $H(3) \le 6$: the tuple $(0, 2, 6)$ is admissible (by
`admissibleTuple_3_admissible`), has length 3, and diameter 6, so the
infimum is $\le 6$. The matching lower bound $H(3) \ge 6$ requires ruling out
admissible 3-tuples of diameter $\le 5$ by case analysis — left as a separate
theorem. -/
theorem narrowness_3_le_six : narrowness 3 ≤ 6 := by
  unfold narrowness
  apply Nat.sInf_le
  refine ⟨[0, 2, 6], admissibleTuple_3_admissible, ?_, ?_⟩
  · rfl
  · decide

/-- **Generic narrowness upper bound**: any admissible $k$-tuple of diameter
$d$ witnesses `narrowness k ≤ d`. The infimum is at most any specific value
that the witness predicate achieves. -/
theorem narrowness_le_of_admissible_tuple {H : List ℕ} {k d : ℕ}
    (hAdm : Admissible H) (hLen : H.length = k) (hDiam : diameter H = d) :
    narrowness k ≤ d := by
  unfold narrowness
  apply Nat.sInf_le
  exact ⟨H, hAdm, hLen, hDiam⟩

/-! ### Shift-invariance of admissibility

Translation by `n : ℕ` is an additive bijection on `ZMod p` for every prime
`p`, so the set of residue classes missed by `H` mod `p` is in bijection
with the set missed by `H.map (· + n)`. Combined with the obvious
preservation of strict ordering, this gives full shift-invariance.

Used for lower-bound proofs on `narrowness k`: an arbitrary admissible
$k$-tuple can be shifted up without loss of generality (the converse
direction lets one shift "back down" too). -/

/-- **Shift-invariance**: `H` is admissible iff its translate `H.map (· + n)`
is admissible, for any `n : ℕ`. -/
theorem admissible_map_add_iff (H : List ℕ) (n : ℕ) :
    Admissible (H.map (· + n)) ↔ Admissible H := by
  refine ⟨?_, ?_⟩
  · -- ←: translate admissible implies original admissible
    rintro ⟨hpair, hres⟩
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_map] at hpair
      exact hpair.imp (fun {a b} h => by omega)
    · intro p hp
      obtain ⟨r, hr⟩ := hres p hp
      refine ⟨r - (n : ZMod p), ?_⟩
      intro h hmem hcontra
      apply hr (h + n) (List.mem_map.mpr ⟨h, hmem, rfl⟩)
      push_cast
      rw [hcontra]
      ring
  · -- →: original admissible implies translate admissible
    rintro ⟨hpair, hres⟩
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_map]
      exact hpair.imp (fun {a b} h => by omega)
    · intro p hp
      obtain ⟨r, hr⟩ := hres p hp
      refine ⟨r + (n : ZMod p), ?_⟩
      intro m hmem hcontra
      rw [List.mem_map] at hmem
      obtain ⟨h, hmem_H, rfl⟩ := hmem
      push_cast at hcontra
      exact hr h hmem_H (add_right_cancel hcontra)

/-- **Key combinatorial lemma**: any admissible 3-tuple $[a, b, c]$ (sorted) has
diameter $c - a \ge 6$.

Strategy: use shift-invariance (`admissible_map_add_iff`) to translate the
tuple down so the first element is 0. Then the problem reduces to: no
admissible tuple `[0, β, δ]` with `0 < β < δ < 6` exists. With `β` and `δ`
ranging over a small finite set, `interval_cases` enumerates all candidates;
in each branch the residues mod 2 and mod 3 are literal numerals, and
`decide` handles the remaining finite check on `ZMod 2 × ZMod 3`. -/
theorem admissible_three_diameter_ge_six
    {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hAdm : Admissible [a, b, c]) : 6 ≤ c - a := by
  by_contra hlt
  push_neg at hlt
  -- Shift to a = 0: set β := b - a, δ := c - a, and witness
  -- [a, b, c] = [0, β, δ].map (· + a), so Admissible [0, β, δ] by shift-invariance.
  set β := b - a with hβ_def
  set δ := c - a with hδ_def
  have hβ_pos : 0 < β := Nat.sub_pos_of_lt hab
  have hδβ : β < δ := by simp [hβ_def, hδ_def]; omega
  have hδ_lt : δ < 6 := by simp [hδ_def]; omega
  have hβ_lt : β < 5 := by omega
  have hShifted : Admissible [0, β, δ] := by
    have hEq : [a, b, c] = ([0, β, δ]).map (· + a) := by
      simp [hβ_def, hδ_def]; omega
    rw [hEq] at hAdm
    exact (admissible_map_add_iff _ a).mp hAdm
  obtain ⟨_, hRes⟩ := hShifted
  obtain ⟨r2, hr2⟩ := hRes 2 Nat.prime_two
  obtain ⟨r3, hr3⟩ := hRes 3 Nat.prime_three
  -- After shifting, residues of the tuple are literal numerals, not a + offset.
  have h2_0 : (0 : ZMod 2) ≠ r2 := hr2 0 (by simp)
  have h2_β : (β : ZMod 2) ≠ r2 := hr2 β (by simp)
  have h2_δ : (δ : ZMod 2) ≠ r2 := hr2 δ (by simp)
  have h3_0 : (0 : ZMod 3) ≠ r3 := hr3 0 (by simp)
  have h3_β : (β : ZMod 3) ≠ r3 := hr3 β (by simp)
  have h3_δ : (δ : ZMod 3) ≠ r3 := hr3 δ (by simp)
  -- Clean up: drop hypotheses still mentioning a, b, c so the goal is closed
  -- over (β, δ, r2, r3) only.
  clear hr2 hr3 hRes hAdm hab hbc hlt hβ_def hδ_def
  -- Enumerate β ∈ {1,...,4}, δ ∈ {β+1,...,5}, then ZMod 2 × ZMod 3 by decide.
  interval_cases β <;> interval_cases δ <;>
    (push_cast at h2_β h2_δ h3_β h3_δ
     revert h2_0 h2_β h2_δ h3_0 h3_β h3_δ r2 r3
     decide)

/-- **$H(3) \ge 6$**: no admissible 3-tuple has diameter less than 6.
The infimum bound follows from `admissible_three_diameter_ge_six` applied to
every admissible length-3 list. -/
theorem narrowness_3_ge_six : 6 ≤ narrowness 3 := by
  unfold narrowness
  apply le_csInf
  · exact ⟨6, [0, 2, 6], admissibleTuple_3_admissible, rfl, by decide⟩
  rintro d ⟨H, hAdm, hLen, rfl⟩
  -- Decompose H = [a, b, c]
  match H, hLen, hAdm with
  | [a, b, c], _, hAdm =>
    -- Extract a < b < c from the pairwise component of admissibility
    have hsort := hAdm.1
    have hab : a < b := by
      have h := List.pairwise_cons.mp hsort
      exact h.1 b (by simp)
    have hbc : b < c := by
      have h1 := List.pairwise_cons.mp hsort
      have h2 := List.pairwise_cons.mp h1.2
      exact h2.1 c (by simp)
    -- diameter [a, b, c] = c - a (when a < b < c)
    have hdiam : diameter [a, b, c] = c - a := by
      unfold diameter
      simp only [List.foldr_cons, List.foldr_nil]
      omega
    rw [hdiam]
    exact admissible_three_diameter_ge_six hab hbc hAdm

/-- **$H(2) \ge 2$**: no admissible 2-tuple has diameter less than 2.

By contradiction, if $b - a < 2$ and $a < b$, then $b = a + 1$. Mod 2 the
two-element tuple becomes $\{\alpha, \alpha + 1\}$ for some $\alpha = (a : \ZMod
2)$, which hits both classes of $\ZMod 2$ — so no residue $r$ can be avoided,
contradicting admissibility at $p = 2$. Mirrors the structure of
`admissible_three_diameter_ge_six`. -/
theorem admissible_two_diameter_ge_two
    {a b : ℕ} (hab : a < b) (hAdm : Admissible [a, b]) : 2 ≤ b - a := by
  by_contra hlt
  push_neg at hlt
  -- a < b and b - a < 2 forces b = a + 1
  have hba1 : b = a + 1 := by omega
  obtain ⟨_, hRes⟩ := hAdm
  obtain ⟨r2, hr2⟩ := hRes 2 Nat.prime_two
  have h2a : (a : ZMod 2) ≠ r2 := hr2 a (by simp)
  have h2b : (b : ZMod 2) ≠ r2 := hr2 b (by simp)
  rw [hba1] at h2b
  push_cast at h2b
  -- Clear residual hypotheses referencing `a, b` so `decide` sees a closed goal.
  clear hr2 hRes hba1 hab hlt
  -- Now h2a : (a : ZMod 2) ≠ r2 and h2b : (a : ZMod 2) + 1 ≠ r2.
  -- Generalize so `decide` can enumerate ZMod 2 × ZMod 2.
  generalize (a : ZMod 2) = α2 at h2a h2b
  revert h2a h2b α2 r2
  decide

/-- **$H(2) \le 2$**: the tuple $(0, 2)$ is admissible (length 2, diameter 2). -/
theorem narrowness_2_le_two : narrowness 2 ≤ 2 :=
  narrowness_le_of_admissible_tuple (admissibleTuple_admissible 2) admissibleTuple_length_2
    (by decide)

/-- **$H(2) \ge 2$**: no admissible 2-tuple has diameter less than 2. -/
theorem narrowness_2_ge_two : 2 ≤ narrowness 2 := by
  unfold narrowness
  apply le_csInf
  · exact ⟨2, [0, 2], admissibleTuple_admissible 2, rfl, by decide⟩
  rintro d ⟨H, hAdm, hLen, rfl⟩
  match H, hLen, hAdm with
  | [a, b], _, hAdm =>
    have hsort := hAdm.1
    have hab : a < b := by
      have h := List.pairwise_cons.mp hsort
      exact h.1 b (by simp)
    have hdiam : diameter [a, b] = b - a := by
      unfold diameter
      simp only [List.foldr_cons, List.foldr_nil]
      omega
    rw [hdiam]
    exact admissible_two_diameter_ge_two hab hAdm

/-! ### Prime gaps and the $H_m$ liminf -/

/-- The $n$-th prime $p_n$. Convention: $p_1 = 2$ (matches Polymath8b §1).

Mathlib's `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth Nat.Prime 0 = 2`), so we
shift by one. Boundary: `primeAt 0 = primeAt 1 = 2` (Nat truncation); harmless
because `liminfGap` is a limit as $n \to \infty$. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- **$H_m = \liminf_{n \to \infty}(p_{n+m} - p_n)$** as a value in $\mathbb{N}_\infty$. -/
noncomputable def liminfGap (m : ℕ) : ℕ∞ :=
  liminf (fun n : ℕ => (primeAt (n + m) - primeAt n : ℕ∞)) atTop

/-! ### The DHL[k, j] family (Polymath8b §3) -/

/-- **Dickson-Hardy-Littlewood predicate** $\DHL[k, j]$: for every admissible
$k$-tuple $\mathcal{H}$, there exist infinitely many $n$ such that the shifted
tuple $n + \mathcal{H}$ contains at least $j$ primes.

The full Dickson-Hardy-Littlewood conjecture is $\DHL[k, k]$ for all $k \ge 2$.
The bounded-gap program proves $\DHL[k, 2]$ (and beyond) for specific $k$. -/
def DHL (k j : ℕ) : Prop :=
  ∀ H : List ℕ, Admissible H → H.length = k →
    Set.Infinite { n : ℕ | (H.countP (fun h => (n + h).Prime)) ≥ j }

/-! ### BoundedGap, liminfGap, DHL equivalences -/

/-- Set-infinite encoding of "$H_m \le H$", convenient for some statements. -/
def BoundedGap (H : ℕ) : Prop :=
  Set.Infinite { p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p < q ∧ q - p ≤ H }

/-- `liminfGap 1 ≤ H` iff `BoundedGap H` — bridge between literature notation
and the set-infinite encoding. -/
-- TRIAGE: PROVABLE (~1-2h) — real Filter.liminf machinery; sister of
-- TwinPrimes.twinPrimes_iff_liminfGap_one. Bundle them when tackled.
theorem liminfGap_one_le_iff (H : ℕ) :
    liminfGap 1 ≤ (H : ℕ∞) ↔ BoundedGap H := sorry

/-- Helper: if `h ∈ H`, then `h ≤ H.foldr max 0`. Used for the diameter bound. -/
private lemma le_foldr_max (h : ℕ) (H : List ℕ) (hmem : h ∈ H) :
    h ≤ H.foldr max 0 := by
  induction H with
  | nil => simp at hmem
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | h_in_t
    · exact le_max_left _ _
    · exact (ih h_in_t).trans (le_max_right _ _)

/-- Helper: if `h ∈ H` and `H` is nonempty, then `H.foldr min init ≤ h` for
`init ≥ all of H`. Specialized to `init = H.foldr max 0` (which is `≥ h`)
gives `H.foldr min (H.foldr max 0) ≤ h` — the min of `H` is `≤` any
element of `H`. -/
private lemma foldr_min_le (h : ℕ) (H : List ℕ) (init : ℕ) (hmem : h ∈ H) :
    H.foldr min init ≤ h := by
  induction H with
  | nil => simp at hmem
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | h_in_t
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h_in_t)

/-- Combinatorial extraction: a `Pairwise (· < ·)` list with at least two
`P`-satisfying elements contains two distinct elements $h_1 < h_2$ with both
satisfying $P$. Used in `dhl_two_implies_boundedGap` to pull two ordered
prime-offset witnesses out of an admissible $k$-tuple. -/
theorem exists_two_increasing_of_countP_two_le
    {α : Type*} [LinearOrder α] (L : List α) (hSorted : L.Pairwise (· < ·))
    (P : α → Bool) (hCount : 2 ≤ L.countP P) :
    ∃ h₁ h₂, h₁ ∈ L ∧ h₂ ∈ L ∧ h₁ < h₂ ∧ P h₁ = true ∧ P h₂ = true := by
  -- The filtered list inherits sortedness from L and has length ≥ 2.
  have hFL : 2 ≤ (L.filter P).length := by
    rw [← List.countP_eq_length_filter]; exact hCount
  have hPair : (L.filter P).Pairwise (· < ·) := hSorted.sublist List.filter_sublist
  -- Destructure L.filter P as h₁ :: h₂ :: rest
  match hF : L.filter P, hFL with
  | h₁ :: h₂ :: _, _ =>
    have h₁_in_filter : h₁ ∈ L.filter P := by rw [hF]; exact List.mem_cons_self
    have h₂_in_filter : h₂ ∈ L.filter P := by
      rw [hF]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have h₁_in_L : h₁ ∈ L := (List.mem_filter.mp h₁_in_filter).1
    have h₂_in_L : h₂ ∈ L := (List.mem_filter.mp h₂_in_filter).1
    have h₁_P : P h₁ = true := (List.mem_filter.mp h₁_in_filter).2
    have h₂_P : P h₂ = true := (List.mem_filter.mp h₂_in_filter).2
    have h12 : h₁ < h₂ := by
      rw [hF] at hPair
      exact (List.pairwise_cons.mp hPair).1 h₂ List.mem_cons_self
    exact ⟨h₁, h₂, h₁_in_L, h₂_in_L, h12, h₁_P, h₂_P⟩

/-- **DHL[k, 2]** for an admissible $k$-tuple of diameter $H$ implies
$H_1 \le H$ (Polymath8b §3, first paragraph after Theorem 3.1). -/
theorem dhl_two_implies_boundedGap (k : ℕ) (hDHL : DHL k 2)
    (H : List ℕ) (hAdm : Admissible H) (hLength : H.length = k) :
    BoundedGap (diameter H) := by
  unfold BoundedGap
  apply Set.infinite_of_forall_exists_gt
  intro N
  -- DHL gives infinitely many n with ≥ 2 primes among n + h_i
  obtain ⟨n, hn_mem, hn_gt⟩ := (hDHL H hAdm hLength).exists_gt N
  simp only [Set.mem_setOf_eq] at hn_mem
  -- hn_mem : 2 ≤ H.countP (fun h => (n + h).Prime)
  -- Convert to Bool-form for the helper
  have hn_bool : 2 ≤ H.countP (fun h => decide (n + h).Prime) := by
    convert hn_mem using 1
  -- Extract two ordered prime-offsets via the helper
  obtain ⟨h₁, h₂, h₁_in_H, h₂_in_H, h12, h₁_prime_b, h₂_prime_b⟩ :=
    exists_two_increasing_of_countP_two_le H hAdm.1
      (fun h => decide (n + h).Prime) hn_bool
  have h₁_prime : (n + h₁).Prime := by simpa using h₁_prime_b
  have h₂_prime : (n + h₂).Prime := by simpa using h₂_prime_b
  -- Construct the BoundedGap witness: p = n + h₁, q = n + h₂
  refine ⟨n + h₁, ⟨h₁_prime, n + h₂, h₂_prime, ?_, ?_⟩, ?_⟩
  · -- n + h₁ < n + h₂
    exact Nat.add_lt_add_left h12 n
  · -- (n + h₂) - (n + h₁) ≤ diameter H
    unfold diameter
    have hh₂ : h₂ ≤ H.foldr max 0 := le_foldr_max h₂ H h₂_in_H
    have hh₁ : H.foldr min (H.foldr max 0) ≤ h₁ :=
      foldr_min_le h₁ H (H.foldr max 0) h₁_in_H
    omega
  · -- N < n + h₁
    omega

/-- General form: $\DHL[k, m+1] \Rightarrow H_m \le H(k)$. -/
-- TRIAGE: PROVABLE (~1h) — same as above generalized to m+1 primes; requires
-- liminfGap_one_le_iff for the m=1 case, plus the diameter ↔ narrowness step.
theorem dhl_implies_liminfGap (k m : ℕ) (_hk : k ≥ m + 1)
    (_hDHL : DHL k (m + 1)) :
    liminfGap m ≤ (narrowness k : ℕ∞) := sorry

end BoundedGaps
