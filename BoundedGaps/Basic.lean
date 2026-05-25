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

/-- Generic admissibility — `sorry` for $k \ne 3$. -/
theorem admissibleTuple_admissible (k : ℕ) : Admissible (admissibleTuple k) := sorry

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

/-- **Key combinatorial lemma**: any admissible 3-tuple $[a, b, c]$ (sorted) has
diameter $c - a \ge 6$.

Proof by simultaneous case analysis on residues mod 2 and mod 3.
Mod 2 admissibility forces $a, b, c$ to all share the same parity, so
$c - a$ is even. For $c - a \in \{2, 4\}$ the parity constraint pins
$b = a + (c-a)/2$, and the resulting tuple $[a, a+\delta/2, a+\delta]$ has
residues mod 3 hitting every class (when $\delta = 4$, residues are
$\{a, a+2, a+1\}$ — all of $\mathbb Z/3$). -/
theorem admissible_three_diameter_ge_six
    {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hAdm : Admissible [a, b, c]) : 6 ≤ c - a := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨_, hRes⟩ := hAdm
  obtain ⟨r2, hr2⟩ := hRes 2 Nat.prime_two
  obtain ⟨r3, hr3⟩ := hRes 3 Nat.prime_three
  have h2a : (a : ZMod 2) ≠ r2 := hr2 a (by simp)
  have h2b : (b : ZMod 2) ≠ r2 := hr2 b (by simp)
  have h2c : (c : ZMod 2) ≠ r2 := hr2 c (by simp)
  have h3a : (a : ZMod 3) ≠ r3 := hr3 a (by simp)
  have h3b : (b : ZMod 3) ≠ r3 := hr3 b (by simp)
  have h3c : (c : ZMod 3) ≠ r3 := hr3 c (by simp)
  clear hr2 hr3 hRes
  -- Introduce offsets γ := b - a, δ := c - a as fresh variables with bounds
  obtain ⟨γ, hγ_pos, hγ_lt, hγ_eq⟩ : ∃ γ : ℕ, 1 ≤ γ ∧ γ ≤ 4 ∧ b = a + γ :=
    ⟨b - a, by omega, by omega, by omega⟩
  obtain ⟨δ, hδ_lt, hδγ, hδ_eq⟩ : ∃ δ : ℕ, δ ≤ 5 ∧ γ < δ ∧ c = a + δ :=
    ⟨c - a, by omega, by omega, by omega⟩
  -- Express residues of b, c via offsets
  have hb2 : (b : ZMod 2) = (a : ZMod 2) + (γ : ZMod 2) := by
    rw [hγ_eq]; push_cast; ring
  have hc2 : (c : ZMod 2) = (a : ZMod 2) + (δ : ZMod 2) := by
    rw [hδ_eq]; push_cast; ring
  have hb3 : (b : ZMod 3) = (a : ZMod 3) + (γ : ZMod 3) := by
    rw [hγ_eq]; push_cast; ring
  have hc3 : (c : ZMod 3) = (a : ZMod 3) + (δ : ZMod 3) := by
    rw [hδ_eq]; push_cast; ring
  rw [hb2] at h2b
  rw [hc2] at h2c
  rw [hb3] at h3b
  rw [hc3] at h3c
  -- Generalize (a : ZMod p) to fresh fin-cases-able variables
  generalize (a : ZMod 2) = α2 at h2a h2b h2c
  generalize (a : ZMod 3) = α3 at h3a h3b h3c
  -- Case split: γ ∈ {1,2,3,4}, then δ ∈ {γ+1,...,5}. In each branch revert all
  -- ZMod variables so `decide` can enumerate over the finite ZMod 2 × ZMod 3 space.
  interval_cases γ <;> interval_cases δ <;>
    (push_cast at h2b h2c h3b h3c
     revert h2a h2b h2c h3a h3b h3c α2 α3 r2 r3
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
theorem liminfGap_one_le_iff (H : ℕ) :
    liminfGap 1 ≤ (H : ℕ∞) ↔ BoundedGap H := sorry

/-- **DHL[k, 2]** for an admissible $k$-tuple of diameter $H$ implies
$H_1 \le H$ (Polymath8b §3, first paragraph after Theorem 3.1).

More generally, $\DHL[k, m+1]$ implies $H_m \le H(k)$. -/
theorem dhl_two_implies_boundedGap (k : ℕ) (_hDHL : DHL k 2)
    (H : List ℕ) (_hAdm : Admissible H) (_hLength : H.length = k) :
    BoundedGap (diameter H) := sorry

/-- General form: $\DHL[k, m+1] \Rightarrow H_m \le H(k)$. -/
theorem dhl_implies_liminfGap (k m : ℕ) (_hk : k ≥ m + 1)
    (_hDHL : DHL k (m + 1)) :
    liminfGap m ≤ (narrowness k : ℕ∞) := sorry

end BoundedGaps
