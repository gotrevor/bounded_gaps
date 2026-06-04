/-
# GPY/Maynard sieve-sum expansion (Polymath8b §3, sub-step (a)).

The `s1`/`s2` sieve asymptotics (`Sieve.lean`, `s1_holds_from_nonprime_asym`
and friends) are cited axioms whose first proof step is purely algebraic:
*open the square* in the Selberg weight `ν = (∑_j c_j ∏_i λ_{F_{j,i}})²` and
regroup the resulting product of Möbius-divisor sums into a **divisor-lattice
double sum** weighted by lattice-point counts
`#{n ∈ block : ∀i, dᵢ ∣ (n+hᵢ) ∧ eᵢ ∣ (n+hᵢ)}`.

This file builds the reusable algebraic bricks for that step (the
`ANALYTIC_AXIOM_BURNDOWN.md` "sub-step (a): square + expand + swap"):
- `divisor_pair_expand`   — single coordinate, general `f g : ℕ → ℝ`.
- `lambdaTransform_pair_block` — the same specialized to two `λ`-transforms.

The downstream sub-steps are (b) the CRT lattice-point count and (c) the
Mertens/singular-series summation (its 1-D core `∑ μ²/φ = Θ(log N)` is already
proven unconditionally in `BoundedGaps.Mertens`).
-/
import Mathlib
import BoundedGaps.Sieve

namespace BoundedGaps.Sieve

open scoped BigOperators
open ArithmeticFunction (moebius)

/-- **Sub-step (a) core, single coordinate.**
For a finite set `S` of *positive* integers and arbitrary real functions
`f g`, the block-sum of the product of two divisor sums regroups as a
divisor-lattice double sum weighted by the count of `m ∈ S` divisible by both
`d` and `e`:
`∑_{m∈S} (∑_{d∣m} f d)(∑_{e∣m} g e)
   = ∑_{d∈D} ∑_{e∈D} f d · g e · #{m∈S : d∣m ∧ e∣m}`
where `D = S.biUnion divisors`. This is the algebraic heart of opening the
square in the GPY/Maynard sieve sum (Polymath8b §3 eqn (sfg-1)). -/
theorem divisor_pair_expand (S : Finset ℕ) (hS : 0 ∉ S) (f g : ℕ → ℝ) :
    ∑ m ∈ S, (∑ d ∈ m.divisors, f d) * (∑ e ∈ m.divisors, g e)
      = ∑ d ∈ S.biUnion (fun m => m.divisors),
          ∑ e ∈ S.biUnion (fun m => m.divisors),
            f d * g e * ((S.filter (fun m => d ∣ m ∧ e ∣ m)).card : ℝ) := by
  classical
  set D := S.biUnion (fun m => m.divisors) with hD
  -- (1) Rewrite each inner divisor-sum as a filtered sum over the common set `D`.
  have hrw : ∀ (h : ℕ → ℝ), ∀ m ∈ S,
      ∑ d ∈ m.divisors, h d = ∑ d ∈ D, (if d ∣ m then h d else 0) := by
    intro h m hm
    have hm0 : m ≠ 0 := fun hmz => hS (hmz ▸ hm)
    have hsub : m.divisors ⊆ D := Finset.subset_biUnion_of_mem (fun m => m.divisors) hm
    have hfilt : D.filter (fun d => d ∣ m) = m.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨fun ⟨_, hd⟩ => ⟨hd, hm0⟩,
             fun ⟨hd, _⟩ => ⟨hsub (Nat.mem_divisors.mpr ⟨hd, hm0⟩), hd⟩⟩
    rw [← hfilt, Finset.sum_filter]
  -- (2) Open both divisor sums over `D`, multiply out with `sum_mul_sum`.
  have step1 : ∑ m ∈ S, (∑ d ∈ m.divisors, f d) * (∑ e ∈ m.divisors, g e)
      = ∑ m ∈ S, ∑ d ∈ D, ∑ e ∈ D,
          (if d ∣ m then f d else 0) * (if e ∣ m then g e else 0) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hrw f m hm, hrw g m hm, Finset.sum_mul_sum]
  rw [step1]
  -- (3) Swap the `m`-sum to the inside.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  -- (4) Per `(d,e)`: collapse the indicator product into a count.
  have hpt : ∀ m, (if d ∣ m then f d else 0) * (if e ∣ m then g e else 0)
      = if (d ∣ m ∧ e ∣ m) then f d * g e else 0 := by
    intro m; by_cases h1 : d ∣ m <;> by_cases h2 : e ∣ m <;> simp [h1, h2]
  simp_rw [hpt]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Multidimensional divisor-lattice swap (workhorse).**
For a `Fintype` index `ι`, a finite set `S`, per-coordinate candidate sets
`D i`, a per-coordinate selection predicate `cond i x m`, and weights `u i x`,
the block-sum of the product of the *active* (selected) sub-sums regroups as a
sum over selection tuples `P ∈ ∏ᵢ D i`, weighted by the count of `m ∈ S`
selecting `P` in every coordinate:
`∑_{m∈S} ∏ᵢ (∑_{x∈D i, cond i x m} u i x)
   = ∑_{P∈∏ D} (∏ᵢ u i (P i)) · #{m∈S : ∀i, cond i (P i) m}`.
This is the `Fintype`-indexed generalization of `divisor_pair_expand`; the GPY
sub-step (a) swap for the `k`-fold Selberg product is the `ι = Fin k`,
`N = ℕ×ℕ` instance (`sieveSum_selberg_nu_separable_expand`). -/
theorem prod_sum_active_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N M : Type*} [DecidableEq N] [DecidableEq M]
    (S : Finset M) (D : ι → Finset N) (cond : ι → N → M → Prop)
    [∀ i x m, Decidable (cond i x m)] (u : ι → N → ℝ) :
    ∑ m ∈ S, ∏ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
      = ∑ P ∈ Fintype.piFinset D, (∏ i, u i (P i))
          * ((S.filter (fun m => ∀ i, cond i (P i) m)).card : ℝ) := by
  classical
  have key : ∀ m ∈ S, ∏ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
      = ∑ P ∈ Fintype.piFinset D,
          if (∀ i, cond i (P i) m) then ∏ i, u i (P i) else 0 := by
    intro m _
    have hf : ∀ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
        = ∑ x ∈ D i, (if cond i x m then u i x else 0) := fun i => Finset.sum_filter _ _
    simp_rw [hf]
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr rfl (fun P _ => Fintype.prod_ite_zero)
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Sub-step (a), single-coordinate, for the Möbius-divisor transform.**
Specializing `divisor_pair_expand` to `f' d = μ(d)·f(log d/log R)` and
`g' e = μ(e)·g(log e/log R)` opens a block-sum of products of two
`λ`-transforms into the divisor-lattice form: each `(d,e)` pair contributes
`μ(d)μ(e) f(·) g(·)` times the count of block elements divisible by both.
This is the Polymath8b §3 (sfg-1) opening for a single sieve coordinate. -/
theorem lambdaTransform_pair_block (S : Finset ℕ) (hS : 0 ∉ S)
    (f g : ℝ → ℝ) (R : ℝ) :
    ∑ m ∈ S, lambdaTransform f R m * lambdaTransform g R m
      = ∑ d ∈ S.biUnion (fun m => m.divisors),
          ∑ e ∈ S.biUnion (fun m => m.divisors),
            ((moebius d : ℝ) * f (Real.log d / Real.log R))
              * ((moebius e : ℝ) * g (Real.log e / Real.log R))
              * ((S.filter (fun m => d ∣ m ∧ e ∣ m)).card : ℝ) := by
  simpa only [lambdaTransform] using
    divisor_pair_expand S hS
      (fun d => (moebius d : ℝ) * f (Real.log d / Real.log R))
      (fun e => (moebius e : ℝ) * g (Real.log e / Real.log R))

/-- **Sub-step (a), multidimensional, pointwise.**
The separable Selberg weight `ν_sep(n) = (∏ᵢ λ_{Fᵢ}(n+hᵢ))²` opens
coordinate-by-coordinate into a **divisor-tuple double sum**: each pair
`(dᵢ, eᵢ)` of divisors of `n+hᵢ` contributes
`μ(dᵢ)μ(eᵢ) Fᵢ(log dᵢ/log R) Fᵢ(log eᵢ/log R)`. The tuple `P i = (dᵢ, eᵢ)`
ranges over `∏ᵢ ((n+hᵢ).divisors ×ˢ (n+hᵢ).divisors)` (`Fintype.piFinset`).
This is the Polymath8b §3 (sfg-1) opening, *before* summing over the block and
swapping (which produces the lattice-point counts — see
`ANALYTIC_AXIOM_BURNDOWN.md` sub-step (a)). -/
theorem selberg_nu_separable_expand_pointwise (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (n : ℕ) :
    selberg_nu_separable k Fs H R n
      = ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            (n + H.getD i.val 0).divisors ×ˢ (n + H.getD i.val 0).divisors),
          ∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs i (Real.log (P i).2 / Real.log R)) := by
  classical
  unfold selberg_nu_separable
  rw [sq, ← Finset.prod_mul_distrib]
  have hsq : ∀ i : Fin k,
      lambdaTransform (Fs i) R (n + H.getD i.val 0)
          * lambdaTransform (Fs i) R (n + H.getD i.val 0)
        = ∑ de ∈ (n + H.getD i.val 0).divisors ×ˢ (n + H.getD i.val 0).divisors,
            ((moebius de.1 : ℝ) * Fs i (Real.log de.1 / Real.log R))
              * ((moebius de.2 : ℝ) * Fs i (Real.log de.2 / Real.log R)) := by
    intro i
    unfold lambdaTransform
    rw [Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [hsq]
  rw [Finset.prod_univ_sum]

/-- Per-coordinate divisor-candidate set: all divisors of `n + hᵢ` as `n`
ranges over the sieve block `[⌈x⌉, ⌊2x⌋] ∩ (b mod W)`. The support of the
`i`-th coordinate in the divisor-lattice expansion. -/
noncomputable def sieveDivisors (H : List ℕ) (i b W : ℕ) (x : ℝ) : Finset ℕ :=
  ((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).biUnion
    (fun n => (n + H.getD i 0).divisors)

/-- **Sub-step (a) headline (separable weight).**
The full Selberg sieve sum `∑_{n∈block} ν_sep(n)` opens into a divisor-lattice
sum over tuples `P i = (dᵢ, eᵢ)` (each `dᵢ, eᵢ` ranging over the candidate set
`sieveDivisors`), weighted by the Möbius product and the **lattice-point count**
`#{m ∈ block : ∀i, dᵢ ∣ (m+hᵢ) ∧ eᵢ ∣ (m+hᵢ)}`. This is Polymath8b §3 eqn
(sfg-1) fully expanded — the algebraic skeleton that the CRT count (sub-step (b),
mathlib's `Nat.Ioc_filter_modEq_card`) and the Mertens/singular-series summation
(sub-step (c), `BoundedGaps.Mertens.mertens_theta_log`) then turn into the (s1)
main term. Obtained by instantiating `prod_sum_active_expand` at `ι = Fin k`,
`N = ℕ×ℕ`, after collapsing each coordinate's active sum to `λ_{Fᵢ}(m+hᵢ)²`. -/
theorem sieveSum_selberg_nu_separable_expand (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) :
    sieveSum (selberg_nu_separable k Fs H R) b W x
      = ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs i (Real.log (P i).2 / Real.log R)))
          * (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card := by
  classical
  set block := (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W) with hblock
  -- `m ∈ block ⟹ 0 < m + hᵢ` (so divisor sets are honest).
  have hpos : ∀ m ∈ block, ∀ i : Fin k, 0 < m + H.getD i.val 0 := by
    intro m hm i
    have hm' : m ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := (Finset.mem_filter.mp hm).1
    have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
    have : ⌈x⌉₊ ≤ m := (Finset.mem_Icc.mp hm').1
    omega
  -- Step A: pointwise, `ν_sep(m) = ∏ᵢ (active sum over the candidate product)`.
  have stepA : ∀ m ∈ block,
      selberg_nu_separable k Fs H R m
        = ∏ i : Fin k, ∑ x' ∈ (sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x).filter
              (fun de => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0)),
            ((moebius x'.1 : ℝ) * Fs i (Real.log x'.1 / Real.log R))
              * ((moebius x'.2 : ℝ) * Fs i (Real.log x'.2 / Real.log R)) := by
    intro m hm
    unfold selberg_nu_separable
    rw [sq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hsub : (m + H.getD i.val 0).divisors ⊆ sieveDivisors H i.val b W x :=
      Finset.subset_biUnion_of_mem (fun n => (n + H.getD i.val 0).divisors) hm
    have hm0 : m + H.getD i.val 0 ≠ 0 := (hpos m hm i).ne'
    -- the filtered candidate product equals the genuine divisor product.
    have hset : (sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x).filter
          (fun de => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0))
        = (m + H.getD i.val 0).divisors ×ˢ (m + H.getD i.val 0).divisors := by
      ext de
      simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
      refine ⟨fun ⟨_, hd1, hd2⟩ => ⟨⟨hd1, hm0⟩, hd2, hm0⟩, fun ⟨⟨hd1, _⟩, hd2, _⟩ => ?_⟩
      exact ⟨⟨hsub (Nat.mem_divisors.mpr ⟨hd1, hm0⟩),
              hsub (Nat.mem_divisors.mpr ⟨hd2, hm0⟩)⟩, hd1, hd2⟩
    rw [hset]
    simp only [lambdaTransform]
    rw [Finset.sum_mul_sum, Finset.sum_product]
  -- Step B: rewrite the block sum and apply the multidimensional swap workhorse.
  rw [sieveSum, ← hblock, Finset.sum_congr rfl stepA]
  convert prod_sum_active_expand block
    (fun i => sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x)
    (fun i de m => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0))
    (fun i de => ((moebius de.1 : ℝ) * Fs i (Real.log de.1 / Real.log R))
              * ((moebius de.2 : ℝ) * Fs i (Real.log de.2 / Real.log R)))

/-- `Nat.lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c`. -/
private theorem nat_lcm_dvd_iff (a b c : ℕ) : Nat.lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=
  ⟨fun h => ⟨(Nat.dvd_lcm_left a b).trans h, (Nat.dvd_lcm_right a b).trans h⟩,
   fun ⟨h1, h2⟩ => Nat.lcm_dvd h1 h2⟩

/-- **Sub-step (b) reduction: pair-divisibility ↦ single lcm modulus.**
The lattice-point count appearing in `sieveSum_selberg_nu_separable_expand`,
`#{m ∈ S : ∀i, dᵢ∣(m+hᵢ) ∧ eᵢ∣(m+hᵢ)}`, equals the count with each coordinate
condition collapsed to the single GPY modulus `[dᵢ,eᵢ] = lcm(dᵢ,eᵢ)`:
`#{m ∈ S : ∀i, [dᵢ,eᵢ]∣(m+hᵢ)}`. This is the standard reduction to a
per-coordinate congruence — the precursor to the CRT lattice count (sub-step
(b)), after which `Nat.Ioc_filter_modEq_card` gives the interval count. -/
theorem lattice_count_lcm {k : ℕ} (H : List ℕ) (S : Finset ℕ) (P : Fin k → ℕ × ℕ) :
    (S.filter (fun m => ∀ i : Fin k,
        (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
      = (S.filter (fun m => ∀ i : Fin k,
          Nat.lcm (P i).1 (P i).2 ∣ (m + H.getD i.val 0))).card := by
  classical
  congr 1
  apply Finset.filter_congr
  intro m _
  exact forall_congr' (fun i => (nat_lcm_dvd_iff _ _ _).symm)

end BoundedGaps.Sieve
