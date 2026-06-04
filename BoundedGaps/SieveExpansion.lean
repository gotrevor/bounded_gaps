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

/-- **Weighted multidimensional swap workhorse.** As `prod_sum_active_expand`,
but each `m ∈ S` carries a real weight `wt m`: the lattice count `#{m∈S:…}` is
replaced by the weighted sum `∑_{m∈S, ∀i cond} wt m`. The card version is the
`wt = 1` special case. This is the **s2** generalization — with
`wt m = primeTheta (m + h_{i₀})` it expands the prime-weighted sieve sum
`sieveThetaSum` (`sieveThetaSum_selberg_nu_expand`). -/
theorem prod_sum_active_expand_weighted {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N M : Type*} [DecidableEq N] [DecidableEq M]
    (S : Finset M) (wt : M → ℝ) (D : ι → Finset N) (cond : ι → N → M → Prop)
    [∀ i x m, Decidable (cond i x m)] (u : ι → N → ℝ) :
    ∑ m ∈ S, wt m * ∏ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
      = ∑ P ∈ Fintype.piFinset D, (∏ i, u i (P i))
          * (∑ m ∈ S.filter (fun m => ∀ i, cond i (P i) m), wt m) := by
  classical
  have key : ∀ m ∈ S, wt m * ∏ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
      = ∑ P ∈ Fintype.piFinset D,
          if (∀ i, cond i (P i) m) then wt m * ∏ i, u i (P i) else 0 := by
    intro m _
    have hprod : (∏ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x))
        = ∑ P ∈ Fintype.piFinset D, if (∀ i, cond i (P i) m) then ∏ i, u i (P i) else 0 := by
      have hf : ∀ i, (∑ x ∈ (D i).filter (fun x => cond i x m), u i x)
          = ∑ x ∈ D i, (if cond i x m then u i x else 0) := fun i => Finset.sum_filter _ _
      simp_rw [hf]
      rw [Finset.prod_univ_sum]
      exact Finset.sum_congr rfl (fun P _ => Fintype.prod_ite_zero)
    rw [hprod, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    split_ifs <;> ring
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← Finset.sum_filter, ← Finset.sum_mul, mul_comm]

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

/-- **Two-family coordinate-product expansion** (the general (sfg-1) opening).
For two test-function families `Gs, Hs`, the block-sum of the `k`-fold product
`∏ᵢ λ_{Gsᵢ}(n+hᵢ)·λ_{Hsᵢ}(n+hᵢ)` opens into the divisor-lattice form, each
tuple `P i = (dᵢ,eᵢ)` weighted by `μ(dᵢ)Gsᵢ·μ(eᵢ)Hsᵢ` times the lattice count.
The separable headline is `Gs = Hs`; the general `selberg_nu` weight
(`sieveSum_selberg_nu_expand`) is a finite `(j,j')`-combination of these
(`Gs = Fs j`, `Hs = Fs j'`). -/
theorem sieveSum_lambdaProd_expand (k : ℕ) (Gs Hs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W),
        ∏ i : Fin k, lambdaTransform (Gs i) R (n + H.getD i.val 0)
          * lambdaTransform (Hs i) R (n + H.getD i.val 0))
      = ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Gs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Hs i (Real.log (P i).2 / Real.log R)))
          * (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card := by
  classical
  set block := (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W) with hblock
  have hpos : ∀ m ∈ block, ∀ i : Fin k, 0 < m + H.getD i.val 0 := by
    intro m hm i
    have hm' : m ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := (Finset.mem_filter.mp hm).1
    have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
    have : ⌈x⌉₊ ≤ m := (Finset.mem_Icc.mp hm').1
    omega
  have stepA : ∀ m ∈ block,
      (∏ i : Fin k, lambdaTransform (Gs i) R (m + H.getD i.val 0)
          * lambdaTransform (Hs i) R (m + H.getD i.val 0))
        = ∏ i : Fin k, ∑ x' ∈ (sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x).filter
              (fun de => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0)),
            ((moebius x'.1 : ℝ) * Gs i (Real.log x'.1 / Real.log R))
              * ((moebius x'.2 : ℝ) * Hs i (Real.log x'.2 / Real.log R)) := by
    intro m hm
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hsub : (m + H.getD i.val 0).divisors ⊆ sieveDivisors H i.val b W x :=
      Finset.subset_biUnion_of_mem (fun n => (n + H.getD i.val 0).divisors) hm
    have hm0 : m + H.getD i.val 0 ≠ 0 := (hpos m hm i).ne'
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
  rw [Finset.sum_congr rfl stepA]
  convert prod_sum_active_expand block
    (fun i => sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x)
    (fun i de m => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0))
    (fun i de => ((moebius de.1 : ℝ) * Gs i (Real.log de.1 / Real.log R))
              * ((moebius de.2 : ℝ) * Hs i (Real.log de.2 / Real.log R)))

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

/-- **s2 two-family theta-weighted expansion.** As `sieveSum_lambdaProd_expand`
but carrying the prime weight `primeTheta(n+h_{i₀})`: the lattice count becomes
the prime-weighted lattice sum `∑_{m∈block, lattice} primeTheta(m+h_{i₀})`. The
s2 analog of the (sfg-1) opening (Polymath8b §3 eqn (theta-oo)). -/
theorem sieveThetaSum_lambdaProd_expand (k : ℕ) (Gs Hs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (b W i₀ : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W),
        primeTheta (n + H.getD i₀ 0) *
          ∏ i : Fin k, lambdaTransform (Gs i) R (n + H.getD i.val 0)
            * lambdaTransform (Hs i) R (n + H.getD i.val 0))
      = ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Gs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Hs i (Real.log (P i).2 / Real.log R)))
          * (∑ m ∈ ((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
              (fun m => ∀ i : Fin k,
                (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0)),
              primeTheta (m + H.getD i₀ 0)) := by
  classical
  set block := (Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W) with hblock
  have hpos : ∀ m ∈ block, ∀ i : Fin k, 0 < m + H.getD i.val 0 := by
    intro m hm i
    have hm' : m ∈ Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊ := (Finset.mem_filter.mp hm).1
    have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx
    have : ⌈x⌉₊ ≤ m := (Finset.mem_Icc.mp hm').1
    omega
  have stepA : ∀ m ∈ block,
      (∏ i : Fin k, lambdaTransform (Gs i) R (m + H.getD i.val 0)
          * lambdaTransform (Hs i) R (m + H.getD i.val 0))
        = ∏ i : Fin k, ∑ x' ∈ (sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x).filter
              (fun de => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0)),
            ((moebius x'.1 : ℝ) * Gs i (Real.log x'.1 / Real.log R))
              * ((moebius x'.2 : ℝ) * Hs i (Real.log x'.2 / Real.log R)) := by
    intro m hm
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hsub : (m + H.getD i.val 0).divisors ⊆ sieveDivisors H i.val b W x :=
      Finset.subset_biUnion_of_mem (fun n => (n + H.getD i.val 0).divisors) hm
    have hm0 : m + H.getD i.val 0 ≠ 0 := (hpos m hm i).ne'
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
  rw [Finset.sum_congr rfl (fun m hm => by rw [stepA m hm])]
  convert prod_sum_active_expand_weighted block (fun m => primeTheta (m + H.getD i₀ 0))
    (fun i => sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x)
    (fun i de m => de.1 ∣ (m + H.getD i.val 0) ∧ de.2 ∣ (m + H.getD i.val 0))
    (fun i de => ((moebius de.1 : ℝ) * Gs i (Real.log de.1 / Real.log R))
              * ((moebius de.2 : ℝ) * Hs i (Real.log de.2 / Real.log R)))

/-- **Sub-step (a) headline, GENERAL basis weight** (the actual `s1` weight).
The Selberg sieve sum for the full `selberg_nu` (a squared finite linear
combination `(∑ⱼ cⱼ ∏ᵢ λ_{Fⱼᵢ})²`) opens into a `(j,j')`-indexed combination of
divisor-lattice sums: each pair of basis indices contributes
`cⱼ·cⱼ'·∑_P (∏ᵢ μ(dᵢ)F_{j,i}·μ(eᵢ)F_{j',i})·#{lattice count}`. This is Polymath8b
§3 eqn (sfg-1) for the genuine multidimensional weight — exactly the object
`s1_holds_from_nonprime_asym` (`Sieve.lean`) must asymptotically estimate.
Reduces to `sieveSum_lambdaProd_expand` per `(j,j')` after opening the square. -/
theorem sieveSum_selberg_nu_expand (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) :
    sieveSum (selberg_nu k J c Fs H R) b W x
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * (((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                (fun m => ∀ i : Fin k,
                  (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card := by
  classical
  -- per-`n`: open the square into a `(j,j')` sum of coordinate products.
  have hbasis : ∀ n, selberg_nu k J c Fs H R n
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∏ i : Fin k, lambdaTransform (Fs j i) R (n + H.getD i.val 0)
            * lambdaTransform (Fs j' i) R (n + H.getD i.val 0) := by
    intro n
    unfold selberg_nu selberg_nu_basis
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [show (c j * ∏ i, lambdaTransform (Fs j i) R (n + H.getD i.val 0))
          * (c j' * ∏ i, lambdaTransform (Fs j' i) R (n + H.getD i.val 0))
        = c j * c j' * ((∏ i, lambdaTransform (Fs j i) R (n + H.getD i.val 0))
            * (∏ i, lambdaTransform (Fs j' i) R (n + H.getD i.val 0))) from by ring,
        ← Finset.prod_mul_distrib]
  rw [sieveSum, Finset.sum_congr rfl (fun n _ => hbasis n)]
  -- pull the finite `(j,j')` sums outside the `n`-sum, then apply the two-family lemma.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  exact sieveSum_lambdaProd_expand k (Fs j) (Fs j') H R b W x hx

/-- **s2 headline, GENERAL basis weight** (the actual `s2` object).
The prime-weighted Selberg sieve sum `sieveThetaSum` for the full `selberg_nu`
opens into a `(j,j')`-combination of divisor-lattice sums, each weighted by the
**prime-weighted lattice sum** `∑_{m∈block, lattice} primeTheta(m+h_{i₀})` —
exactly the object `s2_holds_from_prime_asym_under_{EH,MPZ}` (`Sieve.lean`) must
asymptotically estimate (the half where EH/BV is consumed). Reduces to
`sieveThetaSum_lambdaProd_expand` per `(j,j')`. -/
theorem sieveThetaSum_selberg_nu_expand (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W i₀ : ℕ) (x : ℝ) (hx : 0 < x) :
    sieveThetaSum (selberg_nu k J c Fs H R) H i₀ b W x
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * (∑ m ∈ ((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                (fun m => ∀ i : Fin k,
                  (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0)),
                primeTheta (m + H.getD i₀ 0)) := by
  classical
  have hbasisθ : ∀ n, selberg_nu k J c Fs H R n * primeTheta (n + H.getD i₀ 0)
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          (primeTheta (n + H.getD i₀ 0) *
            ∏ i : Fin k, lambdaTransform (Fs j i) R (n + H.getD i.val 0)
              * lambdaTransform (Fs j' i) R (n + H.getD i.val 0)) := by
    intro n
    unfold selberg_nu selberg_nu_basis
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.prod_mul_distrib]
    ring
  rw [sieveThetaSum, Finset.sum_congr rfl (fun n _ => hbasisθ n)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  exact sieveThetaSum_lambdaProd_expand k (Fs j) (Fs j') H R b W i₀ x hx

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

/-- **Sub-step (b) CRT combination.** For coprime `W, Q` (with `0 < Q`), the
simultaneous sieve condition `m ≡ b [MOD W] ∧ Q ∣ (m + h)` (the per-coordinate
residue-plus-divisibility constraint, after `lattice_count_lcm` with
`Q = [dᵢ,eᵢ]`) is a single residue class mod `W*Q`. Plugging this into the
interval-count formula `Nat.Ioc_filter_modEq_card` yields the GPY main term
`(interval length)/(W·Q)` up to an `O(1)` boundary error. -/
theorem crt_combine {W Q : ℕ} (hcop : Nat.Coprime W Q) (hQ : 0 < Q) (b h : ℕ) :
    ∃ r, ∀ m : ℕ, (m ≡ b [MOD W] ∧ Q ∣ (m + h)) ↔ m ≡ r [MOD (W * Q)] := by
  -- `c := (Q-1)*h` solves `Q ∣ (c + h)` since `c + h = Q*h`.
  set c := (Q - 1) * h with hc
  have hch : c + h = Q * h := by
    rw [hc, Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left h hQ)]
  have hc0 : (c + h) ≡ 0 [MOD Q] := Nat.modEq_zero_iff_dvd.mpr ⟨h, hch⟩
  -- `Q ∣ (m+h) ↔ m ≡ c [MOD Q]`.
  have hdvd_iff : ∀ m, Q ∣ (m + h) ↔ m ≡ c [MOD Q] := by
    intro m
    rw [← Nat.modEq_zero_iff_dvd]
    exact ⟨fun hm => Nat.ModEq.add_right_cancel' h (hm.trans hc0.symm),
           fun hm => (hm.add_right h).trans hc0⟩
  obtain ⟨r, hr1, hr2⟩ := Nat.chineseRemainder hcop b c
  refine ⟨r, fun m => ?_⟩
  rw [hdvd_iff m,
      show (m ≡ b [MOD W]) ↔ (m ≡ r [MOD W]) from
        ⟨fun h => h.trans hr1.symm, fun h => h.trans hr1⟩,
      show (m ≡ c [MOD Q]) ↔ (m ≡ r [MOD Q]) from
        ⟨fun h => h.trans hr2.symm, fun h => h.trans hr2⟩]
  exact Nat.modEq_and_modEq_iff_modEq_mul hcop

/-- Per-coordinate: `q ∣ (m + h) ↔ m ≡ (q-1)*h [MOD q]` (for `0 < q`). -/
private theorem dvd_iff_modEq {q : ℕ} (hq : 0 < q) (h m : ℕ) :
    q ∣ (m + h) ↔ m ≡ (q - 1) * h [MOD q] := by
  have hch : (q - 1) * h + h = q * h := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left h hq)]
  have hc0 : ((q - 1) * h + h) ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr ⟨h, hch⟩
  rw [← Nat.modEq_zero_iff_dvd]
  exact ⟨fun hm => Nat.ModEq.add_right_cancel' h (hm.trans hc0.symm),
         fun hm => (hm.add_right h).trans hc0⟩

/-- **Sub-step (b) multi-coordinate divisibility CRT.** For a coordinate list
`l` with pairwise-coprime positive moduli `q` and shifts `h`, the full
simultaneous condition `∀ i ∈ l, q i ∣ (m + h i)` is a single residue class mod
`(l.map q).prod`. This is the engine for the GPY lattice-point count: after
`lattice_count_lcm` (`q i = [dᵢ,eᵢ]`), on the coprime diagonal the entire
`∀i`-condition collapses to one modulus, whose interval count is then exactly
`Nat.Ioc_filter_modEq_card`. (Folding in the residue `m ≡ b [MOD W]` is one more
`crt_combine` step, `W` coprime to the product.) The off-diagonal
(`gcd(qᵢ,qⱼ) > 1`) is the genuine error term and the bridge to sub-step (c). -/
theorem crt_divisibility_iff {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (co : l.Pairwise (fun i j => Nat.Coprime (q i) (q j))) (hq : ∀ i ∈ l, 0 < q i) :
    ∃ r, ∀ m : ℕ, (∀ i ∈ l, q i ∣ (m + h i)) ↔ m ≡ r [MOD (l.map q).prod] := by
  set c : ι → ℕ := fun i => (q i - 1) * h i with hc
  refine ⟨Nat.chineseRemainderOfList c q l co, fun m => ?_⟩
  have hrw : (∀ i ∈ l, q i ∣ (m + h i)) ↔ (∀ i ∈ l, m ≡ c i [MOD q i]) :=
    forall_congr' (fun i => imp_congr_right (fun hi => dvd_iff_modEq (hq i hi) (h i) m))
  rw [hrw]
  refine ⟨fun hall => Nat.chineseRemainderOfList_modEq_unique c q l co hall, fun hmod i hi => ?_⟩
  exact ((Nat.modEq_list_map_prod_iff co).mp hmod i hi).trans
    ((Nat.chineseRemainderOfList c q l co).prop i hi)

/-- **Sub-step (b) diagonal capstone.** On the coprime diagonal (moduli
`q i = [dᵢ,eᵢ]` pairwise coprime and coprime to `W`), the *entire* sieve
membership condition `m ≡ b [MOD W] ∧ ∀ i ∈ l, q i ∣ (m + h i)` is a single
residue class mod `W · (l.map q).prod`. Hence the GPY lattice-point count is the
count of one arithmetic progression, evaluated exactly by
`Nat.Ioc_filter_modEq_card` (interval length over `W·∏q`, plus an `O(1)`
boundary term). Combines `crt_divisibility_iff` with `crt_combine`'s CRT step. -/
theorem sieve_condition_single_class {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (W b : ℕ) (co : l.Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (hq : ∀ i ∈ l, 0 < q i) (hWcop : Nat.Coprime W (l.map q).prod) :
    ∃ r, ∀ m : ℕ, (m ≡ b [MOD W] ∧ ∀ i ∈ l, q i ∣ (m + h i))
        ↔ m ≡ r [MOD (W * (l.map q).prod)] := by
  obtain ⟨r₀, hr₀⟩ := crt_divisibility_iff l q h co hq
  obtain ⟨r, hr1, hr2⟩ := Nat.chineseRemainder hWcop b r₀
  refine ⟨r, fun m => ?_⟩
  rw [hr₀ m,
      show (m ≡ b [MOD W]) ↔ (m ≡ r [MOD W]) from
        ⟨fun hh => hh.trans hr1.symm, fun hh => hh.trans hr1⟩,
      show (m ≡ r₀ [MOD (l.map q).prod]) ↔ (m ≡ r [MOD (l.map q).prod]) from
        ⟨fun hh => hh.trans hr2.symm, fun hh => hh.trans hr2⟩]
  exact Nat.modEq_and_modEq_iff_modEq_mul hWcop

/-- **Sub-step (b): the GPY lattice count is a single arithmetic-progression
count.** On the coprime diagonal, the count of block elements satisfying the
full sieve membership condition equals the count of one residue class mod
`W·(l.map q).prod` — exactly the form `Nat.Ioc_filter_modEq_card` evaluates to
`(interval length)/(W·∏q) + O(1)`. This closes the chain from the divisor-lattice
expansion (`sieveSum_selberg_nu_separable_expand`, with `q i = [dᵢ,eᵢ]` via
`lattice_count_lcm`) to a mathlib-computable count, on the coprime diagonal. -/
theorem lattice_count_eq_modEq {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (W b : ℕ) (S : Finset ℕ) (co : l.Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (hq : ∀ i ∈ l, 0 < q i) (hWcop : Nat.Coprime W (l.map q).prod) :
    ∃ r, (S.filter (fun m => m ≡ b [MOD W] ∧ ∀ i ∈ l, q i ∣ (m + h i))).card
        = (S.filter (fun m => m ≡ r [MOD (W * (l.map q).prod)])).card := by
  classical
  obtain ⟨r, hr⟩ := sieve_condition_single_class l q h W b co hq hWcop
  exact ⟨r, by rw [Finset.filter_congr (fun m _ => hr m)]⟩

end BoundedGaps.Sieve
