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

/-- **Sub-step (b) interval count, single arithmetic progression, O(1) error.**
The number of `m ∈ (A, B]` lying in one residue class `m ≡ v [MOD M]` (with
`0 < M`) is within `1` of the expected `(B - A)/M`. This is the elementary
boundary estimate that turns the exact AP count of `lattice_count_eq_modEq` into
the GPY main term `(interval length)/(W·∏q)`. Proof: mathlib's
`Nat.Ioc_filter_modEq_card` gives the exact count as `⌊(B-v)/M⌋ - ⌊(A-v)/M⌋`;
each floor is within `1` of its real value, so the difference is within `1` of
`(B-A)/M`. (Verified independently on Aristotle job `6515817c` as the combined
`Icc`/CRT statement `crt_interval_count_bound`; this is the cleaner single-AP
form that composes with our `lattice_count_eq_modEq` chain.) -/
theorem ap_interval_count_bound {M : ℕ} (hM : 0 < M) (v A B : ℕ) (hAB : A ≤ B) :
    |(((Finset.Ioc A B).filter (fun m => m ≡ v [MOD M])).card : ℝ)
      - (B - A : ℝ) / M| ≤ 1 := by
  have hcard := Nat.Ioc_filter_modEq_card A B hM v
  set x : ℚ := ((B : ℚ) - v) / M with hx
  set y : ℚ := ((A : ℚ) - v) / M with hy
  have hMℚ : (0 : ℚ) < M := by exact_mod_cast hM
  have hyx : y ≤ x := by rw [hx, hy]; gcongr
  have hfloor : ⌊y⌋ ≤ ⌊x⌋ := Int.floor_le_floor hyx
  rw [max_eq_left (sub_nonneg.mpr hfloor)] at hcard
  have hcardℝ : (((Finset.Ioc A B).filter (fun m => m ≡ v [MOD M])).card : ℝ)
      = (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) := by exact_mod_cast hcard
  rw [hcardℝ]
  have hxr  : (⌊x⌋ : ℝ) ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
  have hxr' : (x : ℝ) - 1 < (⌊x⌋ : ℝ) := by exact_mod_cast Int.sub_one_lt_floor x
  have hyr  : (⌊y⌋ : ℝ) ≤ (y : ℝ) := by exact_mod_cast Int.floor_le y
  have hyr' : (y : ℝ) - 1 < (⌊y⌋ : ℝ) := by exact_mod_cast Int.sub_one_lt_floor y
  have hmain : (x : ℝ) - (y : ℝ) = (B - A : ℝ) / M := by
    rw [hx, hy]; push_cast; ring
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [hxr, hxr', hyr, hyr', hmain]

/-- **Sub-step (b) capstone — the GPY diagonal main term with O(1) error.**
On the coprime diagonal (moduli `q i = [dᵢ,eᵢ]` pairwise coprime and coprime to
`W`, all positive), the GPY lattice-point count over an interval block `(A, B]`
satisfies
`#{m ∈ (A,B] : m ≡ b [MOD W] ∧ ∀ i ∈ l, q i ∣ (m + h i)} = (B-A)/(W·∏q) + O(1)`,
the `O(1)` being a single boundary unit. This closes sub-step (b) on the
diagonal: `lattice_count_eq_modEq` collapses the multi-coordinate sieve
condition to one residue class, then `ap_interval_count_bound` evaluates that
class's interval count. The remaining sieve content is the off-diagonal error
(`gcd(qᵢ,qⱼ) > 1`) and the sub-step (c) Mertens summation of these main terms. -/
theorem lattice_count_main_term {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (W b A B : ℕ) (co : l.Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (hq : ∀ i ∈ l, 0 < q i) (hWcop : Nat.Coprime W (l.map q).prod)
    (hW : 0 < W) (hAB : A ≤ B) :
    |(((Finset.Ioc A B).filter
          (fun m => m ≡ b [MOD W] ∧ ∀ i ∈ l, q i ∣ (m + h i))).card : ℝ)
      - (B - A : ℝ) / ((W * (l.map q).prod : ℕ) : ℝ)| ≤ 1 := by
  have hQpos : 0 < (l.map q).prod := by
    apply List.prod_pos
    intro x hxmem
    rw [List.mem_map] at hxmem
    obtain ⟨i, hi, rfl⟩ := hxmem
    exact hq i hi
  obtain ⟨r, hr⟩ := lattice_count_eq_modEq l q h W b (Finset.Ioc A B) co hq hWcop
  rw [hr]
  exact ap_interval_count_bound (Nat.mul_pos hW hQpos) r A B hAB

/-- **Off-diagonal vanishing (the mechanism killing the non-coprime terms).** If a
single modulus value `p` divides two of the GPY moduli `q i, q j` (`i ≠ j` indices
in `l`) but the shifts satisfy `h i ≢ h j [MOD p]`, then *no* block element meets
the sieve condition, so the lattice count is exactly `0`. Reason: `q i ∣ (m+h i)`
and `q j ∣ (m+h j)` force `p ∣ (m+h i)` and `p ∣ (m+h j)`, whence `h i ≡ h j [MOD p]`.
Primality of `p` is not needed. This is the elementary core of sub-step (b)'s
off-diagonal: under the W-trick a shared prime factor `p > D₀ ≥ H` of two moduli
satisfies `h i ≢ h j [MOD p]` (see `lattice_count_offdiag_vanish_of_lt`), so every
off-diagonal `∑_P` term drops out and the diagonal main term dominates. -/
theorem lattice_count_offdiag_vanish {ι : Type*} (l : List ι) (q h : ι → ℕ) (S : Finset ℕ)
    {i j : ι} (hi : i ∈ l) (hj : j ∈ l) {p : ℕ}
    (hpi : p ∣ q i) (hpj : p ∣ q j) (hne : ¬ (h i ≡ h j [MOD p])) :
    (S.filter (fun m => ∀ k ∈ l, q k ∣ (m + h k))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hm
  apply hne
  have h1 : p ∣ (m + h i) := hpi.trans (hm i hi)
  have h2 : p ∣ (m + h j) := hpj.trans (hm j hj)
  have e1 : m + h i ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h1
  have e2 : m + h j ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr h2
  exact Nat.ModEq.add_left_cancel' m (e1.trans e2.symm)

/-- **Off-diagonal vanishing, W-trick form.** A shared modulus value `p` exceeding
both shifts (`h i, h j < p`) with `h i ≠ h j` forces `h i ≢ h j [MOD p]`, so the
lattice count is `0`. In GPY, `p` is a shared prime factor `> D₀ ≥ H` of two
moduli, and the shifts of an admissible tuple are distinct and `< H ≤ p`. -/
theorem lattice_count_offdiag_vanish_of_lt {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (S : Finset ℕ) {i j : ι} (hi : i ∈ l) (hj : j ∈ l) {p : ℕ}
    (hpi : p ∣ q i) (hpj : p ∣ q j) (hij : h i ≠ h j) (hip : h i < p) (hjp : h j < p) :
    (S.filter (fun m => ∀ k ∈ l, q k ∣ (m + h k))).card = 0 := by
  refine lattice_count_offdiag_vanish l q h S hi hj hpi hpj (fun hcon => hij ?_)
  rw [Nat.ModEq, Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp] at hcon
  exact hcon

/-- **Off-diagonal vanishing under the W-trick (the real discharge).** With
`W` divisible by every prime `≤ D₀` (the GPY sieve modulus), the `i`-th sieve
modulus `q i` coprime to `W`, and the shifts bounded `h i, h j ≤ D₀` and distinct,
*non-coprimality* of two moduli `q i, q j` forces the lattice count to `0`. Reason:
a shared prime `p ∣ q i, q j` cannot divide `W` (it would divide `gcd(q i, W) = 1`),
so `p > D₀ ≥ h i, h j`; then `lattice_count_offdiag_vanish_of_lt` applies. So under
the W-trick only *pairwise-coprime* moduli survive — `sum_restrict_offdiag_vanish`
restricts the expansion to the coprime diagonal. -/
theorem lattice_count_offdiag_vanish_Wtrick {ι : Type*} (l : List ι) (q h : ι → ℕ)
    (S : Finset ℕ) {i j : ι} (hi : i ∈ l) (hj : j ∈ l) (D₀ W : ℕ)
    (hWdvd : ∀ p, p.Prime → p ≤ D₀ → p ∣ W)
    (hcopi : Nat.Coprime (q i) W) (hncop : ¬ Nat.Coprime (q i) (q j))
    (hbi : h i ≤ D₀) (hbj : h j ≤ D₀) (hij : h i ≠ h j) :
    (S.filter (fun m => ∀ k ∈ l, q k ∣ (m + h k))).card = 0 := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hncop
  have hpi : p ∣ q i := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpj : p ∣ q j := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpD : D₀ < p := by
    by_contra hle
    have hpW : p ∣ W := hWdvd p hp (not_lt.mp hle)
    have hcontra : p ∣ Nat.gcd (q i) W := Nat.dvd_gcd hpi hpW
    rw [hcopi] at hcontra
    exact hp.ne_one (Nat.dvd_one.mp hcontra)
  exact lattice_count_offdiag_vanish_of_lt l q h S hi hj hpi hpj hij
    (lt_of_le_of_lt hbi hpD) (lt_of_le_of_lt hbj hpD)

/-- **Off-diagonal vanishing in the expansion form.** The exact lattice count
appearing in `sieveSum_selberg_nu_separable_expand` (and the theta sister) is
`#{m ∈ S : ∀i, (P i).1 ∣ (m+hᵢ) ∧ (P i).2 ∣ (m+hᵢ)}`. If some value `p` divides
the `i`-th modulus `lcm((P i).1,(P i).2)` and the `j`-th modulus
`lcm((P j).1,(P j).2)` (`i ≠ j`) but the shifts disagree mod `p`
(`hᵢ ≢ hⱼ [MOD p]`), this count is exactly `0`. So in the `∑_P` expansion every
off-diagonal tuple `P` (two coordinates sharing a prime with incompatible shifts)
drops out — only the coprime-diagonal `P` survive, where `lattice_count_main_term`
gives the GPY main term. (Pair-divisibility form of `lattice_count_offdiag_vanish`,
via `nat_lcm_dvd_iff`.) -/
theorem lattice_count_pair_offdiag_vanish {k : ℕ} (H : List ℕ) (S : Finset ℕ)
    (P : Fin k → ℕ × ℕ) {i j : Fin k} {p : ℕ}
    (hpi : p ∣ Nat.lcm (P i).1 (P i).2) (hpj : p ∣ Nat.lcm (P j).1 (P j).2)
    (hne : ¬ (H.getD i.val 0 ≡ H.getD j.val 0 [MOD p])) :
    (S.filter (fun m => ∀ t : Fin k,
        (P t).1 ∣ (m + H.getD t.val 0) ∧ (P t).2 ∣ (m + H.getD t.val 0))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hm
  apply hne
  have hi : p ∣ (m + H.getD i.val 0) := hpi.trans ((nat_lcm_dvd_iff _ _ _).mpr (hm i))
  have hj : p ∣ (m + H.getD j.val 0) := hpj.trans ((nat_lcm_dvd_iff _ _ _).mpr (hm j))
  have e1 : m + H.getD i.val 0 ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hi
  have e2 : m + H.getD j.val 0 ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hj
  exact Nat.ModEq.add_left_cancel' m (e1.trans e2.symm)

/-- **Theta-weighted off-diagonal vanishing (s2 sister).** The weighted count in
`sieveThetaSum_selberg_nu_expand`, `∑_{m∈S, lattice} wt m` (with `wt = primeTheta(·+h_{i₀})`),
also vanishes on the off-diagonal: if two coordinates' moduli `lcm(P i), lcm(P j)`
share a value `p` with incompatible shifts (`hᵢ ≢ hⱼ [MOD p]`), the membership set
is empty so the weighted sum is `0`, for *any* weight `wt`. So the same diagonal
restriction governs `s2` as `s1`. -/
theorem sieveTheta_pair_offdiag_vanish {k : ℕ} (H : List ℕ) (S : Finset ℕ)
    (P : Fin k → ℕ × ℕ) (wt : ℕ → ℝ) {i j : Fin k} {p : ℕ}
    (hpi : p ∣ Nat.lcm (P i).1 (P i).2) (hpj : p ∣ Nat.lcm (P j).1 (P j).2)
    (hne : ¬ (H.getD i.val 0 ≡ H.getD j.val 0 [MOD p])) :
    ∑ m ∈ S.filter (fun m => ∀ t : Fin k,
        (P t).1 ∣ (m + H.getD t.val 0) ∧ (P t).2 ∣ (m + H.getD t.val 0)), wt m = 0 := by
  have hempty : S.filter (fun m => ∀ t : Fin k,
      (P t).1 ∣ (m + H.getD t.val 0) ∧ (P t).2 ∣ (m + H.getD t.val 0)) = ∅ :=
    Finset.card_eq_zero.mp (lattice_count_pair_offdiag_vanish H S P hpi hpj hne)
  rw [hempty, Finset.sum_empty]

/-- **Sub-step (b) diagonal restriction.** In the divisor-lattice expansion
`∑_P (weight P)·(value P)` (the output of `sieveSum_selberg_nu_separable_expand`
and its theta sister, with `value P` the lattice count resp. the theta-weighted
count), every off-diagonal tuple `P` contributes `0` because its `value P = 0`
(`lattice_count_pair_offdiag_vanish` / `sieveTheta_pair_offdiag_vanish`). Hence the
whole sum restricts to the *coprime-diagonal* tuples — exactly those on which
`lattice_count_main_term` evaluates the count. This is the assembly step turning
the full expansion into the diagonal main term, abstracted over the diagonal
predicate `diag` (discharged by the W-trick: a shared prime of two coordinate
moduli `> D₀ ≥ H` forces incompatible shifts). -/
theorem sum_restrict_offdiag_vanish {ι : Type*} (s : Finset ι) (weight val : ι → ℝ)
    (diag : ι → Prop) [DecidablePred diag]
    (hvanish : ∀ P ∈ s, ¬ diag P → val P = 0) :
    ∑ P ∈ s, weight P * val P = ∑ P ∈ s.filter diag, weight P * val P := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  by_cases h : diag P
  · rw [if_pos h]
  · rw [if_neg h, hvanish P hP h, mul_zero]

/-- **Sub-step (c) entry — the GPY 1-D diagonalization identity.**
The Selberg quadratic form on a finite set `T` of positive integers,
`∑_{d,e ∈ T} w(d) w(e) / [d,e]` (with `[d,e] = Nat.lcm d e`), diagonalizes into a
*single* sum of squares over the common-divisor variable `r`:
`∑_{d,e} w(d)w(e)/[d,e] = ∑_{r ∈ R} φ(r) · (∑_{d ∈ T, r∣d} w(d)/d)²`,
for any finset `R` that contains every divisor of every `d ∈ T`.

This is the algebraic core of GPY's diagonalization of the Selberg sieve (the
step turning the divisor-lattice quadratic form of sub-step (b)'s diagonal main
term into the diagonal sum whose Mertens/Riemann asymptotic gives the constant
`α = I(F)`). For the sieve application take `w d = μ(d) · F(log d / log R)` (the
summand of `lambdaTransform`): see `gpy_diagonalize_moebius`. Pure finite
algebra: `1/[d,e] = gcd(d,e)/(d·e)` (`Nat.gcd_mul_lcm`) followed by
`gcd(d,e) = ∑_{r∣gcd} φ(r)` (`Nat.sum_totient`) and reindexing `r` outermost. -/
theorem gpy_diagonalize (T R : Finset ℕ) (w : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T, w d * w e / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, (Nat.totient r : ℝ)
          * (∑ d ∈ T.filter (fun d => r ∣ d), w d / (d : ℝ)) ^ 2 := by
  classical
  have step1 : ∀ d ∈ T, ∀ e ∈ T,
      w d * w e / (Nat.lcm d e : ℝ)
        = ∑ r ∈ R, (if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0)
            * (w d / (d:ℝ)) * (w e / (e:ℝ)) := by
    intro d hd e he
    have hd1 := hT d hd; have he1 := hT e he
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hd1
    have he0 : (e:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp he1
    have hgcd0 : Nat.gcd d e ≠ 0 := Nat.gcd_ne_zero_left (by omega)
    have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d:ℝ) * (e:ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hlcm0 : (Nat.lcm d e : ℝ) ≠ 0 := by
      have : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      exact_mod_cast this
    have hrw : w d * w e / (Nat.lcm d e : ℝ)
        = (Nat.gcd d e : ℝ) * ((w d / (d:ℝ)) * (w e / (e:ℝ))) := by
      field_simp
      linear_combination (-(w d * w e)) * hgl
    rw [hrw]
    have htot : (Nat.gcd d e : ℝ) = ∑ r ∈ (Nat.gcd d e).divisors, (Nat.totient r : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast (Nat.sum_totient _).symm
    have hfilter : (Nat.gcd d e).divisors = R.filter (fun r => r ∣ d ∧ r ∣ e) := by
      ext r
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hrd, hre⟩, _⟩
        exact ⟨hR d hd r hrd, hrd, hre⟩
      · rintro ⟨_, hrd, hre⟩
        exact ⟨⟨hrd, hre⟩, hgcd0⟩
    rw [htot, hfilter, Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => step1 d hd e he))]
  -- swap `r` to the outermost position
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ T) => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  -- per-`r` slice factors into a square
  have key : ∑ d ∈ T.filter (fun d => r ∣ d), w d / (d:ℝ)
      = ∑ d ∈ T, (if r ∣ d then (1:ℝ) else 0) * (w d / (d:ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h : r ∣ d <;> simp [h]
  rw [key, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h1 : r ∣ d <;> by_cases h2 : r ∣ e <;> simp [h1, h2, mul_assoc]

/-- **GPY diagonalization, Möbius-weighted form** (the sieve specialization).
With the GPY weight `w(d) = μ(d) · g(d)` — exactly the summand of
`lambdaTransform g R` over divisors — the Selberg quadratic form diagonalizes:
`∑_{d,e ∈ T} μ(d)μ(e) g(d)g(e)/[d,e] = ∑_{r ∈ R} φ(r) (∑_{d∈T, r∣d} μ(d)g(d)/d)²`.
The right side is the diagonal sum whose asymptotic (sub-step (c) Mertens/Riemann
limit) produces the main-term constant. Direct instance of `gpy_diagonalize`. -/
theorem gpy_diagonalize_moebius (T R : Finset ℕ) (g : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g d * ((moebius e : ℝ) * g e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, (Nat.totient r : ℝ)
          * (∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g d / (d : ℝ)) ^ 2 :=
  gpy_diagonalize T R (fun d => (moebius d : ℝ) * g d) hT hR

/-- **GPY `y_r` substitution** — the divisor-restricted inner sum of
`gpy_diagonalize_moebius` written in terms of a *coprime-restricted* sum over
`s = d/r`. Reindexing `d = r·s` and using `μ(r·s) = μ(r)·μ(s)·[gcd(r,s)=1]`
(Möbius vanishes off the squarefree locus) gives
`∑_{d ∈ T, r∣d} μ(d) g(d)/d = (μ(r)/r) · ∑_{s, (r,s)=1} μ(s) g(r·s)/s`.
This is the GPY change of variable exposing the diagonal sum `∑_r φ(r) y_r²`
(with `y_r := ∑_{d, r∣d} μ(d)g(d)/d`) in the multiplicative form whose
Mertens/Riemann asymptotic (sub-step (c)) yields the integral constant. Pure
finite algebra (`Finset.sum_image` reindex + Möbius multiplicativity);
`#print axioms = [propext, Classical.choice, Quot.sound]`. -/
theorem gpy_yvar_substitution (T : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g d / (d : ℝ)
      = (moebius r : ℝ) / (r : ℝ) *
          ∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
              (fun s => Nat.Coprime r s),
            (moebius s : ℝ) * g (r * s) / (s : ℝ) := by
  classical
  set S := T.filter (fun d => r ∣ d) with hS
  have hr0 : r ≠ 0 := by omega
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x / r = y / r → x = y := by
    intro x hx y hy hxy
    simp only [hS, Finset.mem_filter] at hx hy
    rw [← Nat.mul_div_cancel' hx.2, ← Nat.mul_div_cancel' hy.2, hxy]
  have hreindex : ∑ d ∈ S, (moebius d : ℝ) * g d / (d : ℝ)
      = ∑ s ∈ S.image (fun d => d / r),
          (moebius (r * s) : ℝ) * g (r * s) / ((r * s : ℕ) : ℝ) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [hS, Finset.mem_filter] at hd
    rw [Nat.mul_div_cancel' hd.2]
  rw [hreindex, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hcop : Nat.Coprime r s
  · rw [if_pos hcop, (ArithmeticFunction.isMultiplicative_moebius).map_mul_of_coprime hcop]
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
      push_cast
      field_simp
  · rw [if_neg hcop]
    have hnsf : ¬ Squarefree (r * s) := by
      have hgcd : Nat.gcd r s ≠ 1 := hcop
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgcd
      have hpr : p ∣ r := hpg.trans (Nat.gcd_dvd_left r s)
      have hps : p ∣ s := hpg.trans (Nat.gcd_dvd_right r s)
      intro hsf
      have hu : IsUnit p := hsf p (Nat.mul_dvd_mul hpr hps)
      rw [Nat.isUnit_iff] at hu
      have := hp.one_lt; omega
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    push_cast; ring

/-- **The GPY/Selberg quadratic form is positive semidefinite.** For any real
weight `w` on a finite set `T` of positive integers,
`0 ≤ ∑_{d,e ∈ T} w(d) w(e) / [d,e]`. Immediate from `gpy_diagonalize`: the form
equals `∑_r φ(r) · (∑_{r∣d} w(d)/d)²`, a sum of non-negative terms (`φ(r) ≥ 0`,
square `≥ 0`). This is the matrix-positivity fact `(1/[d,e])_{d,e} ⪰ 0`
underlying every Selberg-sieve majorant — in particular `sieveSum (selberg_nu …)
≥ 0` per coordinate. -/
theorem gpy_quadform_nonneg (T : Finset ℕ) (w : ℕ → ℝ) (hT : ∀ d ∈ T, 1 ≤ d) :
    0 ≤ ∑ d ∈ T, ∑ e ∈ T, w d * w e / (Nat.lcm d e : ℝ) := by
  classical
  rw [gpy_diagonalize T (T.biUnion (fun d => d.divisors)) w hT
        (fun d hd r hrd => Finset.mem_biUnion.mpr
          ⟨d, hd, Nat.mem_divisors.mpr ⟨hrd, by have := hT d hd; omega⟩⟩)]
  refine Finset.sum_nonneg (fun r _ => ?_)
  positivity

/-- **Heuristic main term factorizes over coordinates.** When the lattice-point
count in the expansion is replaced by its GPY main value `M / ∏ᵢ [dᵢ,eᵢ]`
(`M = (B−A)/W` shared, `lattice_count_main_term`), the resulting sum over the
product lattice `∏ᵢ (Dset i)` factors into a product of independent
per-coordinate sums:
`∑_P (∏ᵢ aᵢ(Pᵢ))·(M/∏ᵢ[Pᵢ]) = M · ∏ᵢ (∑_{de∈Dset i} aᵢ(de)/[de])`.
Pure algebra (`Finset.prod_univ_sum` distributing `∏∑ = ∑_P ∏`, plus
`prod_div_distrib`). This is the structural step turning the (heuristic) GPY
main term into a `k`-fold product of 1-D quadratic forms. -/
theorem piFinset_lattice_main_factor {k : ℕ} (Dset : Fin k → Finset (ℕ × ℕ))
    (a : Fin k → (ℕ × ℕ) → ℝ) (M : ℝ) :
    ∑ P ∈ Fintype.piFinset Dset,
        (∏ i : Fin k, a i (P i)) * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))
      = M * ∏ i : Fin k, ∑ de ∈ Dset i, a i de / (Nat.lcm de.1 de.2 : ℝ) := by
  classical
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.prod_div_distrib]
  ring

/-- **Heuristic GPY main term, fully diagonalized.** Combining
`piFinset_lattice_main_factor` (factor over coordinates), `Finset.sum_product`
(each coordinate's `(d,e)`-pair sum is a double sum), and
`gpy_diagonalize_moebius` (diagonalize each 1-D quadratic form), the heuristic
main term of the separable sieve expansion — with the lattice count replaced by
`M/∏ᵢ[dᵢ,eᵢ]` and the GPY weight `aᵢ(d,e) = μ(d)Fᵢ·μ(e)Fᵢ` (the
`sieveSum_selberg_nu_separable_expand` summand) — equals
`M · ∏ᵢ ∑_r φ(r) (∑_{d∈Dᵢ, r∣d} μ(d)Fᵢ(log d/log R)/d)²`,
a product of `k` diagonalized 1-D Selberg quadratic forms. This is the complete
algebraic skeleton of the (s1) main term; only the *asymptotic* evaluation of
each diagonal sum (sub-step (c), `R→∞`) and the off-diagonal count discrepancy
remain. -/
theorem heuristic_main_term_diagonalized {k : ℕ} (D Rset : Fin k → Finset ℕ)
    (Fs : Fin k → ℝ → ℝ) (R M : ℝ)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d)
    (hR : ∀ i, ∀ d ∈ D i, ∀ r, r ∣ d → r ∈ Rset i) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        (∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Fs i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Fs i (Real.log (P i).2 / Real.log R)))
        * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))
      = M * ∏ i : Fin k, ∑ r ∈ Rset i, (Nat.totient r : ℝ)
          * (∑ d ∈ (D i).filter (fun d => r ∣ d),
              (moebius d : ℝ) * Fs i (Real.log d / Real.log R) / (d : ℝ)) ^ 2 := by
  classical
  rw [piFinset_lattice_main_factor (fun i => D i ×ˢ D i)
      (fun i de => ((moebius de.1 : ℝ) * Fs i (Real.log de.1 / Real.log R))
        * ((moebius de.2 : ℝ) * Fs i (Real.log de.2 / Real.log R))) M]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.sum_product]
  exact gpy_diagonalize_moebius (D i) (Rset i)
    (fun d => Fs i (Real.log d / Real.log R)) (hD i) (hR i)

/-- **(s1) reduction: `sieveSum = heuristic main + correction`.** For *any*
chosen main value `M`, the separable Selberg sieve sum splits exactly as
`sieveSum = ∑_P coeffₚ·(M/∏ᵢ[Pᵢ]) + ∑_P coeffₚ·(countₚ − M/∏ᵢ[Pᵢ])`,
the first summand being the heuristic main term (`= M·∏ᵢ diagonalized quadratic
form` via `heuristic_main_term_diagonalized` once `M = (B−A)/W`), the second the
**correction** `∑_P coeffₚ·(countₚ − M/∏ᵢ[Pᵢ])` that the analytic estimate must
show is `o(main)`. Pure algebra (add and subtract `M/∏[·]` termwise on
`sieveSum_selberg_nu_separable_expand`); isolates the exact remaining analytic
obligation (sub-step (c) asymptotic + off-diagonal/error discrepancy). -/
theorem sieveSum_separable_eq_heuristic_add_correction (k : ℕ) (Fs : Fin k → ℝ → ℝ)
    (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) (M : ℝ) :
    sieveSum (selberg_nu_separable k Fs H R) b W x
      = (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs i (Real.log (P i).2 / Real.log R)))
          * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      + (∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs i (Real.log (P i).2 / Real.log R)))
          * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                (fun m => ∀ i : Fin k,
                  (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
              - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))) := by
  rw [sieveSum_selberg_nu_separable_expand k Fs H R b W x hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- **The GPY variable `y_r` vanishes off the squarefree locus.** If `r` is not
squarefree then `∑_{d∈T, r∣d} μ(d)g(d)/d = 0`: every `d` divisible by a
non-squarefree `r` is itself non-squarefree, so `μ(d) = 0`. -/
theorem gpy_yvar_eq_zero_of_not_squarefree (T : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hr : ¬ Squarefree r) :
    ∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g d / (d : ℝ) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun d hd => ?_)
  obtain ⟨_, hrd⟩ := Finset.mem_filter.mp hd
  have hdnsf : ¬ Squarefree d := fun hsf => hr (hsf.squarefree_of_dvd hrd)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdnsf]
  simp

/-- **The diagonalized Selberg form is supported on squarefree `r`.** Combining
`gpy_diagonalize_moebius` with `gpy_yvar_eq_zero_of_not_squarefree`, the diagonal
sum restricts to squarefree `r`:
`∑_{d,e}μ(d)μ(e)g(d)g(e)/[d,e] = ∑_{r∈R, Squarefree r} φ(r)(∑_{r∣d}μ(d)g(d)/d)²`.
This is the reduction to the clean multiplicative locus (where `φ(r)/r² =
∏_{p∣r}(p−1)/p²`) on which the sub-step (c) asymptotic is computed. -/
theorem gpy_diagonalize_moebius_squarefree (T R : Finset ℕ) (g : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g d * ((moebius e : ℝ) * g e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R.filter (fun r => Squarefree r), (Nat.totient r : ℝ)
          * (∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g d / (d : ℝ)) ^ 2 := by
  classical
  rw [gpy_diagonalize_moebius T R g hT hR, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h : Squarefree r
  · rw [if_pos h]
  · rw [if_neg h, gpy_yvar_eq_zero_of_not_squarefree T g r h]
    ring

/-- **Diagonal Selberg form, asymptotic-ready (squarefree `r`, `y_r`
substituted).** Capstone of the sub-step (c) algebra: combining
`gpy_diagonalize_moebius_squarefree` (restrict to squarefree `r`),
`gpy_yvar_substitution` (`y_r = (μ(r)/r)·z_r` with `z_r` the coprime-restricted
sum), and `μ(r)² = 1` on the squarefree locus, the Selberg quadratic form equals
`∑_{r∈R squarefree} (φ(r)/r²) · (∑_{s,(r,s)=1} μ(s)g(r·s)/s)²`.
This is the canonical form the sub-step (c) asymptotic (`R→∞`) consumes: the
coefficient `φ(r)/r² = ∏_{p∣r}(p−1)/p²` is multiplicative in `r`, and the inner
`z_r` is a coprime-restricted Möbius sum. -/
theorem gpy_diagonal_asymptotic_form (T R : Finset ℕ) (g : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g d * ((moebius e : ℝ) * g e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R.filter (fun r => Squarefree r), ((Nat.totient r : ℝ) / (r : ℝ) ^ 2)
          * (∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * g (r * s) / (s : ℝ)) ^ 2 := by
  classical
  rw [gpy_diagonalize_moebius_squarefree T R g hT hR]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hsf : Squarefree r := (Finset.mem_filter.mp hr).2
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hsf.ne_zero
  rw [gpy_yvar_substitution T g r hr1, mul_pow, div_pow]
  have hmu : ((moebius r : ℝ)) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  rw [hmu]
  ring

/-- **(s1) reduction for the FULL `selberg_nu` weight.** The general-basis
analogue of `sieveSum_separable_eq_heuristic_add_correction` — the form
`s1_holds_from_nonprime_asym` actually uses (general `J, c, Fs`). For any chosen
main value `M`, the Selberg sieve sum splits exactly as `heuristic main +
correction`, the heuristic part carrying the `M/∏ᵢ[Pᵢ]` GPY main value and the
correction `∑_{j,j',P} cⱼcⱼ'·coeff·(countₚ − M/∏ᵢ[Pᵢ])` being the analytic
obligation. Pure termwise add/subtract on `sieveSum_selberg_nu_expand`. -/
theorem sieveSum_selberg_nu_eq_heuristic_add_correction (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) (M : ℝ) :
    sieveSum (selberg_nu k J c Fs H R) b W x
      = (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      + (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                  (fun m => ∀ i : Fin k,
                    (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
                - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))) := by
  rw [sieveSum_selberg_nu_expand k J c Fs H R b W x hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- **(s2) reduction (theta-weighted sister).** For an *arbitrary* per-tuple main
value `mθ : P ↦ ℝ`, the prime-weighted Selberg sieve sum `sieveThetaSum` splits
as `heuristic main + correction`, mirroring the (s1) reduction. The natural
choice of `mθ P` is the EH/BV-supplied estimate of the theta-weighted lattice
count `∑_{m∈lattice} θ(m+h_{i₀})`; the correction
`∑_{j,j',P} cⱼcⱼ'·coeff·(θ-count − mθ)` is the obligation `s2` discharges from
the level of distribution. Pure termwise add/subtract on
`sieveThetaSum_selberg_nu_expand`. -/
theorem sieveThetaSum_selberg_nu_eq_heuristic_add_correction (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W i₀ : ℕ) (x : ℝ) (hx : 0 < x)
    (mθ : (Fin k → ℕ × ℕ) → ℝ) :
    sieveThetaSum (selberg_nu k J c Fs H R) H i₀ b W x
      = (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * mθ P)
      + (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * ((∑ m ∈ ((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                  (fun m => ∀ i : Fin k,
                    (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0)),
                  primeTheta (m + H.getD i₀ 0))
                - mθ P)) := by
  rw [sieveThetaSum_selberg_nu_expand k J c Fs H R b W i₀ x hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- **Correction split: diagonal error + off-diagonal main.** The correction
sum `∑_P wₚ·(valₚ − mainₚ)` (the obligation isolated by the `*_heuristic_add_correction`
reductions, with `val = count`, `main = M/∏[Pᵢ]`) splits, *given* that `val`
vanishes off the diagonal (the W-trick fact `lattice_count_pair_offdiag_vanish`
⟹ off-diagonal lattice counts are `0`), into
`(∑_{diag} wₚ(valₚ−mainₚ)) + (∑_{¬diag} wₚ(−mainₚ))`: the first is the diagonal
`O(1)` error (bounded by `∑_{diag}|wₚ|` via `lattice_count_main_term`), the
second the **off-diagonal heuristic main** (the "singular series" discrepancy).
This is the organizational step routing the correction to its two analytic
sub-obligations. Pure algebra (`Finset.sum_filter_add_sum_filter_not` + `val=0`
off-diagonal). -/
theorem correction_split_offdiag {ι : Type*} (s : Finset ι) (w val main : ι → ℝ)
    (diag : ι → Prop) [DecidablePred diag]
    (hvanish : ∀ P ∈ s, ¬ diag P → val P = 0) :
    ∑ P ∈ s, w P * (val P - main P)
      = (∑ P ∈ s.filter diag, w P * (val P - main P))
        + (∑ P ∈ s.filter (fun P => ¬ diag P), w P * (- main P)) := by
  rw [← Finset.sum_filter_add_sum_filter_not s diag (fun P => w P * (val P - main P))]
  congr 1
  refine Finset.sum_congr rfl (fun P hP => ?_)
  rw [Finset.mem_filter] at hP
  rw [hvanish P hP.1 hP.2]
  ring

/-- **Diagonal `O(1)`-error bound.** If `|valₚ − mainₚ| ≤ 1` for every `P ∈ s`
(the diagonal lattice count vs its GPY main value, `lattice_count_main_term`),
then `|∑_P wₚ(valₚ − mainₚ)| ≤ ∑_P |wₚ|`. So the diagonal-error piece of the
correction (`correction_split_offdiag`) is controlled by the total weight
`∑_{diag}|coeffₚ|` — reducing that analytic sub-obligation to a divisor-sum size
bound `∑|coeff| = o(main)`. Triangle inequality + `|val−main| ≤ 1`. -/
theorem diag_error_bound {ι : Type*} (s : Finset ι) (w val main : ι → ℝ)
    (h : ∀ P ∈ s, |val P - main P| ≤ 1) :
    |∑ P ∈ s, w P * (val P - main P)| ≤ ∑ P ∈ s, |w P| := by
  calc |∑ P ∈ s, w P * (val P - main P)|
      ≤ ∑ P ∈ s, |w P * (val P - main P)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ P ∈ s, |w P| * |val P - main P| := by
          refine Finset.sum_congr rfl (fun P _ => ?_); rw [abs_mul]
    _ ≤ ∑ P ∈ s, |w P| * 1 :=
          Finset.sum_le_sum (fun P hP =>
            mul_le_mul_of_nonneg_left (h P hP) (abs_nonneg _))
    _ = ∑ P ∈ s, |w P| := by simp

/-- **Full correction bound.** Combining `correction_split_offdiag` (split on the
diagonal, off-diagonal count `= 0`), `diag_error_bound` (diagonal `O(1)` error),
and the triangle inequality: the whole correction is bounded by the diagonal
total weight plus the off-diagonal heuristic main term,
`|∑_P wₚ(valₚ−mainₚ)| ≤ (∑_{diag}|wₚ|) + |∑_{¬diag} wₚ(−mainₚ)|`.
So `s1`'s analytic obligation `correction = o(main)` reduces to the two clean
estimates `∑_{diag}|coeff| = o(main)` (divisor-sum size) and
`∑_{¬diag} coeff·main = o(main)` (singular-series discrepancy). -/
theorem correction_abs_bound {ι : Type*} (s : Finset ι) (w val main : ι → ℝ)
    (diag : ι → Prop) [DecidablePred diag]
    (hvanish : ∀ P ∈ s, ¬ diag P → val P = 0)
    (herr : ∀ P ∈ s.filter diag, |val P - main P| ≤ 1) :
    |∑ P ∈ s, w P * (val P - main P)|
      ≤ (∑ P ∈ s.filter diag, |w P|)
        + |∑ P ∈ s.filter (fun P => ¬ diag P), w P * (- main P)| := by
  rw [correction_split_offdiag s w val main diag hvanish]
  refine (abs_add_le _ _).trans ?_
  gcongr
  exact diag_error_bound (s.filter diag) w val main herr

/-- **Off-diagonal heuristic-main absolute bound (leaf 3 narrowing).** When the heuristic main
`main P ≥ 0`, the off-diagonal main term `|∑_{¬diag} wₚ·(−mainₚ)|` is bounded by the *absolute*
weighted sum `∑_{¬diag} |wₚ|·mainₚ` (triangle inequality + `|wₚ·(−mainₚ)| = |wₚ|·mainₚ`). Turns the
signed off-diagonal obligation into a clean nonnegative size bound. -/
theorem offdiag_main_abs_le {ι : Type*} (s : Finset ι) (w main : ι → ℝ)
    (hmain : ∀ P ∈ s, 0 ≤ main P) :
    |∑ P ∈ s, w P * (- main P)| ≤ ∑ P ∈ s, |w P| * main P := by
  calc |∑ P ∈ s, w P * (- main P)|
      ≤ ∑ P ∈ s, |w P * (- main P)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ P ∈ s, |w P| * main P := by
        refine Finset.sum_congr rfl (fun P hP => ?_)
        rw [abs_mul, abs_neg, abs_of_nonneg (hmain P hP)]

/-- **Fully-explicit correction bound (s1 obligation, both halves nonnegative).** Combines
`correction_abs_bound` (split + diagonal `O(1)` error) with `offdiag_main_abs_le` (off-diagonal main
`≥ 0`): the whole correction is bounded by the diagonal total weight `∑_{diag}|wₚ|` PLUS the
off-diagonal weighted-main sum `∑_{¬diag}|wₚ|·mainₚ`. So `s1`'s analytic obligation `correction =
o(main)` reduces to two CLEAN nonnegative size estimates: `∑_{diag}|wₚ| = o(main)` (leaf 2, DONE via
`diagonal_weight_le_hyperbola`) and `∑_{¬diag}|wₚ|·mainₚ = o(main)` (leaf 3, the singular-series
discrepancy). -/
theorem correction_abs_bound_offdiag {ι : Type*} (s : Finset ι) (w val main : ι → ℝ)
    (diag : ι → Prop) [DecidablePred diag]
    (hvanish : ∀ P ∈ s, ¬ diag P → val P = 0)
    (herr : ∀ P ∈ s.filter diag, |val P - main P| ≤ 1)
    (hmain : ∀ P ∈ s.filter (fun P => ¬ diag P), 0 ≤ main P) :
    |∑ P ∈ s, w P * (val P - main P)|
      ≤ (∑ P ∈ s.filter diag, |w P|)
        + ∑ P ∈ s.filter (fun P => ¬ diag P), |w P| * main P := by
  refine (correction_abs_bound s w val main diag hvanish herr).trans ?_
  gcongr
  exact offdiag_main_abs_le (s.filter (fun P => ¬ diag P)) w main hmain

/-- **The Möbius-weighted (Selberg) quadratic form is PSD.** Direct instance of
`gpy_quadform_nonneg` at `w = μ·g` (the `lambdaTransform` summand): the
per-coordinate GPY quadratic form `∑_{d,e} μ(d)g(d)·μ(e)g(e)/[d,e]` is `≥ 0`. -/
theorem gpy_quadform_moebius_nonneg (T : Finset ℕ) (g : ℕ → ℝ) (hT : ∀ d ∈ T, 1 ≤ d) :
    0 ≤ ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g d * ((moebius e : ℝ) * g e) / (Nat.lcm d e : ℝ) :=
  gpy_quadform_nonneg T (fun d => (moebius d : ℝ) * g d) hT

/-- **Bilinear GPY diagonalization.** The polarized version of `gpy_diagonalize`:
for *two different* weights `w₁, w₂` on `T`, the bilinear Selberg form
diagonalizes into a product of the two `y`-variables,
`∑_{d,e} w₁(d) w₂(e)/[d,e] = ∑_r φ(r) (∑_{r∣d} w₁(d)/d)(∑_{r∣e} w₂(e)/e)`.
This is the form the *cross terms* `j ≠ j'` of the full `selberg_nu`
(`J`-term basis) heuristic main term require — `gpy_diagonalize` only covers the
single-weight diagonal `j = j'`. Proof mirrors `gpy_diagonalize`
(`Nat.sum_totient` divisor expansion of the gcd, swap `r` outward, factor the
per-`r` slice as a product of two sums via `Finset.sum_mul_sum`). -/
theorem gpy_diagonalize_bilinear (T R : Finset ℕ) (w₁ w₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T, w₁ d * w₂ e / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, (Nat.totient r : ℝ)
          * ((∑ d ∈ T.filter (fun d => r ∣ d), w₁ d / (d : ℝ))
             * (∑ e ∈ T.filter (fun e => r ∣ e), w₂ e / (e : ℝ))) := by
  classical
  have step1 : ∀ d ∈ T, ∀ e ∈ T,
      w₁ d * w₂ e / (Nat.lcm d e : ℝ)
        = ∑ r ∈ R, (if r ∣ d ∧ r ∣ e then (Nat.totient r : ℝ) else 0)
            * (w₁ d / (d:ℝ)) * (w₂ e / (e:ℝ)) := by
    intro d hd e he
    have hd1 := hT d hd; have he1 := hT e he
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hd1
    have he0 : (e:ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp he1
    have hgcd0 : Nat.gcd d e ≠ 0 := Nat.gcd_ne_zero_left (by omega)
    have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d:ℝ) * (e:ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hlcm0 : (Nat.lcm d e : ℝ) ≠ 0 := by
      have : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      exact_mod_cast this
    have hrw : w₁ d * w₂ e / (Nat.lcm d e : ℝ)
        = (Nat.gcd d e : ℝ) * ((w₁ d / (d:ℝ)) * (w₂ e / (e:ℝ))) := by
      field_simp
      linear_combination (-(w₁ d * w₂ e)) * hgl
    rw [hrw]
    have htot : (Nat.gcd d e : ℝ) = ∑ r ∈ (Nat.gcd d e).divisors, (Nat.totient r : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast (Nat.sum_totient _).symm
    have hfilter : (Nat.gcd d e).divisors = R.filter (fun r => r ∣ d ∧ r ∣ e) := by
      ext r
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hrd, hre⟩, _⟩
        exact ⟨hR d hd r hrd, hrd, hre⟩
      · rintro ⟨_, hrd, hre⟩
        exact ⟨⟨hrd, hre⟩, hgcd0⟩
    rw [htot, hfilter, Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => step1 d hd e he))]
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ T) => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have key1 : ∑ d ∈ T.filter (fun d => r ∣ d), w₁ d / (d:ℝ)
      = ∑ d ∈ T, (if r ∣ d then (1:ℝ) else 0) * (w₁ d / (d:ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases h : r ∣ d <;> simp [h]
  have key2 : ∑ e ∈ T.filter (fun e => r ∣ e), w₂ e / (e:ℝ)
      = ∑ e ∈ T, (if r ∣ e then (1:ℝ) else 0) * (w₂ e / (e:ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : r ∣ e <;> simp [h]
  rw [key1, key2, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h1 : r ∣ d <;> by_cases h2 : r ∣ e <;> simp [h1, h2, mul_assoc]

/-- **Bilinear GPY diagonalization, Möbius-weighted.** With the two GPY weights
`w₁(d) = μ(d)g₁(d)`, `w₂(e) = μ(e)g₂(e)` (the `lambdaTransform` summands for two
different basis functions `g₁, g₂`), the cross Selberg form diagonalizes:
`∑_{d,e} μ(d)g₁(d)·μ(e)g₂(e)/[d,e] = ∑_r φ(r) (∑_{r∣d}μ(d)g₁(d)/d)(∑_{r∣e}μ(e)g₂(e)/e)`.
Direct instance of `gpy_diagonalize_bilinear`. The `j = j'` case (`g₁ = g₂`)
recovers `gpy_diagonalize_moebius`. -/
theorem gpy_diagonalize_moebius_bilinear (T R : Finset ℕ) (g₁ g₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, (Nat.totient r : ℝ)
          * ((∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g₁ d / (d : ℝ))
             * (∑ e ∈ T.filter (fun e => r ∣ e), (moebius e : ℝ) * g₂ e / (e : ℝ))) :=
  gpy_diagonalize_bilinear T R (fun d => (moebius d : ℝ) * g₁ d)
    (fun e => (moebius e : ℝ) * g₂ e) hT hR

/-- **GPY `y_r`-form diagonalization (bilinear), Path-Y weight `μ²/φ`.** The
exact algebraic bridge from the diagonalized Selberg form's natural weight `φ(r)`
(`gpy_diagonalize_moebius_bilinear`) to Maynard's **Path-Y** weight `μ²(r)/φ(r)`,
by absorbing one factor `φ(r)` into each inner divisor sum. Defining the GPY
`y`-variable `y_{i,r} := φ(r)·∑_{d∈T, r∣d} μ(d)gᵢ(d)/d`,
`∑_{d,e} μ(d)g₁(d)·μ(e)g₂(e)/[d,e] = ∑_{r∈R} (μ²(r)/φ(r))·y_{1,r}·y_{2,r}`.
Holds termwise: on squarefree `r`, `μ²(r)=1` and `(μ²/φ)·(φ y₁)(φ y₂) = φ·y₁y₂`
recovers `gpy_diagonalize_moebius_bilinear`'s summand; off the squarefree locus
`μ²(r)=0` *and* `y_{i,r}=0` (`gpy_yvar_eq_zero_of_not_squarefree`), so both sides
vanish. This exhibits the `μ²/φ` weight that the entire Path-Y Riemann ladder
(`WeightedRiemann*`, `S1MainTermDecomp`) is built around — the inner `y_{i,r}` is
exactly what the smoothing step `y_{i,r} ≈ gᵢ(log r/log R)` then replaces, leaving
`∑_r (μ²/φ)(r)·gᵢ(log r/log R)·gⱼ(log r/log R)` (the 1-D `nestedLogSumW` block). -/
theorem gpy_diagonalize_moebius_bilinear_yform (T R : Finset ℕ) (g₁ g₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
          * (((Nat.totient r : ℝ) * ∑ d ∈ T.filter (fun d => r ∣ d),
                (moebius d : ℝ) * g₁ d / (d : ℝ))
             * ((Nat.totient r : ℝ) * ∑ e ∈ T.filter (fun e => r ∣ e),
                (moebius e : ℝ) * g₂ e / (e : ℝ))) := by
  classical
  rw [gpy_diagonalize_moebius_bilinear T R g₁ g₂ hT hR]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h : Squarefree r
  · have hmu : ((moebius r : ℝ)) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    have hpos : 0 < Nat.totient r := Nat.totient_pos.mpr (Nat.pos_of_ne_zero h.ne_zero)
    have hne : (Nat.totient r : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hmu]
    field_simp
  · rw [gpy_yvar_eq_zero_of_not_squarefree T g₁ r h]
    ring

/-- **GPY `y_r`-form diagonalization (single), Path-Y weight `μ²/φ`.** The
`g₁ = g₂ = g` instance of `gpy_diagonalize_moebius_bilinear_yform`:
`∑_{d,e} μ(d)g(d)·μ(e)g(e)/[d,e] = ∑_{r∈R} (μ²(r)/φ(r))·y_r²`,
with `y_r := φ(r)·∑_{d∈T, r∣d} μ(d)g(d)/d`. The Path-Y companion of
`gpy_diagonal_asymptotic_form` (whose `z_r` route carries the singular `φ/r²`
weight). -/
theorem gpy_diagonalize_moebius_yform (T R : Finset ℕ) (g : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g d * ((moebius e : ℝ) * g e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
          * ((Nat.totient r : ℝ) * ∑ d ∈ T.filter (fun d => r ∣ d),
                (moebius d : ℝ) * g d / (d : ℝ)) ^ 2 := by
  rw [gpy_diagonalize_moebius_bilinear_yform T R g g hT hR]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

/-- **The Path-Y `y_r`-form and the Polymath8b `z_r`-form of the diagonalized
Selberg quadratic form agree** (cross-validation of `gpy_diagonalize_moebius_yform`).
Both `gpy_diagonalize_moebius_yform` (Path-Y: weight `μ²/φ`, GPY variable
`y_r = φ(r)·∑_{r∣d}μ(d)g(d)/d`) and `gpy_diagonal_asymptotic_form` (Polymath8b
`d`-space: weight `φ/r²`, coprime-restricted variable `z_r = ∑_{(r,s)=1}μ(s)g(rs)/s`)
equal the same quadratic form `∑_{d,e}μ(d)g(d)μ(e)g(e)/[d,e]`, so their right-hand
sides are equal:
`∑_{r∈R} (μ²/φ)(r)·y_r² = ∑_{r∈R sf} (φ(r)/r²)·z_r²`.
Termwise this is the substitution `y_r = (μ(r)φ(r)/r)·z_r` (`gpy_yvar_substitution`)
with `μ(r)²=1` on the squarefree locus — the exact bridge between the two
conventions. The two asymptotics differ only in *which* sum you evaluate: the `z_r`
route's `∑μ(s)/s` is PNT-strength (a contour in Polymath8b), while the `y_r` route's
`∑(μ²/φ)·y_r²` is contour-free (positive Mertens) — hence Path Y. -/
theorem gpy_diagonal_yform_eq_zform (T R : Finset ℕ) (g : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d)
    (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    (∑ r ∈ R, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
        * ((Nat.totient r : ℝ) * ∑ d ∈ T.filter (fun d => r ∣ d),
              (moebius d : ℝ) * g d / (d : ℝ)) ^ 2)
      = ∑ r ∈ R.filter (fun r => Squarefree r), ((Nat.totient r : ℝ) / (r : ℝ) ^ 2)
          * (∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * g (r * s) / (s : ℝ)) ^ 2 := by
  rw [← gpy_diagonalize_moebius_yform T R g hT hR, gpy_diagonal_asymptotic_form T R g hT hR]

/-- **Cross heuristic GPY main term, fully diagonalized** (general `J`-basis).
The bilinear analogue of `heuristic_main_term_diagonalized`: the heuristic main
term of one `(j, j')` cross block of `sieveSum_selberg_nu_eq_heuristic_add_correction`
— weight `aᵢ(d,e) = μ(d)Gs₁ᵢ(log d/log R)·μ(e)Gs₂ᵢ(log e/log R)` with `Gs₁ = Fs j`,
`Gs₂ = Fs j'` — equals
`M · ∏ᵢ ∑_r φ(r) (∑_{d∈Dᵢ, r∣d} μ(d)Gs₁ᵢ/d)(∑_{e∈Dᵢ, r∣e} μ(e)Gs₂ᵢ/e)`,
a product of `k` diagonalized bilinear Selberg forms. Combining this over the
`∑_{j,j'} cⱼcⱼ'` linear combination gives the FULL `selberg_nu` heuristic main
term in diagonalized form (the `j = j'` summands recover
`heuristic_main_term_diagonalized`). This completes the algebraic diagonalization
of the general (non-separable, `J`-term) GPY main term; only the per-factor
*asymptotic* (sub-step (c) `R→∞`) and the off-diagonal count discrepancy remain. -/
theorem heuristic_main_term_diagonalized_bilinear {k : ℕ} (D Rset : Fin k → Finset ℕ)
    (Gs₁ Gs₂ : Fin k → ℝ → ℝ) (R M : ℝ)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d)
    (hR : ∀ i, ∀ d ∈ D i, ∀ r, r ∣ d → r ∈ Rset i) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        (∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Gs₁ i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Gs₂ i (Real.log (P i).2 / Real.log R)))
        * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))
      = M * ∏ i : Fin k, ∑ r ∈ Rset i, (Nat.totient r : ℝ)
          * ((∑ d ∈ (D i).filter (fun d => r ∣ d),
                (moebius d : ℝ) * Gs₁ i (Real.log d / Real.log R) / (d : ℝ))
             * (∑ e ∈ (D i).filter (fun e => r ∣ e),
                (moebius e : ℝ) * Gs₂ i (Real.log e / Real.log R) / (e : ℝ))) := by
  classical
  rw [piFinset_lattice_main_factor (fun i => D i ×ˢ D i)
      (fun i de => ((moebius de.1 : ℝ) * Gs₁ i (Real.log de.1 / Real.log R))
        * ((moebius de.2 : ℝ) * Gs₂ i (Real.log de.2 / Real.log R))) M]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.sum_product]
  exact gpy_diagonalize_moebius_bilinear (D i) (Rset i)
    (fun d => Gs₁ i (Real.log d / Real.log R))
    (fun e => Gs₂ i (Real.log e / Real.log R)) (hD i) (hR i)

/-- Every divisor in a `sieveDivisors` family is a positive integer (`divisors`
of a nonzero `n + hᵢ` are all `≥ 1`). Supplies the `1 ≤ d` hypothesis of the
GPY diagonalization lemmas at the concrete sieve lattice. -/
theorem sieveDivisors_pos {H : List ℕ} {i b W : ℕ} {x : ℝ} {d : ℕ}
    (hd : d ∈ sieveDivisors H i b W x) : 1 ≤ d := by
  rw [sieveDivisors, Finset.mem_biUnion] at hd
  obtain ⟨n, _, hdn⟩ := hd
  exact Nat.pos_of_mem_divisors hdn

/-- `sieveDivisors` is divisor-closed: if `d` lies in the family and `r ∣ d`,
then `r` also lies in the family (same `n`, since `r ∣ d ∣ (n + hᵢ)`). Supplies
the divisor-closure hypothesis (`Rset = sieveDivisors`) of the GPY
diagonalization lemmas at the concrete sieve lattice. -/
theorem sieveDivisors_dvd_closed {H : List ℕ} {i b W : ℕ} {x : ℝ} {d : ℕ}
    (hd : d ∈ sieveDivisors H i b W x) {r : ℕ} (hr : r ∣ d) :
    r ∈ sieveDivisors H i b W x := by
  rw [sieveDivisors, Finset.mem_biUnion] at hd ⊢
  obtain ⟨n, hn, hdn⟩ := hd
  rw [Nat.mem_divisors] at hdn
  exact ⟨n, hn, Nat.mem_divisors.mpr ⟨hr.trans hdn.1, hdn.2⟩⟩

/-- **Full `selberg_nu` heuristic GPY main term, fully diagonalized.** Applying
`heuristic_main_term_diagonalized_bilinear` to every `(j, j')` cross block of the
heuristic main term produced by `sieveSum_selberg_nu_eq_heuristic_add_correction`
(at the concrete sieve lattice `D = Rset = sieveDivisors`, closure supplied by
`sieveDivisors_pos`/`sieveDivisors_dvd_closed`): the heuristic GPY main term of
the general `J`-basis Selberg sieve equals
`∑_{j,j'} cⱼcⱼ' · M · ∏ᵢ ∑_r φ(r) (∑_{r∣d} μ(d)Fⱼᵢ/d)(∑_{r∣e} μ(e)Fⱼ'ᵢ/e)`,
a `J²`-fold combination of products of `k` diagonalized 1-D bilinear Selberg
forms. This is the complete algebraic diagonalization of the (non-separable,
general) GPY main term at the concrete lattice — the exact object whose `R→∞`
asymptotic (sub-step (c)) yields the `Mₖ(F)` constant. -/
theorem heuristic_main_selberg_nu_diagonalized (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (M : ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
          * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          (M * ∏ i : Fin k, ∑ r ∈ sieveDivisors H i.val b W x, (Nat.totient r : ℝ)
            * ((∑ d ∈ (sieveDivisors H i.val b W x).filter (fun d => r ∣ d),
                  (moebius d : ℝ) * Fs j i (Real.log d / Real.log R) / (d : ℝ))
               * (∑ e ∈ (sieveDivisors H i.val b W x).filter (fun e => r ∣ e),
                  (moebius e : ℝ) * Fs j' i (Real.log e / Real.log R) / (e : ℝ)))) := by
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [heuristic_main_term_diagonalized_bilinear
    (fun i => sieveDivisors H i.val b W x) (fun i => sieveDivisors H i.val b W x)
    (fun i => Fs j i) (fun i => Fs j' i) R M
    (fun _ _ hd => sieveDivisors_pos hd)
    (fun _ _ hd r hr => sieveDivisors_dvd_closed hd hr)]

/-- **Bilinear diagonalized form, restricted to squarefree `r`.** The bilinear
analogue of `gpy_diagonalize_moebius_squarefree`: off the squarefree locus the
`g₁` factor `∑_{r∣d} μ(d)g₁(d)/d` vanishes (`gpy_yvar_eq_zero_of_not_squarefree`),
killing the whole product, so the cross diagonal sum restricts to squarefree `r`. -/
theorem gpy_diagonalize_moebius_bilinear_squarefree (T R : Finset ℕ) (g₁ g₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d) (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R.filter (fun r => Squarefree r), (Nat.totient r : ℝ)
          * ((∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g₁ d / (d : ℝ))
             * (∑ e ∈ T.filter (fun e => r ∣ e), (moebius e : ℝ) * g₂ e / (e : ℝ))) := by
  classical
  rw [gpy_diagonalize_moebius_bilinear T R g₁ g₂ hT hR, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases h : Squarefree r
  · rw [if_pos h]
  · rw [if_neg h, gpy_yvar_eq_zero_of_not_squarefree T g₁ r h]
    ring

/-- **Bilinear diagonal Selberg form, asymptotic-ready** (cross `j ≠ j'` block).
The bilinear analogue of `gpy_diagonal_asymptotic_form`: combining
`gpy_diagonalize_moebius_bilinear_squarefree`, `gpy_yvar_substitution` on both
factors, and `μ(r)² = 1` on the squarefree locus, the cross Selberg form equals
`∑_{r sf} (φ(r)/r²) · z₁ᵣ · z₂ᵣ` with `zᵢᵣ = ∑_{(r,s)=1} μ(s)gᵢ(rs)/s` the
coprime-restricted Möbius sums. This is the canonical bilinear form whose `R→∞`
asymptotic produces each cross main-term constant; the `g₁ = g₂` case recovers
`gpy_diagonal_asymptotic_form`. -/
theorem gpy_diagonal_asymptotic_form_bilinear (T R : Finset ℕ) (g₁ g₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d) (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    ∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)
      = ∑ r ∈ R.filter (fun r => Squarefree r), ((Nat.totient r : ℝ) / (r : ℝ) ^ 2)
          * ((∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * g₁ (r * s) / (s : ℝ))
             * (∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * g₂ (r * s) / (s : ℝ))) := by
  classical
  rw [gpy_diagonalize_moebius_bilinear_squarefree T R g₁ g₂ hT hR]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hsf : Squarefree r := (Finset.mem_filter.mp hr).2
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hsf.ne_zero
  rw [gpy_yvar_substitution T g₁ r hr1, gpy_yvar_substitution T g₂ r hr1]
  have hmu : ((moebius r : ℝ)) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  set Z₁ := ∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s), (moebius s : ℝ) * g₁ (r * s) / (s : ℝ)
  set Z₂ := ∑ s ∈ ((T.filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s), (moebius s : ℝ) * g₂ (r * s) / (s : ℝ)
  have hexp : (Nat.totient r : ℝ)
        * ((moebius r : ℝ) / (r : ℝ) * Z₁ * ((moebius r : ℝ) / (r : ℝ) * Z₂))
      = (moebius r : ℝ) ^ 2 * ((Nat.totient r : ℝ) / (r : ℝ) ^ 2 * (Z₁ * Z₂)) := by
    ring
  rw [hexp, hmu, one_mul]

/-- **Cross heuristic main term in canonical (squarefree-`z`) form.** The
canonical-form analogue of `heuristic_main_term_diagonalized_bilinear`, using
`gpy_diagonal_asymptotic_form_bilinear` for the per-coordinate factor: one
`(j, j')` cross block of the heuristic GPY main term equals
`M · ∏ᵢ ∑_{r sf} (φ(r)/r²) z₁ᵢᵣ z₂ᵢᵣ` with `z` the coprime-restricted Möbius
sums of `Gs₁ᵢ, Gs₂ᵢ`. This is the fully asymptotic-ready object the `R→∞`
limit consumes per coordinate. -/
theorem heuristic_main_term_diagonalized_bilinear_canonical {k : ℕ}
    (D Rset : Fin k → Finset ℕ) (Gs₁ Gs₂ : Fin k → ℝ → ℝ) (R M : ℝ)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d)
    (hR : ∀ i, ∀ d ∈ D i, ∀ r, r ∣ d → r ∈ Rset i) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        (∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Gs₁ i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Gs₂ i (Real.log (P i).2 / Real.log R)))
        * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))
      = M * ∏ i : Fin k, ∑ r ∈ (Rset i).filter (fun r => Squarefree r),
          ((Nat.totient r : ℝ) / (r : ℝ) ^ 2)
          * ((∑ s ∈ (((D i).filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * Gs₁ i (Real.log ((r * s : ℕ) : ℝ) / Real.log R) / (s : ℝ))
             * (∑ s ∈ (((D i).filter (fun d => r ∣ d)).image (fun d => d / r)).filter
                (fun s => Nat.Coprime r s),
              (moebius s : ℝ) * Gs₂ i (Real.log ((r * s : ℕ) : ℝ) / Real.log R) / (s : ℝ))) := by
  classical
  rw [piFinset_lattice_main_factor (fun i => D i ×ˢ D i)
      (fun i de => ((moebius de.1 : ℝ) * Gs₁ i (Real.log de.1 / Real.log R))
        * ((moebius de.2 : ℝ) * Gs₂ i (Real.log de.2 / Real.log R))) M]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.sum_product]
  exact gpy_diagonal_asymptotic_form_bilinear (D i) (Rset i)
    (fun d => Gs₁ i (Real.log d / Real.log R))
    (fun e => Gs₂ i (Real.log e / Real.log R)) (hD i) (hR i)

/-- **Full `selberg_nu` heuristic main term in canonical form.** The capstone of
the algebraic diagonalization: combining `heuristic_main_term_diagonalized_bilinear_canonical`
over the `∑_{j,j'} cⱼcⱼ'` basis combination (at the concrete sieve lattice
`D = Rset = sieveDivisors`), the heuristic GPY main term of the general `J`-basis
Selberg sieve equals
`∑_{j,j'} cⱼcⱼ' · M · ∏ᵢ ∑_{r sf} (φ(r)/r²) z₁ᵢᵣ z₂ᵢᵣ`,
each per-coordinate factor a sum over squarefree `r` of `(φ(r)/r²)` times a
product of coprime-restricted Möbius sums of `Fⱼᵢ, Fⱼ'ᵢ`. This is the exact
object whose `R→∞` asymptotic (sub-step (c)) yields the `Mₖ(F)` GPY constant —
the entire algebraic reduction of the (non-separable, general) main term is now
machine-checked. -/
theorem heuristic_main_selberg_nu_canonical (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (M : ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
          * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          (M * ∏ i : Fin k, ∑ r ∈ (sieveDivisors H i.val b W x).filter (fun r => Squarefree r),
            ((Nat.totient r : ℝ) / (r : ℝ) ^ 2)
            * ((∑ s ∈ (((sieveDivisors H i.val b W x).filter (fun d => r ∣ d)).image
                  (fun d => d / r)).filter (fun s => Nat.Coprime r s),
                (moebius s : ℝ) * Fs j i (Real.log ((r * s : ℕ) : ℝ) / Real.log R) / (s : ℝ))
               * (∑ s ∈ (((sieveDivisors H i.val b W x).filter (fun d => r ∣ d)).image
                  (fun d => d / r)).filter (fun s => Nat.Coprime r s),
                (moebius s : ℝ) * Fs j' i (Real.log ((r * s : ℕ) : ℝ) / Real.log R) / (s : ℝ)))) := by
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [heuristic_main_term_diagonalized_bilinear_canonical
    (fun i => sieveDivisors H i.val b W x) (fun i => sieveDivisors H i.val b W x)
    (fun i => Fs j i) (fun i => Fs j' i) R M
    (fun _ _ hd => sieveDivisors_pos hd)
    (fun _ _ hd r hr => sieveDivisors_dvd_closed hd hr)]

/-- **Cross heuristic main term in Path-Y (`y_r`, `μ²/φ`) form.** The Path-Y
companion of `heuristic_main_term_diagonalized_bilinear_canonical`, using
`gpy_diagonalize_moebius_bilinear_yform` for the per-coordinate factor: one
`(j, j')` cross block of the heuristic GPY main term equals
`M · ∏ᵢ ∑_r (μ²(r)/φ(r)) y₁ᵢᵣ y₂ᵢᵣ` with `yₐᵢᵣ := φ(r)·∑_{d∈Dᵢ, r∣d} μ(d)Gsₐᵢ(log d/log R)/d`
the GPY `y`-variables. The `μ²/φ` weight is precisely the one the Path-Y Riemann
ladder (`WeightedRiemann*`, `S1MainTermDecomp`) consumes; the inner `yₐᵢᵣ` is what
the smoothing step `yₐᵢᵣ ≈ Gsₐᵢ(log r/log R)` (Maynard `PartialSummation`) then
replaces, leaving the `nestedLogSumW (μ²/φ)` block. -/
theorem heuristic_main_term_diagonalized_bilinear_yform {k : ℕ}
    (D Rset : Fin k → Finset ℕ) (Gs₁ Gs₂ : Fin k → ℝ → ℝ) (R M : ℝ)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d)
    (hR : ∀ i, ∀ d ∈ D i, ∀ r, r ∣ d → r ∈ Rset i) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        (∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Gs₁ i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Gs₂ i (Real.log (P i).2 / Real.log R)))
        * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))
      = M * ∏ i : Fin k, ∑ r ∈ Rset i,
          ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
          * (((Nat.totient r : ℝ) * ∑ d ∈ (D i).filter (fun d => r ∣ d),
                (moebius d : ℝ) * Gs₁ i (Real.log d / Real.log R) / (d : ℝ))
             * ((Nat.totient r : ℝ) * ∑ e ∈ (D i).filter (fun e => r ∣ e),
                (moebius e : ℝ) * Gs₂ i (Real.log e / Real.log R) / (e : ℝ))) := by
  classical
  rw [piFinset_lattice_main_factor (fun i => D i ×ˢ D i)
      (fun i de => ((moebius de.1 : ℝ) * Gs₁ i (Real.log de.1 / Real.log R))
        * ((moebius de.2 : ℝ) * Gs₂ i (Real.log de.2 / Real.log R))) M]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.sum_product]
  exact gpy_diagonalize_moebius_bilinear_yform (D i) (Rset i)
    (fun d => Gs₁ i (Real.log d / Real.log R))
    (fun e => Gs₂ i (Real.log e / Real.log R)) (hD i) (hR i)

/-- **Full `selberg_nu` heuristic main term in Path-Y (`y_r`, `μ²/φ`) form.** The
Path-Y companion of `heuristic_main_selberg_nu_canonical`: combining
`heuristic_main_term_diagonalized_bilinear_yform` over the `∑_{j,j'} cⱼcⱼ'` basis
combination (at the concrete sieve lattice `D = Rset = sieveDivisors`), the
heuristic GPY main term of the general `J`-basis Selberg sieve equals
`∑_{j,j'} cⱼcⱼ' · M · ∏ᵢ ∑_r (μ²(r)/φ(r)) y₁ᵢᵣ y₂ᵢᵣ`,
each per-coordinate factor a sum over `r` of the Path-Y weight `μ²(r)/φ(r)` times a
product of GPY `y`-variables of `Fⱼᵢ, Fⱼ'ᵢ`. **This is the heuristic main term in the
exact `μ²/φ` Path-Y shape** that the smoothing step (`yₐᵢᵣ ≈ Fₐᵢ(log r/log R)`,
gap (B)) plus the `nestedLogSumW(μ²/φ)` Riemann ladder (`S1MainTermDecomp`, DONE)
consume — the structural spine of gap (A) in the `y_r`-space convention. -/
theorem heuristic_main_selberg_nu_yform (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (M : ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
            sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
          (∏ i : Fin k,
            ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
              * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
          * (M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ)))
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          (M * ∏ i : Fin k, ∑ r ∈ sieveDivisors H i.val b W x,
            ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
            * (((Nat.totient r : ℝ) * ∑ d ∈ (sieveDivisors H i.val b W x).filter (fun d => r ∣ d),
                  (moebius d : ℝ) * Fs j i (Real.log d / Real.log R) / (d : ℝ))
               * ((Nat.totient r : ℝ) * ∑ e ∈ (sieveDivisors H i.val b W x).filter (fun e => r ∣ e),
                  (moebius e : ℝ) * Fs j' i (Real.log e / Real.log R) / (e : ℝ)))) := by
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
  rw [heuristic_main_term_diagonalized_bilinear_yform
    (fun i => sieveDivisors H i.val b W x) (fun i => sieveDivisors H i.val b W x)
    (fun i => Fs j i) (fun i => Fs j' i) R M
    (fun _ _ hd => sieveDivisors_pos hd)
    (fun _ _ hd r hr => sieveDivisors_dvd_closed hd hr)]

/-- **`sieveSum = Path-Y `y_r`-form main term + correction`** (gap (A) capstone). Composing
`sieveSum_selberg_nu_eq_heuristic_add_correction` (the exact `heuristic_main + correction` split, any
chosen main value `M`) with `heuristic_main_selberg_nu_yform` (heuristic main in the Path-Y `μ²/φ`
`y`-variable form), the literal Selberg sieve sum equals
`∑_{j,j'} cⱼcⱼ'·M·∏ᵢ ∑_r (μ²(r)/φ(r))·y₁ᵢᵣ·y₂ᵢᵣ + correction`,
with `y_{a,i,r} = φ(r)·∑_{d∈Dᵢ, r∣d} μ(d)F_{a,i}(log d/log R)/d` the GPY `y`-variables and the
correction `∑_{j,j',P} cⱼcⱼ'·coeff·(count − M/∏ᵢ[Pᵢ])` the analytic obligation. **This is the entire
algebraic content of gap (A)** in the `y_r`-space convention: the main term is now in EXACTLY the
`μ²/φ` shape the Path-Y Riemann ladder consumes. The two remaining obligations are purely analytic —
(B) the smoothing `y_{a,i,r} ≈ (μ(r)/log R)·F_{a,i}(log r/log R)` (with the antiderivative convention)
feeding the `nestedLogSumW(μ²/φ)` ladder (`S1MainTermDecomp`, DONE), and (C) `correction = o(main)`. -/
theorem sieveSum_selberg_nu_yform_add_correction (k J : ℕ) (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (H : List ℕ) (R : ℝ) (b W : ℕ) (x : ℝ) (hx : 0 < x) (M : ℝ) :
    sieveSum (selberg_nu k J c Fs H R) b W x
      = (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          (M * ∏ i : Fin k, ∑ r ∈ sieveDivisors H i.val b W x,
            ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
            * (((Nat.totient r : ℝ) * ∑ d ∈ (sieveDivisors H i.val b W x).filter (fun d => r ∣ d),
                  (moebius d : ℝ) * Fs j i (Real.log d / Real.log R) / (d : ℝ))
               * ((Nat.totient r : ℝ) * ∑ e ∈ (sieveDivisors H i.val b W x).filter (fun e => r ∣ e),
                  (moebius e : ℝ) * Fs j' i (Real.log e / Real.log R) / (e : ℝ)))))
      + (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∑ P ∈ Fintype.piFinset (fun i : Fin k =>
              sieveDivisors H i.val b W x ×ˢ sieveDivisors H i.val b W x),
            (∏ i : Fin k,
              ((moebius (P i).1 : ℝ) * Fs j i (Real.log (P i).1 / Real.log R))
                * ((moebius (P i).2 : ℝ) * Fs j' i (Real.log (P i).2 / Real.log R)))
            * ((((Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊).filter (fun n => n % W = b % W)).filter
                  (fun m => ∀ i : Fin k,
                    (P i).1 ∣ (m + H.getD i.val 0) ∧ (P i).2 ∣ (m + H.getD i.val 0))).card
                - M / ∏ i : Fin k, (Nat.lcm (P i).1 (P i).2 : ℝ))) := by
  rw [sieveSum_selberg_nu_eq_heuristic_add_correction k J c Fs H R b W x hx M,
    heuristic_main_selberg_nu_yform k J c Fs H R b W x M]

/-- **Lattice weight, absolute value, factorizes over coordinates.** For a
product weight `∏ᵢ aᵢ(Pᵢ)` over the lattice `∏ᵢ Dset i`, the sum of absolute
values factors:
`∑_{P} |∏ᵢ aᵢ(Pᵢ)| = ∏ᵢ ∑_{de∈Dset i} |aᵢ(de)|`.
This is the structural reduction of the correction's total weight (the
`∑_{diag}|coeff|` that `diag_error_bound` reduces the diagonal `O(1)` error to)
from a `k`-dimensional lattice sum to a product of `k` *one-dimensional* divisor
sums — turning the analytic size bound `∑|coeff| = o(main)` into a per-coordinate
estimate. Pure algebra (`Finset.prod_univ_sum` + `Finset.abs_prod`). -/
theorem piFinset_sum_abs_prod_factor {k : ℕ} (Dset : Fin k → Finset (ℕ × ℕ))
    (a : Fin k → (ℕ × ℕ) → ℝ) :
    ∑ P ∈ Fintype.piFinset Dset, |∏ i : Fin k, a i (P i)|
      = ∏ i : Fin k, ∑ de ∈ Dset i, |a i de| := by
  classical
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.abs_prod]

/-- **Correction total-weight bound, factorized (sieve form).** Specializing
`piFinset_sum_abs_prod_factor` to the concrete correction weight
`coeffₚ = ∏ᵢ μ(Pᵢ.1)Fⱼᵢ·μ(Pᵢ.2)Fⱼ'ᵢ` of
`sieveSum_selberg_nu_eq_heuristic_add_correction`: the total absolute weight
`∑_P |coeffₚ|` equals
`∏ᵢ ∑_{(d,e)∈Dᵢ×Dᵢ} |μ(d)Fⱼᵢ(log d/log R)·μ(e)Fⱼ'ᵢ(log e/log R)|`,
a product of `k` one-dimensional weighted divisor sums. Each 1-D factor is
`≤ ‖Fⱼᵢ‖∞‖Fⱼ'ᵢ‖∞·(∑_{d∈Dᵢ}μ(d)²)·(∑_{e∈Dᵢ}μ(e)²)` — the divisor-sum size the
`o(main)` estimate must control (with the simplex support of `F` keeping the
product below `M·(log R)^k`). -/
theorem correction_weight_factor {k : ℕ} (D : Fin k → Finset ℕ)
    (Gs₁ Gs₂ : Fin k → ℝ → ℝ) (R : ℝ) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        |∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Gs₁ i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Gs₂ i (Real.log (P i).2 / Real.log R))|
      = ∏ i : Fin k, ∑ de ∈ (D i ×ˢ D i),
          |((moebius de.1 : ℝ) * Gs₁ i (Real.log de.1 / Real.log R))
            * ((moebius de.2 : ℝ) * Gs₂ i (Real.log de.2 / Real.log R))| :=
  piFinset_sum_abs_prod_factor (fun i => D i ×ˢ D i)
    (fun i de => ((moebius de.1 : ℝ) * Gs₁ i (Real.log de.1 / Real.log R))
      * ((moebius de.2 : ℝ) * Gs₂ i (Real.log de.2 / Real.log R)))

/-- **Absolute-value product sum factorizes.** `∑_{(d,e)∈A×B} |f(d)·g(e)| =
(∑_{d∈A}|f(d)|)·(∑_{e∈B}|g(e)|)`. The 1-D companion of `correction_weight_factor`:
each per-coordinate pair-sum splits into a product of two independent
single-variable absolute sums (`Finset.sum_product` + `abs_mul` +
`Finset.sum_mul_sum`). -/
theorem sum_prod_abs_mul_factor {α : Type*} (A B : Finset α) (f g : α → ℝ) :
    ∑ de ∈ A ×ˢ B, |f de.1 * g de.2| = (∑ d ∈ A, |f d|) * (∑ e ∈ B, |g e|) := by
  classical
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
  rw [abs_mul]

/-- **Correction total-weight bound, fully split into 1-D Möbius sums.** Refining
`correction_weight_factor` with `sum_prod_abs_mul_factor` per coordinate: the
total absolute correction weight equals
`∏ᵢ (∑_{d∈Dᵢ} |μ(d)Fⱼᵢ(log d/log R)|)·(∑_{e∈Dᵢ} |μ(e)Fⱼ'ᵢ(log e/log R)|)`,
a product of `2k` clean single-variable Möbius-weighted divisor sums. Each factor
`∑_{d∈Dᵢ} |μ(d)F(log d/log R)| ≤ ‖F‖∞ · #{d∈Dᵢ squarefree}` is the precise 1-D
size the `∑|coeff| = o(main)` estimate bounds (using `|μ| ≤ 1` and the simplex
support `d ≤ R`). This is the final structural reduction of analytic obligation
#2 to per-coordinate 1-D Möbius-sum size bounds. -/
theorem correction_weight_factor_split {k : ℕ} (D : Fin k → Finset ℕ)
    (Gs₁ Gs₂ : Fin k → ℝ → ℝ) (R : ℝ) :
    ∑ P ∈ Fintype.piFinset (fun i => D i ×ˢ D i),
        |∏ i : Fin k,
          ((moebius (P i).1 : ℝ) * Gs₁ i (Real.log (P i).1 / Real.log R))
            * ((moebius (P i).2 : ℝ) * Gs₂ i (Real.log (P i).2 / Real.log R))|
      = ∏ i : Fin k,
          (∑ d ∈ D i, |(moebius d : ℝ) * Gs₁ i (Real.log d / Real.log R)|)
          * (∑ e ∈ D i, |(moebius e : ℝ) * Gs₂ i (Real.log e / Real.log R)|) := by
  rw [correction_weight_factor D Gs₁ Gs₂ R]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact sum_prod_abs_mul_factor (D i) (D i)
    (fun d => (moebius d : ℝ) * Gs₁ i (Real.log d / Real.log R))
    (fun e => (moebius e : ℝ) * Gs₂ i (Real.log e / Real.log R))

/-- **Cauchy–Schwarz for the GPY/Selberg bilinear form.** The cross Selberg form
`B(g₁,g₂) = ∑_{d,e} μ(d)g₁(d)·μ(e)g₂(e)/[d,e]` satisfies
`B(g₁,g₂)² ≤ B(g₁,g₁)·B(g₂,g₂)`.
Proof: diagonalize all three forms (`gpy_diagonalize_moebius` /
`gpy_diagonalize_moebius_bilinear`) to the common `φ`-weighted inner product
`⟨y₁,y₂⟩ = ∑_r φ(r) y₁ᵣ y₂ᵣ`, then apply the discrete Cauchy–Schwarz inequality
(`Finset.sum_mul_sq_le_sq_mul_sq` with `f = √φ·y₁`, `g = √φ·y₂`).

**Why this matters analytically:** it controls every *cross* (`j ≠ j'`)
main-term block by the geometric mean of the *diagonal* (`j = j'`) blocks. So once
the diagonal asymptotic `B(Fⱼᵢ,Fⱼᵢ) ~ cⱼᵢ·(main)` is established (sub-step (c)),
the cross terms `∑_{j≠j'} cⱼcⱼ'·B(Fⱼᵢ,Fⱼ'ᵢ)` are *automatically* bounded — the
`IsLittleO` glue (sub-step (d)) needs only the diagonal limit. -/
theorem gpy_bilinear_cauchy_schwarz (T R : Finset ℕ) (g₁ g₂ : ℕ → ℝ)
    (hT : ∀ d ∈ T, 1 ≤ d) (hR : ∀ d ∈ T, ∀ r, r ∣ d → r ∈ R) :
    (∑ d ∈ T, ∑ e ∈ T,
        (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)) ^ 2
      ≤ (∑ d ∈ T, ∑ e ∈ T,
          (moebius d : ℝ) * g₁ d * ((moebius e : ℝ) * g₁ e) / (Nat.lcm d e : ℝ))
        * (∑ d ∈ T, ∑ e ∈ T,
          (moebius d : ℝ) * g₂ d * ((moebius e : ℝ) * g₂ e) / (Nat.lcm d e : ℝ)) := by
  classical
  rw [gpy_diagonalize_moebius_bilinear T R g₁ g₂ hT hR,
      gpy_diagonalize_moebius T R g₁ hT hR,
      gpy_diagonalize_moebius T R g₂ hT hR]
  set y₁ : ℕ → ℝ := fun r => ∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g₁ d / (d : ℝ)
    with hy₁
  set y₂ : ℕ → ℝ := fun r => ∑ d ∈ T.filter (fun d => r ∣ d), (moebius d : ℝ) * g₂ d / (d : ℝ)
    with hy₂
  have hφ : ∀ r : ℕ, (0:ℝ) ≤ (Nat.totient r : ℝ) := fun r => Nat.cast_nonneg _
  have key := Finset.sum_mul_sq_le_sq_mul_sq R
    (fun r => Real.sqrt (Nat.totient r) * y₁ r) (fun r => Real.sqrt (Nat.totient r) * y₂ r)
  have c0 : ∑ r ∈ R, Real.sqrt (Nat.totient r) * y₁ r * (Real.sqrt (Nat.totient r) * y₂ r)
      = ∑ r ∈ R, (Nat.totient r : ℝ) * (y₁ r * y₂ r) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [show Real.sqrt (Nat.totient r) * y₁ r * (Real.sqrt (Nat.totient r) * y₂ r)
        = (Real.sqrt (Nat.totient r) * Real.sqrt (Nat.totient r)) * (y₁ r * y₂ r) by ring,
      Real.mul_self_sqrt (hφ r)]
  have c1 : ∑ r ∈ R, (Real.sqrt (Nat.totient r) * y₁ r) ^ 2
      = ∑ r ∈ R, (Nat.totient r : ℝ) * y₁ r ^ 2 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_pow, Real.sq_sqrt (hφ r)]
  have c2 : ∑ r ∈ R, (Real.sqrt (Nat.totient r) * y₂ r) ^ 2
      = ∑ r ∈ R, (Nat.totient r : ℝ) * y₂ r ^ 2 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mul_pow, Real.sq_sqrt (hφ r)]
  rw [c0, c1, c2] at key
  exact key

/-- **Diagonal coefficient reassembles the joint `F²`.** On the diagonal tuple
(`Pᵢ.1 = Pᵢ.2 = dᵢ`, with `mᵢ = μ(dᵢ)`, `aᵢ = log dᵢ/log R`), summing the
`selberg_nu` correction coefficient `∑_{j,j'} cⱼcⱼ' ∏ᵢ (mᵢFⱼᵢ(aᵢ))(mᵢFⱼ'ᵢ(aᵢ))`
over the basis indices collapses to `(∏ᵢ mᵢ²)·F(a)²`, where `F = ∑ⱼ cⱼ∏ᵢFⱼᵢ` is
the *joint* test function (`hFdecomp`).

**Why this matters for analytic obligation #3** (`∑_{diag}|coeff| = o(main)`): the
naive per-`(j,j')`-block factorization (`correction_weight_factor_split`) is loose
because the simplex support lives on the joint `F`, not the individual `Fⱼᵢ`. This
identity shows the `j`-sum *reassembles* `F(a)²`, which **is** simplex-supported
(vanishes off `∑ᵢaᵢ ≤ 1`). So the diagonal size bound is really
`∑_{d on simplex, sf} (∏ᵢμ(dᵢ)²)·F(log d/log R)²`, a single simplex-restricted
sum — the correct (non-loose) substrate for the `o(main)` estimate. The square
form also re-exposes positivity (`F(a)² ≥ 0`), consistent with the PSD diagonal. -/
theorem selberg_nu_basis_diagonal_reassemble {k J : ℕ} (c : Fin J → ℝ)
    (Fs : Fin J → Fin k → ℝ → ℝ) (F : (Fin k → ℝ) → ℝ)
    (hFdecomp : ∀ t : Fin k → ℝ, F t = ∑ j : Fin J, c j * ∏ i : Fin k, Fs j i (t i))
    (m : Fin k → ℝ) (a : Fin k → ℝ) :
    ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ∏ i : Fin k, (m i * Fs j i (a i)) * (m i * Fs j' i (a i))
      = (∏ i : Fin k, (m i) ^ 2) * (F a) ^ 2 := by
  classical
  have hprod : ∀ (j j' : Fin J),
      ∏ i : Fin k, (m i * Fs j i (a i)) * (m i * Fs j' i (a i))
        = (∏ i : Fin k, (m i) ^ 2)
          * ((∏ i : Fin k, Fs j i (a i)) * (∏ i : Fin k, Fs j' i (a i))) := by
    intro j j'
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        (by ring : (m i * Fs j i (a i)) * (m i * Fs j' i (a i))
          = (m i) ^ 2 * (Fs j i (a i) * Fs j' i (a i)))),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  calc ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ∏ i : Fin k, (m i * Fs j i (a i)) * (m i * Fs j' i (a i))
      = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          ((∏ i : Fin k, (m i) ^ 2)
            * ((∏ i : Fin k, Fs j i (a i)) * (∏ i : Fin k, Fs j' i (a i)))) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
        rw [hprod j j']
    _ = (∏ i : Fin k, (m i) ^ 2) * ∑ j : Fin J, ∑ j' : Fin J,
          c j * c j' * ((∏ i : Fin k, Fs j i (a i)) * (∏ i : Fin k, Fs j' i (a i))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        ring
    _ = (∏ i : Fin k, (m i) ^ 2) * (F a) ^ 2 := by
        congr 1
        rw [hFdecomp a, pow_two, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
        ring

/-- **Simplex support ⟹ divisor product `≤ R`.** If the joint test function `F`
is supported on the Maynard simplex and `F(log d₁/log R, …, log dₖ/log R) ≠ 0`
(with `dᵢ ≥ 1`, `R > 1`), then `∏ᵢ dᵢ ≤ R`. Translating the simplex constraint
`∑ᵢ (log dᵢ/log R) ≤ 1` by `log R > 0` gives `∑ᵢ log dᵢ ≤ log R`, i.e.
`log(∏dᵢ) ≤ log R`, i.e. `∏dᵢ ≤ R`.

This is the bridge turning the simplex support hypothesis (an `s1` premise) into
the *hyperbolic* divisor constraint `∏dᵢ ≤ R` that bounds the diagonal weight
`∑_{d on simplex,sf}(∏μ²)F²` (`selberg_nu_basis_diagonal_reassemble`): the d-tuples
contributing are confined to `∏dᵢ ≤ R`, whose count is `≍ R(log R)^{k-1}` — the
`o(main)` gain over the naive `R^k` that makes analytic obligation #3 close. -/
theorem support_simplex_prod_le {k : ℕ} (F : (Fin k → ℝ) → ℝ)
    (hsupp : Function.support F ⊆ simplex k) (R : ℝ) (hR : 1 < R)
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hF : F (fun i => Real.log (d i) / Real.log R) ≠ 0) :
    (∏ i : Fin k, (d i : ℝ)) ≤ R := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hdpos : ∀ i, (0:ℝ) < (d i : ℝ) := fun i => by
    have h0 : 0 < d i := hd i
    exact_mod_cast h0
  have hprodpos : (0:ℝ) < ∏ i : Fin k, (d i : ℝ) := Finset.prod_pos (fun i _ => hdpos i)
  have hmem : (fun i => Real.log (d i) / Real.log R) ∈ simplex k :=
    hsupp (Function.mem_support.mpr hF)
  have hsum1 : ∑ i : Fin k, Real.log (d i) / Real.log R ≤ 1 := hmem.2
  have hsumlog : ∑ i : Fin k, Real.log (d i) ≤ Real.log R := by
    rw [← Finset.sum_div] at hsum1
    exact (div_le_one hlogR).mp hsum1
  have hlogprod : Real.log (∏ i : Fin k, (d i : ℝ)) = ∑ i : Fin k, Real.log (d i) :=
    Real.log_prod (fun i _ => ne_of_gt (hdpos i))
  rw [← hlogprod] at hsumlog
  have hexp := Real.exp_le_exp.mpr hsumlog
  rwa [Real.exp_log hprodpos, Real.exp_log (lt_trans one_pos hR)] at hexp

/-- **Simplex-supported continuous `F` is globally bounded.** A continuous `F`
with `Function.support F ⊆ simplex k` satisfies `∃ C ≥ 0, ∀ t, |F t| ≤ C`. The
simplex sits inside the compact box `[0,1]^k` (`0 ≤ tᵢ` and `∑tᵢ ≤ 1 ⟹ tᵢ ≤ 1`),
on which the continuous `|F|` attains a finite max; off the box `F = 0`.

This supplies the `‖F‖∞` bound the diagonal size estimate needs: combined with
`selberg_nu_basis_diagonal_reassemble` (diagonal weight `= ∑(∏μ²)F²`) and
`support_simplex_prod_le` (contributing tuples have `∏dᵢ ≤ R`), the diagonal
weight is `≤ C²·#{squarefree d-tuples with ∏dᵢ ≤ R}`, reducing analytic obligation
#2 to the `k`-dim divisor count `Dₖ(R) ≍ R(log R)^{k-1}` (via the repo's
`SingularSeries.dirichlet_hyperbola`). The `s1` premise `ContDiff ℝ ∞ F` gives
the continuity. -/
theorem support_simplex_bounded {k : ℕ} (F : (Fin k → ℝ) → ℝ)
    (hF : Continuous F) (hsupp : Function.support F ⊆ simplex k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Fin k → ℝ, |F t| ≤ C := by
  classical
  set K : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Icc (0:ℝ) 1) with hKdef
  have hKcompact : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsimplexK : simplex k ⊆ K := by
    intro t ht
    rw [hKdef, Set.mem_univ_pi]
    intro i
    exact Set.mem_Icc.mpr ⟨ht.1 i,
      le_trans (Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)) ht.2⟩
  obtain ⟨C, hC⟩ := hKcompact.bddAbove_image hF.abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases htK : t ∈ K
  · exact le_trans (hC (Set.mem_image_of_mem _ htK)) (le_max_left _ _)
  · have hts : t ∉ simplex k := fun h => htK (hsimplexK h)
    have hF0 : F t = 0 := by
      by_contra hne
      exact hts (hsupp (Function.mem_support.mpr hne))
    rw [hF0, abs_zero]
    exact le_max_right _ _

/-- **Diagonal weight `≤ C²·(hyperbola count)`** — the single-bound endpoint of
analytic obligation #2. The reassembled diagonal weight
`∑_d (∏ᵢμ(dᵢ)²)·F(log d/log R)²` (`selberg_nu_basis_diagonal_reassemble`) is
bounded by `C²·#{d ∈ lattice : ∏ᵢdᵢ ≤ R}`, where `C = ‖F‖∞`. Two facts combine:
(i) the summand vanishes off `∏ᵢdᵢ ≤ R` (`support_simplex_prod_le`), so the sum
restricts to the hyperbola; (ii) on it each summand is `≤ 1·C² = C²` (Möbius
squares `≤ 1`, `F² ≤ ‖F‖∞²`). So obligation #2 (`∑_{diag}|coeff| = o(main)`) is
reduced to the **single** estimate `#{d : ∏ᵢdᵢ ≤ R} = o(main/C²)` — the `k`-dim
Dirichlet divisor count `Dₖ(R) ≍ R(log R)^{k-1} = o(M·(log R)^k)` (since
`R = x^{θ/2} ≪ x ≈ MW`). The bound on `Dₖ(R)` (iterate of
`SingularSeries.dirichlet_hyperbola`) is the last missing analytic brick for #2. -/
theorem diagonal_weight_le_count {k : ℕ} (D : Fin k → Finset ℕ) (F : (Fin k → ℝ) → ℝ)
    (hsupp : Function.support F ⊆ simplex k) (R : ℝ) (hR : 1 < R)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d) (C : ℝ) (hC : ∀ t, |F t| ≤ C) :
    ∑ d ∈ Fintype.piFinset D,
        (∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2)
          * (F (fun i => Real.log (d i) / Real.log R)) ^ 2
      ≤ C ^ 2 * (((Fintype.piFinset D).filter
          (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)).card : ℝ) := by
  classical
  have hmu1 : ∀ n : ℕ, ((moebius n : ℝ)) ^ 2 ≤ 1 := fun n => by
    by_cases hsf : Squarefree n
    · have heq : ((moebius n : ℝ)) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [heq]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
  rw [← Finset.sum_filter_add_sum_filter_not (Fintype.piFinset D)
        (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)]
  have hnot : ∑ d ∈ (Fintype.piFinset D).filter
        (fun d => ¬ (∏ i : Fin k, (d i : ℝ)) ≤ R),
        (∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2)
          * (F (fun i => Real.log (d i) / Real.log R)) ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun d hd => ?_)
    rw [Finset.mem_filter] at hd
    have hd1 : ∀ i, 1 ≤ d i := fun i => hD i (d i) (Fintype.mem_piFinset.mp hd.1 i)
    have hF0 : F (fun i => Real.log (d i) / Real.log R) = 0 := by
      by_contra hne
      exact hd.2 (support_simplex_prod_le F hsupp R hR d hd1 hne)
    rw [hF0]; ring
  rw [hnot, add_zero]
  calc ∑ d ∈ (Fintype.piFinset D).filter (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R),
          (∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2)
            * (F (fun i => Real.log (d i) / Real.log R)) ^ 2
      ≤ ∑ _d ∈ (Fintype.piFinset D).filter (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R), C ^ 2 := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        have hmu : ∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2 ≤ 1 :=
          Finset.prod_le_one (fun i _ => sq_nonneg _) (fun i _ => hmu1 (d i))
        have hF2 : (F (fun i => Real.log (d i) / Real.log R)) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
        calc (∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2)
                * (F (fun i => Real.log (d i) / Real.log R)) ^ 2
            ≤ 1 * C ^ 2 := mul_le_mul hmu hF2 (sq_nonneg _) zero_le_one
          _ = C ^ 2 := one_mul _
    _ = C ^ 2 * (((Fintype.piFinset D).filter
          (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### Obligation #2 leaf (2): the `k`-dimensional Dirichlet hyperbola count.

`diagonal_weight_le_count` reduced the diagonal sieve weight to the lattice count
`#{d ∈ lattice : ∏ᵢ dᵢ ≤ R}`. The genuine analytic content of that count is the
`k`-fold divisor estimate `Dₖ(R) = #{d : ∏dᵢ ≤ R} ≍ R(log R)^{k-1}`. We prove the
clean UPPER bound `Dₖ(N) ≤ N·(1+log N)^{k-1}` (machine-checked, axiom-clean), then
bridge the real-`R`/general-lattice count down to it. Combined with
`diagonal_weight_le_count` this gives the diagonal weight an explicit closed-form
bound `≤ C²·⌊R⌋₊·(1+log⌊R⌋₊)^{k-1}`, which is `o(M·(log R)^k)` for `R = x^{θ/2} ≪ x ≈ MW`
— exactly analytic obligation #2 for `s1_holds_from_nonprime_asym`. -/

/-- **k-dimensional Dirichlet hyperbola count, upper bound.** The number of ordered
`k`-tuples of positive integers in `[1,N]` with product `≤ N` is
`≤ N·(1+log N)^{k-1}`. Proof: induction on `k`, partitioning the `(k+1)`-tuples by
their first coordinate `m ∈ [1,N]`; the fiber bijects (via `Fin.cons`/`Fin.tail`)
with the `k`-tuple count at bound `⌊N/m⌋`, and the harmonic sum
`∑_{m≤N} 1/m ≤ 1+log N` (`harmonic_le_one_add_log`) closes the step. -/
theorem hyperbola_count_le (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) :
    (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
        (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ)
      ≤ (N : ℝ) * (1 + Real.log N) ^ (k - 1) := by
  suffices aux : ∀ j : ℕ, ∀ N : ℕ, 1 ≤ N →
      (((Fintype.piFinset (fun _ : Fin (j+1) => Finset.Icc 1 N)).filter
          (fun d => ∏ i : Fin (j+1), d i ≤ N)).card : ℝ)
        ≤ (N : ℝ) * (1 + Real.log N) ^ j by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, (Nat.succ_pred_eq_of_pos hk).symm⟩
    simpa using aux j N hN
  clear hk hN N k
  intro j
  induction j with
  | zero =>
    intro N hN
    rw [pow_zero, mul_one]
    have hfilter : (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 N)).filter
        (fun d => ∏ i : Fin 1, d i ≤ N)
        = Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 N) := by
      apply Finset.filter_true_of_mem
      intro d hd
      rw [Fin.prod_univ_one]
      exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hd 0)).2
    rw [hfilter, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, Nat.card_Icc]
    have : N + 1 - 1 = N := by omega
    rw [this]
  | succ j IH =>
    intro N hN
    classical
    set S := (Fintype.piFinset (fun _ : Fin (j+2) => Finset.Icc 1 N)).filter
        (fun d => ∏ i : Fin (j+2), d i ≤ N) with hS
    have hprod : ∀ d : Fin (j+2) → ℕ,
        ∏ i : Fin (j+2), d i = d 0 * ∏ i : Fin (j+1), Fin.tail d i := by
      intro d; rw [Fin.prod_univ_succ]; rfl
    have hpart : S.card = ∑ m ∈ Finset.Icc 1 N, (S.filter (fun d => d 0 = m)).card := by
      apply Finset.card_eq_sum_card_fiberwise
        (f := fun d : Fin (j+2) → ℕ => d 0) (t := Finset.Icc 1 N)
      intro d hd
      rw [Finset.mem_coe, hS, Finset.mem_filter] at hd
      rw [Finset.mem_coe]
      exact Fintype.mem_piFinset.mp hd.1 0
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        ((S.filter (fun d => d 0 = m)).card : ℝ) ≤ (N : ℝ) / m * (1 + Real.log N) ^ j := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      obtain ⟨hm1, hmN⟩ := hm
      have hm0 : 0 < m := by omega
      set M := N / m with hMdef
      have hMpos : 1 ≤ M := by
        rw [hMdef, Nat.le_div_iff_mul_le hm0]; simpa using hmN
      have hMle : M ≤ N := Nat.div_le_self N m
      have hcard_eq : (S.filter (fun d => d 0 = m)).card
          = ((Fintype.piFinset (fun _ : Fin (j+1) => Finset.Icc 1 M)).filter
              (fun d' => ∏ i : Fin (j+1), d' i ≤ M)).card := by
        refine Finset.card_bij' (fun d _ => Fin.tail d) (fun d' _ => Fin.cons m d') ?_ ?_ ?_ ?_
        · intro d hd
          simp only [hS, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hd
          obtain ⟨⟨hmem, hprodN⟩, hd0⟩ := hd
          have hprodM : ∏ i : Fin (j+1), Fin.tail d i ≤ M := by
            have hkey : m * ∏ i : Fin (j+1), Fin.tail d i ≤ N := by
              rw [← hd0, ← hprod d]; exact hprodN
            rw [hMdef, Nat.le_div_iff_mul_le hm0, mul_comm]; exact hkey
          rw [Finset.mem_filter, Fintype.mem_piFinset]
          refine ⟨fun i => ?_, hprodM⟩
          rw [Finset.mem_Icc]
          refine ⟨(hmem i.succ).1, ?_⟩
          calc Fin.tail d i ≤ ∏ i' : Fin (j+1), Fin.tail d i' :=
                Finset.single_le_prod' (fun i' _ => (hmem i'.succ).1) (Finset.mem_univ i)
            _ ≤ M := hprodM
        · intro d' hd'
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hd'
          obtain ⟨hmem', hprodM'⟩ := hd'
          simp only [hS, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
          refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
          · refine Fin.cases ?_ ?_ i
            · rw [Fin.cons_zero]; exact ⟨hm1, hmN⟩
            · intro i'; rw [Fin.cons_succ]; exact ⟨(hmem' i').1, le_trans (hmem' i').2 hMle⟩
          · rw [hprod (Fin.cons m d'), Fin.cons_zero, Fin.tail_cons]
            calc m * ∏ i, d' i ≤ m * M := Nat.mul_le_mul (le_refl m) hprodM'
              _ ≤ N := by rw [hMdef, mul_comm]; exact Nat.div_mul_le_self N m
          · rw [Fin.cons_zero]
        · intro d hd
          have hd2 : d 0 = m := by
            simp only [hS, Finset.mem_filter] at hd; exact hd.2
          change Fin.cons m (Fin.tail d) = d
          funext i
          refine Fin.cases ?_ ?_ i
          · rw [Fin.cons_zero]; exact hd2.symm
          · intro i'; rw [Fin.cons_succ]; rfl
        · intro d' hd'
          change Fin.tail (Fin.cons m d' : Fin (j+2) → ℕ) = d'
          simp [Fin.tail_cons]
      rw [hcard_eq]
      have hIH := IH M hMpos
      have hM0 : 0 < M := hMpos
      have hlogM : (0:ℝ) ≤ 1 + Real.log M := by
        have h := Real.log_nonneg (show (1:ℝ) ≤ (M:ℝ) by exact_mod_cast hMpos); linarith
      have hlogMN : 1 + Real.log M ≤ 1 + Real.log N := by
        have : Real.log M ≤ Real.log N :=
          Real.log_le_log (show (0:ℝ) < (M:ℝ) by exact_mod_cast hM0)
            (show (M:ℝ) ≤ (N:ℝ) by exact_mod_cast hMle)
        linarith
      calc (((Fintype.piFinset (fun _ : Fin (j+1) => Finset.Icc 1 M)).filter
              (fun d' => ∏ i : Fin (j+1), d' i ≤ M)).card : ℝ)
          ≤ (M : ℝ) * (1 + Real.log M) ^ j := hIH
        _ ≤ (N : ℝ) / m * (1 + Real.log N) ^ j := by
            apply mul_le_mul
            · rw [hMdef]; exact_mod_cast Nat.cast_div_le
            · exact pow_le_pow_left₀ hlogM hlogMN j
            · exact pow_nonneg hlogM j
            · positivity
    have hcast : (S.card : ℝ)
        = ∑ m ∈ Finset.Icc 1 N, ((S.filter (fun d => d 0 = m)).card : ℝ) := by
      rw [hpart]; push_cast; rfl
    rw [hcast]
    have hharm : (∑ m ∈ Finset.Icc 1 N, ((m:ℝ))⁻¹) ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      rw [harmonic_eq_sum_Icc] at h
      push_cast at h
      exact h
    have hlogN_nonneg : (0:ℝ) ≤ 1 + Real.log N := by
      have h := Real.log_nonneg (show (1:ℝ) ≤ (N:ℝ) by exact_mod_cast hN); linarith
    have hpow_nonneg : (0:ℝ) ≤ (1 + Real.log N) ^ j := pow_nonneg hlogN_nonneg j
    calc ∑ m ∈ Finset.Icc 1 N, ((S.filter (fun d => d 0 = m)).card : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 N, (N : ℝ) / m * (1 + Real.log N) ^ j :=
          Finset.sum_le_sum hterm
      _ = (1 + Real.log N) ^ j * (N * ∑ m ∈ Finset.Icc 1 N, ((m:ℝ))⁻¹) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [div_eq_mul_inv]; ring
      _ ≤ (1 + Real.log N) ^ j * (N * (1 + Real.log N)) := by
          apply mul_le_mul_of_nonneg_left _ hpow_nonneg
          apply mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = (N : ℝ) * (1 + Real.log N) ^ (j + 1) := by ring

/-- **Bridge: the general (real-`R`, arbitrary lattice) diagonal count is bounded by
the hyperbola count.** Any `d` in the filtered lattice has positive entries with
`∏(dᵢ:ℝ) ≤ R`, hence each `dᵢ ≤ ∏dⱼ ≤ ⌊R⌋₊` and the nat product is `≤ ⌊R⌋₊`, so the
filtered set injects into the `[1,⌊R⌋₊]`-box count. Then `hyperbola_count_le` applies. -/
theorem lattice_count_le_hyperbola {k : ℕ} (hk : 1 ≤ k) (D : Fin k → Finset ℕ)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d) (R : ℝ) (hR : 1 < R) :
    (((Fintype.piFinset D).filter
        (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)).card : ℝ)
      ≤ (⌊R⌋₊ : ℝ) * (1 + Real.log ⌊R⌋₊) ^ (k - 1) := by
  classical
  set N := ⌊R⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hR.le)
  have hsub : (Fintype.piFinset D).filter (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)
      ⊆ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
          (fun d => ∏ i : Fin k, d i ≤ N) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdmem, hdR⟩ := hd
    have hd1 : ∀ i, 1 ≤ d i := fun i => hD i (d i) (Fintype.mem_piFinset.mp hdmem i)
    have hprodN : ∏ i : Fin k, d i ≤ N := by
      rw [hNdef, Nat.le_floor_iff (le_trans zero_le_one hR.le)]
      push_cast
      exact hdR
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, hprodN⟩
    rw [Finset.mem_Icc]
    refine ⟨hd1 i, ?_⟩
    calc d i ≤ ∏ i' : Fin k, d i' :=
          Finset.single_le_prod' (fun i' _ => hd1 i') (Finset.mem_univ i)
      _ ≤ N := hprodN
  calc (((Fintype.piFinset D).filter
          (fun d => (∏ i : Fin k, (d i : ℝ)) ≤ R)).card : ℝ)
      ≤ (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N)).filter
          (fun d => ∏ i : Fin k, d i ≤ N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (N : ℝ) * (1 + Real.log N) ^ (k - 1) := hyperbola_count_le k hk N hN

/-- **Obligation #2 diagonal capstone (closed form).** The diagonal sieve weight is
bounded by `C²·⌊R⌋₊·(1+log⌊R⌋₊)^{k-1}`. Combines `diagonal_weight_le_count` (weight ≤
`C²·count`) with the hyperbola bound. Since `R = x^{θ/2} ≪ x ≈ MW`, the RHS is
`o(M·(log R)^k)` — discharging the diagonal half of analytic obligation #2 to an
explicit `≍ R(log R)^{k-1}` estimate. -/
theorem diagonal_weight_le_hyperbola {k : ℕ} (hk : 1 ≤ k) (D : Fin k → Finset ℕ)
    (F : (Fin k → ℝ) → ℝ) (hsupp : Function.support F ⊆ simplex k) (R : ℝ) (hR : 1 < R)
    (hD : ∀ i, ∀ d ∈ D i, 1 ≤ d) (C : ℝ) (hC : ∀ t, |F t| ≤ C) :
    ∑ d ∈ Fintype.piFinset D,
        (∏ i : Fin k, ((moebius (d i) : ℝ)) ^ 2)
          * (F (fun i => Real.log (d i) / Real.log R)) ^ 2
      ≤ C ^ 2 * ((⌊R⌋₊ : ℝ) * (1 + Real.log ⌊R⌋₊) ^ (k - 1)) := by
  refine le_trans (diagonal_weight_le_count D F hsupp R hR hD C hC) ?_
  exact mul_le_mul_of_nonneg_left (lattice_count_le_hyperbola hk D hD R hR) (sq_nonneg C)

/-! ### Möbius inversion over multiples (foundation for the contour-free Path-Y sieve `selberg_nu_yr`)

The exact (non-asymptotic) duality between a finite divisor-closed family of GPY `y_r` values and
the sieve coefficients `λ_d` realising them. With `λ_d = d·(∑_{s∈R, d∣s} μ(s/d)·Y s)`, the GPY
variable `∑_{r∣d} λ_d/d` recovers exactly `Y r` — so feeding a SMOOTH `Y r = F(log r/log R)`
produces a sieve whose diagonalised main term is `∑_r (μ²/φ) F²` directly
(`WeightedMertens.weighted_mertens_coprime_sq`), with NO PNT-strength `z_r` evaluation. -/

/-- `∑_{e ∣ m} μ(e) = [m = 1]` (the Möbius `μ ∗ ζ = δ` identity, ℝ-valued). -/
theorem moebius_div_collapse (m : ℕ) :
    (∑ e ∈ m.divisors, (moebius e : ℝ)) = if m = 1 then 1 else 0 := by
  have h : (∑ e ∈ m.divisors, (moebius e : ℤ)) = if m = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  calc (∑ e ∈ m.divisors, (moebius e : ℝ))
      = ((∑ e ∈ m.divisors, (moebius e : ℤ) : ℤ) : ℝ) := by push_cast; rfl
    _ = if m = 1 then 1 else 0 := by rw [h]; split <;> simp

/-- Inner Möbius collapse: for `r ∣ s`, `s ≥ 1`, `∑_{d ∣ s, r ∣ d} μ(s/d) = [s = r]`. Proof: the
complementary-divisor bijection `d ↦ d/r` maps the sum to `∑_{c ∣ (s/r)} μ((s/r)/c) = ∑_{c ∣ (s/r)} μ c
= [s/r = 1]` (`Nat.sum_div_divisors` + `moebius_div_collapse`). -/
theorem inner_moebius_collapse (r s : ℕ) (hs : 1 ≤ s) (hrs : r ∣ s) :
    (∑ d ∈ s.divisors.filter (fun d => r ∣ d), (moebius (s / d) : ℝ))
      = if s = r then 1 else 0 := by
  have hr1 : 1 ≤ r := Nat.pos_of_dvd_of_pos hrs hs
  have hsr0 : s / r ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd hs hrs) hr1; omega
  have hbij : (∑ d ∈ s.divisors.filter (fun d => r ∣ d), (moebius (s / d) : ℝ))
      = ∑ c ∈ (s / r).divisors, (moebius ((s / r) / c) : ℝ) := by
    refine Finset.sum_bij' (fun d _ => d / r) (fun c _ => c * r) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hds, _⟩, j, hj⟩ := hd
      obtain ⟨k, hk⟩ := hds
      show d / r ∈ (s / r).divisors
      rw [Nat.mem_divisors, hj, Nat.mul_div_cancel_left j hr1]
      exact ⟨⟨k, by rw [hk, hj, mul_assoc, Nat.mul_div_cancel_left _ hr1]⟩, hsr0⟩
    · intro c hc
      simp only [Nat.mem_divisors] at hc
      obtain ⟨⟨k, hk⟩, _⟩ := hc
      show c * r ∈ s.divisors.filter (fun d => r ∣ d)
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨k, ?_⟩, by omega⟩, ⟨c, by ring⟩⟩
      have hsrr : s = r * (s / r) := (Nat.mul_div_cancel' hrs).symm
      rw [hsrr, hk]; ring
    · intro d hd
      simp only [Finset.mem_filter] at hd
      exact Nat.div_mul_cancel hd.2
    · intro c hc
      exact Nat.mul_div_cancel _ hr1
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨_, _⟩, hrd⟩ := hd
      show (moebius (s / d) : ℝ) = (moebius ((s / r) / (d / r)) : ℝ)
      rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hrd]
  rw [hbij, Nat.sum_div_divisors (s / r) (fun e => (moebius e : ℝ)), moebius_div_collapse]
  by_cases h : s = r
  · simp [h, Nat.div_self hr1]
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by rw [← Nat.div_mul_cancel hrs, hc, one_mul])

/-- **Möbius inversion over multiples in a divisor-closed finite set.**
For `R` finite, divisor-closed (`d ∣ s ∈ R → d ∈ R`), all elements `≥ 1`, and any target
`Y : ℕ → ℝ`, the weight `a(d) := ∑_{s∈R, d∣s} μ(s/d)·Y(s)` inverts the multiples-sum:
`∑_{d∈R, r∣d} a(d) = Y(r)` for every `r ∈ R`. This is the exact (non-asymptotic) duality that
realises a SMOOTH GPY `y_r = Y(r)` from an explicit sieve coefficient `λ_d = d·a(d)` — the
foundation of the contour-free Path-Y sieve construction `selberg_nu_yr`. -/
theorem moebius_inversion_multiples (R : Finset ℕ)
    (hR0 : ∀ s ∈ R, 1 ≤ s)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R)
    (Y : ℕ → ℝ) (r : ℕ) (hr : r ∈ R) :
    (∑ d ∈ R.filter (fun d => r ∣ d),
        ∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s) = Y r := by
  classical
  -- swap: ∑_{d∈R, r|d} ∑_{s∈R, d|s} = ∑_{s∈R} ∑_{d∈R, r|d ∧ d|s}
  have hswap : (∑ d ∈ R.filter (fun d => r ∣ d),
        ∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s)
      = ∑ s ∈ R, ∑ d ∈ R.filter (fun d => r ∣ d ∧ d ∣ s), (moebius (s / d) : ℝ) * Y s := by
    refine Finset.sum_comm' ?_
    intro d s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, hrd⟩, hs, hds⟩; exact ⟨⟨hd, hrd, hds⟩, hs⟩
    · rintro ⟨⟨hd, hrd, hds⟩, hs⟩; exact ⟨⟨hd, hrd⟩, hs, hds⟩
  rw [hswap]
  -- inner sum over s
  rw [Finset.sum_eq_single r]
  · -- s = r term
    have hset : R.filter (fun d => r ∣ d ∧ d ∣ r) = r.divisors.filter (fun d => r ∣ d) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_, hrd, hdr⟩; exact ⟨⟨hdr, by have := hR0 r hr; omega⟩, hrd⟩
      · rintro ⟨⟨hdr, _⟩, hrd⟩; exact ⟨hRdc r hr d hdr, hrd, hdr⟩
    rw [hset, ← Finset.sum_mul, inner_moebius_collapse r r (hR0 r hr) dvd_rfl, if_pos rfl, one_mul]
  · -- s ≠ r terms vanish
    intro s hs hsr
    rw [← Finset.sum_mul]
    by_cases hrs : r ∣ s
    · have hset : R.filter (fun d => r ∣ d ∧ d ∣ s) = s.divisors.filter (fun d => r ∣ d) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hrd, hds⟩; exact ⟨⟨hds, by have := hR0 s hs; omega⟩, hrd⟩
        · rintro ⟨⟨hds, _⟩, hrd⟩; exact ⟨hRdc s hs d hds, hrd, hds⟩
      rw [hset, inner_moebius_collapse r s (hR0 s hs) hrs, if_neg hsr, zero_mul]
    · -- r ∤ s: filter empty
      have : R.filter (fun d => r ∣ d ∧ d ∣ s) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d _ ⟨hrd, hds⟩
        exact hrs (dvd_trans hrd hds)
      rw [this, Finset.sum_empty, zero_mul]
  · intro hrR; exact absurd hr hrR

/-- **Diagonalisation meets inversion — the contour-free y-space main term.** For `R` finite,
divisor-closed, all `≥ 1`, and the inversion-defined sieve coefficient
`λ_d := d·(∑_{s∈R, d∣s} μ(s/d)·Y s)`, the diagonalised Selberg form collapses to the SMOOTH sum
`∑_{d,e∈R} λ_d λ_e / [d,e] = ∑_{r∈R} φ(r)·Y(r)²`. Composes `gpy_diagonalize` (general weight) with
`moebius_inversion_multiples` (the inner GPY variable `∑_{r∣d} λ_d/d` evaluates to `Y r` exactly).
This is the crux that makes Path-Y `s1` contour-free: with `R = {r ≤ N squarefree, (r,W)=1}` and
`Y r = F(log r/log R)/φ(r)`, `φ(r)Y(r)² = (μ²/φ)(r)·F²`, so the main term is exactly the
`WeightedMertens.weighted_mertens_coprime_sq` sum `→ (φ(W)/W)·∫F²` — NO PNT-strength `z_r`. -/
theorem gpy_diagonalize_yform_smooth (R : Finset ℕ)
    (hR0 : ∀ s ∈ R, 1 ≤ s)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R)
    (Y : ℕ → ℝ) :
    (∑ d ∈ R, ∑ e ∈ R,
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s))
          * ((e : ℝ) * (∑ s ∈ R.filter (fun s => e ∣ s), (moebius (s / e) : ℝ) * Y s))
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ R, (Nat.totient r : ℝ) * Y r ^ 2 := by
  rw [gpy_diagonalize R R
    (fun d => (d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s))
    hR0 (fun d hd r hr => hRdc d hd r hr)]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  congr 1
  have hinner : (∑ d ∈ R.filter (fun d => r ∣ d),
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s)) / (d : ℝ))
      = Y r := by
    rw [← moebius_inversion_multiples R hR0 hRdc Y r hr]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd1 : 1 ≤ d := hR0 d ((Finset.mem_filter.mp hd).1)
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hinner]

/-- **The y-space sieve diagonal main term IS `∑(μ²/φ)F²`** (the exact `weighted_mertens_coprime_sq`
shape). Specialising `gpy_diagonalize_yform_smooth` to `Y s = F(log s/L)/φ(s)` on a squarefree,
divisor-closed `R`: since `μ(r)²=1` there, `φ(r)Y(r)² = (μ²/φ)(r)·F(log r/L)²`. So the explicit
y-space coefficient `λ_d = d·∑_{s∈R,d|s}μ(s/d)·F(log s/L)/φ(s)` gives
`∑_{d,e∈R} λ_d λ_e/[d,e] = ∑_{r∈R}(μ²/φ)(r)·F(log r/L)²` — which (over `R = {r≤N sf, (r,W)=1}`,
`L = log N`) is exactly `WeightedMertens.gMuSqTotientCoprime`-weighted, hence `→ (φ(W)/W)·∫F²` by
`weighted_mertens_coprime_sq`. The full contour-free Path-Y `s1` main term, modulo the lattice-count
reduction `sieveSum ≈ (count)·∑λλ/[d,e]` (the `selberg_nu_yr` wiring + correction, next). -/
theorem gpy_diagonalize_yform_muphi (R : Finset ℕ)
    (hR0 : ∀ s ∈ R, 1 ≤ s)
    (hRsf : ∀ s ∈ R, Squarefree s)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R)
    (F : ℝ → ℝ) (L : ℝ) :
    (∑ d ∈ R, ∑ e ∈ R,
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s),
            (moebius (s / d) : ℝ) * (F (Real.log s / L) / (Nat.totient s : ℝ))))
          * ((e : ℝ) * (∑ s ∈ R.filter (fun s => e ∣ s),
            (moebius (s / e) : ℝ) * (F (Real.log s / L) / (Nat.totient s : ℝ))))
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ R, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * F (Real.log r / L) ^ 2 := by
  rw [gpy_diagonalize_yform_smooth R hR0 hRdc
    (fun s => F (Real.log s / L) / (Nat.totient s : ℝ))]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hφ : (0 : ℝ) < (Nat.totient r : ℝ) := by
    have : 0 < Nat.totient r := Nat.totient_pos.mpr (hR0 r hr)
    exact_mod_cast this
  have hμ : ((moebius r : ℝ)) ^ 2 = 1 := by
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hRsf r hr)
    exact_mod_cast this
  rw [hμ]
  field_simp

/-- **The concrete y-space sieve index set satisfies the diagonalisation hypotheses.** The actual
support `R_N = {r ≤ N : Squarefree r ∧ (r,W)=1}` is `≥ 1`, squarefree, and **divisor-closed** (a
divisor of a squarefree `W`-coprime `r ≤ N` is again squarefree, `W`-coprime, and `≤ N`). Hence
`gpy_diagonalize_yform_muphi`/`gpy_diagonalize_yform_smooth`/`moebius_inversion_multiples` all apply
to `R_N` — the y-space construction is non-vacuous on the real sieve index set. -/
theorem sieveR_yspace_hyps (N W : ℕ) :
    (∀ s ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W), 1 ≤ s)
    ∧ (∀ s ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W), Squarefree s)
    ∧ (∀ s ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W),
        ∀ d, d ∣ s → d ∈ (Finset.Icc 1 N).filter (fun r => Squarefree r ∧ Nat.Coprime r W)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  · intro s hs
    exact (Finset.mem_filter.mp hs).2.1
  · intro s hs d hds
    rw [Finset.mem_filter, Finset.mem_Icc] at hs ⊢
    obtain ⟨⟨hs1, hsN⟩, hsf, hcop⟩ := hs
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hds (by omega)
    have hdN : d ≤ N := le_trans (Nat.le_of_dvd (by omega) hds) hsN
    exact ⟨⟨hd1, hdN⟩, hsf.squarefree_of_dvd hds, Nat.Coprime.coprime_dvd_left hds hcop⟩

/-- **Bilinear (cross-term `j≠j'`) y-space diagonalisation, smooth form.** The bilinear analog of
`gpy_diagonalize_yform_smooth` (via `gpy_diagonalize_bilinear` + `moebius_inversion_multiples` on each
factor): for inversion coefficients `λ^{(a)}_d = d·∑_{s∈R,d|s}μ(s/d)Y_a(s)`,
`∑_{d,e∈R} λ^{(1)}_d λ^{(2)}_e/[d,e] = ∑_{r∈R} φ(r)·Y₁(r)·Y₂(r)`. -/
theorem gpy_diagonalize_yform_smooth_bilinear (R : Finset ℕ)
    (hR0 : ∀ s ∈ R, 1 ≤ s) (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R) (Y₁ Y₂ : ℕ → ℝ) :
    (∑ d ∈ R, ∑ e ∈ R,
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y₁ s))
          * ((e : ℝ) * (∑ s ∈ R.filter (fun s => e ∣ s), (moebius (s / e) : ℝ) * Y₂ s))
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ R, (Nat.totient r : ℝ) * (Y₁ r * Y₂ r) := by
  rw [gpy_diagonalize_bilinear R R
    (fun d => (d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y₁ s))
    (fun e => (e : ℝ) * (∑ s ∈ R.filter (fun s => e ∣ s), (moebius (s / e) : ℝ) * Y₂ s))
    hR0 (fun d hd r hr => hRdc d hd r hr)]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  congr 1
  have inv : ∀ (Y : ℕ → ℝ), (∑ d ∈ R.filter (fun d => r ∣ d),
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s), (moebius (s / d) : ℝ) * Y s)) / (d : ℝ))
      = Y r := by
    intro Y
    rw [← moebius_inversion_multiples R hR0 hRdc Y r hr]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd1 : 1 ≤ d := hR0 d ((Finset.mem_filter.mp hd).1)
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
  rw [inv Y₁, inv Y₂]

/-- **Bilinear y-space diagonalisation, `μ²/φ` form** (the cross-term `s1` shape). With
`Y_a(s) = F_a(log s/L)/φ(s)` on squarefree divisor-closed `R`:
`∑_{d,e∈R} λ^{(1)}_d λ^{(2)}_e/[d,e] = ∑_{r∈R}(μ²/φ)(r)·F₁(log r/L)·F₂(log r/L)`. -/
theorem gpy_diagonalize_yform_muphi_bilinear (R : Finset ℕ)
    (hR0 : ∀ s ∈ R, 1 ≤ s) (hRsf : ∀ s ∈ R, Squarefree s)
    (hRdc : ∀ s ∈ R, ∀ d, d ∣ s → d ∈ R) (F₁ F₂ : ℝ → ℝ) (L : ℝ) :
    (∑ d ∈ R, ∑ e ∈ R,
        ((d : ℝ) * (∑ s ∈ R.filter (fun s => d ∣ s),
            (moebius (s / d) : ℝ) * (F₁ (Real.log s / L) / (Nat.totient s : ℝ))))
          * ((e : ℝ) * (∑ s ∈ R.filter (fun s => e ∣ s),
            (moebius (s / e) : ℝ) * (F₂ (Real.log s / L) / (Nat.totient s : ℝ))))
          / (Nat.lcm d e : ℝ))
      = ∑ r ∈ R, ((moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ))
          * (F₁ (Real.log r / L) * F₂ (Real.log r / L)) := by
  rw [gpy_diagonalize_yform_smooth_bilinear R hR0 hRdc
    (fun s => F₁ (Real.log s / L) / (Nat.totient s : ℝ))
    (fun s => F₂ (Real.log s / L) / (Nat.totient s : ℝ))]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hφ : (0 : ℝ) < (Nat.totient r : ℝ) := by
    have : 0 < Nat.totient r := Nat.totient_pos.mpr (hR0 r hr)
    exact_mod_cast this
  have hμ : ((moebius r : ℝ)) ^ 2 = 1 := by
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hRsf r hr); exact_mod_cast this
  rw [hμ]; field_simp

end BoundedGaps.Sieve
