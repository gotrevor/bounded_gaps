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

end BoundedGaps.Sieve
