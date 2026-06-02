/-
# Orbit-free / computable ε-Rayleigh Gram assembly (`Mk_eps`)

The ε-analog of the cross/bilinear/computable layer in `SymmetricReductionOrbitFree`. Reuses the
disjoint-union double-sum engine `OrbitFree.symWeight_double_sum` and the computable non-ε
denominator entry `OrbitFree.gramDenEntry`.

**Denominator side: DONE.** The ε-denominator's per-pair weight `(1+ε)^{k+|p+q|}` is constant
over each orbit pair (degree is permutation-invariant), so the ε-denominator Gram entry is
`(1+ε)^{k+|a|+|b|}` times `gramDenEntry`, and the ε-Maynard denominator of a symmetric weight is
the orbit-basis quadratic form with those entries.

**Numerator side: TODO** — needs the orbit-free re-index of the `affineSlackRat` triple sum (the
ε-analog of `OrbitFree.numerator_orbitFree`). Harder than the non-ε case: `affineSlackRat` is an
`∑ₘ` of binomial-weighted `dirichletIntegralWithSlack` with the slack exponent `β-m` *varying*
with `m`, so `numerator_summand_factor` applies per-`m` with an `m`-dependent local factor.
-/
import BoundedGaps.SymmetricReductionOrbitFree
import BoundedGaps.EpsBridge

namespace BoundedGaps

open Finset
open scoped Nat
open SymmetricReduction SievePolynomial OrbitFree EpsBridge

namespace OrbitFree

/-- **Constant `(1+ε)`-factor of the ε-denominator orbit pair.** Since every orbit pair `(p,q)`
has `|p+q| = |a|+|b|` (degree is permutation-invariant), the weight `(1+ε)^{k+|p+q|}` is constant
over the pair and factors out, leaving the non-ε orbit-pair denominator sum. -/
lemma orbitPair_denominator_eps_const {k : ℕ} (a b : MultiIndex k) (ε : ℚ) :
    ∑ p ∈ monoOrbit a, ∑ q ∈ monoOrbit b,
        ((1 + ε) ^ (k + ∑ i, (p + q) i) * monomialIntegral (p + q))
      = (1 + ε) ^ (k + a.degree + b.degree) *
          ∑ p ∈ monoOrbit a, ∑ q ∈ monoOrbit b, monomialIntegral (p + q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hdeg : (∑ i, (p + q) i) = a.degree + b.degree := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [monoOrbit_mem_degree a hp, monoOrbit_mem_degree b hq]
  rw [hdeg, ← Nat.add_assoc]

/-- **Computable ε-denominator Gram entry** — `(1+ε)^{k+|a|+|b|}` times the non-ε computable
denominator entry `gramDenEntry`. -/
def gramDenEntryEps {k : ℕ} (a b : MultiIndex k) (ε : ℚ) : ℚ :=
  (1 + ε) ^ (k + a.degree + b.degree) * gramDenEntry a b

/-- **Bilinear (Gram) expansion of the ε-denominator.** The ε-Maynard denominator of a symmetric
weight is the orbit-basis quadratic form `∑_{a,b∈R} c_a c_b · gramDenEntryEps a b ε` with the
computable ε-denominator Gram entries. The ε-analog of
`polynomialMaynardDenominator_symWeight`. -/
theorem polynomialMaynardDenominator_eps_symWeight {k : ℕ} (R : Finset (MultiIndex k))
    (c : MultiIndex k → ℚ) (ε : ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMaynardDenominator_eps (symWeight R c) ε
      = ∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryEps a b ε := by
  classical
  unfold polynomialMaynardDenominator_eps
  rw [symWeight_double_sum R c hR]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  dsimp only
  rw [gramDenEntryEps, ← gramDenEntry_eq, crossDenominator_orbitSum,
      ← orbitPair_denominator_eps_const, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]

/-! ## ε-numerator Gram bilinear structure

The ε-numerator is bilinear in the terms (like the non-ε one), so the Gram expansion over the
orbit basis follows from `symWeight_double_sum` regardless of whether the entry is yet orbit-free.
The entry's `native_decide`-ready closed form (the `affineSlackRat` orbit-free re-index) is the
remaining TODO; this layer is the structural scaffold for it. -/

/-- The **cross ε-numerator** of two weights (`k = n+1`): the marked-coordinate triple sum of
`affineSlackRat`. `= polynomialMaynardNumerator_eps P ε` on the diagonal. -/
noncomputable def crossNumerator_eps {n : ℕ} (P Q : PolynomialSieveWeight (n + 1)) (ε : ℚ) : ℚ :=
  ∑ i : Fin (n + 1), ∑ p ∈ P.terms, ∑ q ∈ Q.terms,
    (p.2 * q.2 / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ))) *
      affineSlackRat (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2) ε

/-- **Cross ε-numerator entry = orbit-pair marked `affineSlackRat` sum.** -/
lemma crossNumerator_eps_orbitSum {n : ℕ} (α β : MultiIndex (n + 1)) (ε : ℚ) :
    crossNumerator_eps (orbitSum α) (orbitSum β) ε
      = ∑ i : Fin (n + 1), ∑ p ∈ monoOrbit α, ∑ q ∈ monoOrbit β,
          (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
            affineSlackRat (Fin.removeNth i (p + q)) (p i + q i + 2) ε := by
  unfold crossNumerator_eps
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [orbitSum_terms, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  refine Finset.sum_congr rfl (fun pm _ => ?_)
  rw [orbitSum_terms, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  refine Finset.sum_congr rfl (fun qm _ => ?_)
  simp

/-- **Bilinear (Gram) expansion of the ε-numerator.** The ε-Maynard numerator of a symmetric
weight is the orbit-basis quadratic form `∑_{a,b∈R} c_a c_b · crossNumerator_eps (orbitSum a)
(orbitSum b) ε`. The ε-analog of `polynomialMaynardNumerator_symWeight`. -/
theorem polynomialMaynardNumerator_eps_symWeight {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ) (ε : ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMaynardNumerator_eps (symWeight R c) ε
      = ∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator_eps (orbitSum a) (orbitSum b) ε := by
  classical
  simp only [polynomialMaynardNumerator_eps]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
        symWeight_double_sum R c hR
          (fun p q => (p.2 * q.2 / (((p.1 i + 1 : ℕ) : ℚ) * ((q.1 i + 1 : ℕ) : ℚ))) *
            affineSlackRat (Fin.removeNth i (p.1 + q.1)) (p.1 i + q.1 i + 2) ε))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [crossNumerator_eps_orbitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  dsimp only
  ring

/-- **Symmetric ε-Maynard ratio as a Gram quotient.** `polynomialMkF_eps (symWeight R c) ε` in the
orbit basis. The denominator side is fully computable (`gramDenEntryEps`); the numerator side waits
on the `crossNumerator_eps` orbit-free re-index (TODO). The ε-analog of `polynomialMkF_symWeight`,
and the object whose `> 2/ϑ` (via `EpsBridge.mk_eps_50_witness_of_poly`) discharges
`mk_eps_50_witness` → unconditional `H₁ ≤ 246`. -/
theorem polynomialMkF_eps_symWeight {n : ℕ} (R : Finset (MultiIndex (n + 1)))
    (c : MultiIndex (n + 1) → ℚ) (ε : ℚ)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (monoOrbit a) (monoOrbit b)) :
    polynomialMkF_eps (symWeight R c) ε
      = (∑ a ∈ R, ∑ b ∈ R, c a * c b * crossNumerator_eps (orbitSum a) (orbitSum b) ε)
          / (∑ a ∈ R, ∑ b ∈ R, c a * c b * gramDenEntryEps a b ε) := by
  unfold polynomialMkF_eps
  rw [polynomialMaynardNumerator_eps_symWeight R c ε hR,
      polynomialMaynardDenominator_eps_symWeight R c ε hR]

/-! ## ε-numerator orbit-free re-index — keystone factorizations

The ε-numerator is denominator-grade per binomial index `m`: the marked coordinate's `(pᵢ+qᵢ)`
cancels in both the `(1-ε)` power and the Dirichlet denominator, leaving a joint-type product
times an `m`-local cell factor. These lemmas isolate that structure. -/

/-- **`removeNth` deletes the marked coordinate from the coordinate sum.** -/
lemma sum_removeNth_add {n : ℕ} (p q : Fin (n + 1) → ℕ) (i : Fin (n + 1)) :
    (∑ j, Fin.removeNth i (p + q) j) = (∑ j, (p + q) j) - (p i + q i) := by
  have hre : (∑ j, Fin.removeNth i (p + q) j) = ∑ j, ((p + q) (i.succAbove j)) := rfl
  have h := Fin.sum_univ_succAbove (fun j => (p + q) j) i
  rw [hre]
  simp only [Pi.add_apply] at h ⊢
  omega

/-- **Dirichlet-slack factorization at the marked coordinate.** Deleting coordinate `i` from
`p+q` factors `dirichletIntegralWithSlack` as the full joint-type product `∏ⱼ(p+q)ⱼ!` over the
marked-cell factorial `(pᵢ+qᵢ)!`, times the slack factorial, over the (per-joint-type, per-slack
**constant**) Dirichlet denominator `(n + |p+q| - (pᵢ+qᵢ) + s)!`. The ε-analog core of
`numerator_summand_factor`. -/
lemma dirichletSlack_removeNth_factor {n : ℕ} (p q : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (s : ℕ) :
    dirichletIntegralWithSlack (Fin.removeNth i (p + q)) s
      = (∏ j, (((p + q) j).factorial : ℚ)) * (s.factorial : ℚ)
          / (((p i + q i).factorial : ℚ) *
              ((n + ((∑ j, (p + q) j) - (p i + q i)) + s).factorial : ℚ)) := by
  unfold dirichletIntegralWithSlack
  rw [sum_removeNth_add p q i]
  have hprod : (∏ j, (((p + q) j).factorial : ℚ))
      = (((p + q) i).factorial : ℚ) * ∏ j, ((Fin.removeNth i (p + q) j).factorial : ℚ) :=
    Fin.prod_univ_succAbove (fun m => (((p + q) m).factorial : ℚ)) i
  have hne : ((p i + q i).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hprod]
  simp only [Pi.add_apply]
  field_simp

/-- The **ε-constant factor** of binomial index `m` at joint-type degree `d = |p+q|`:
`(2ε)^m·(1-ε)^{n+d+2-m}/(n+d+2-m)!`. Depends on `(p,q)` only through `d` (constant per joint
type), not the marked cell. -/
noncomputable def affineConstFactor (n d m : ℕ) (ε : ℚ) : ℚ :=
  (2 * ε) ^ m * (1 - ε) ^ (n + d + 2 - m) / ((n + d + 2 - m).factorial : ℚ)

/-- The **ε-local cell factor** of binomial index `m` at marked cell `(a,b) = (pᵢ,qᵢ)`:
`C(a+b+2,m)·(a+b+2-m)!/(a+b)!`. Depends on `(p,q)` only through the marked cell. -/
noncomputable def affineLocalFactor (a b m : ℕ) : ℚ :=
  ((Nat.choose (a + b + 2) m : ℚ)) * ((a + b + 2 - m).factorial : ℚ) / ((a + b).factorial : ℚ)

/-- **ε-`affineSlackRat` factored over the marked coordinate.** `affineSlackRat(removeNthᵢ(p+q),
pᵢ+qᵢ+2, ε)` is the joint-type product `∏ⱼ(p+q)ⱼ!` times a sum over the binomial index `m` of a
joint-type-degree-constant factor `affineConstFactor` and a marked-cell-local factor
`affineLocalFactor`. The full ε-analog of `numerator_summand_factor` (the `m=0` term is the non-ε
case). The `(pᵢ+qᵢ)` cancellation (`dirichletSlack_removeNth_factor`) is what makes the const
factor cell-independent. -/
lemma affineSlackRat_removeNth_factor {n : ℕ} (p q : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (ε : ℚ) :
    affineSlackRat (Fin.removeNth i (p + q)) (p i + q i + 2) ε
      = (∏ j, (((p + q) j).factorial : ℚ)) *
          ∑ m ∈ Finset.range (p i + q i + 2 + 1),
            affineConstFactor n (∑ j, (p + q) j) m ε * affineLocalFactor (p i) (q i) m := by
  have hcd : (p i + q i) ≤ ∑ j, (p + q) j := by
    have := Finset.single_le_sum (f := fun j => (p + q) j) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
    simpa [Pi.add_apply] using this
  unfold affineSlackRat
  rw [sum_removeNth_add p q i, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm2 : m ≤ p i + q i + 2 := by
    rw [Finset.mem_range] at hm; omega
  rw [dirichletSlack_removeNth_factor p q i (p i + q i + 2 - m)]
  have hexp : n + ((∑ j, (p + q) j) - (p i + q i)) + (p i + q i + 2 - m)
      = n + (∑ j, (p + q) j) + 2 - m := by omega
  have hpow : (1 - ε) ^ (n + (∑ j, (p + q) j) + 2 - m)
      = (1 - ε) ^ (n + ((∑ j, (p + q) j) - (p i + q i))) * (1 - ε) ^ (p i + q i + 2 - m) := by
    rw [← pow_add]; congr 1; omega
  unfold affineConstFactor affineLocalFactor
  rw [hexp, hpow]
  have hne : ((p i + q i).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hne2 : ((n + (∑ j, (p + q) j) + 2 - m).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- **ε-numerator per-(p,q) summand: pull the joint-type product out of the marked sum.** The
joint-type product `∏ⱼ(p+q)ⱼ!` is independent of the marked coordinate `i`, so the marked-sum
`∑ᵢ 1/((pᵢ+1)(qᵢ+1))·affineSlackRat(...)` factors as `∏ⱼ(p+q)ⱼ!` times a sum of per-cell
`affineConstFactor·affineLocalFactor` weights. The ε-analog of `numerator_combinatorial_factored`'s
per-pair collapse — each per-`i` summand depends on `(p,q)` only through the joint type
(`∏ⱼ(p+q)ⱼ!` and the cell `(pᵢ,qᵢ)` plus the constant degree `|p+q|`). -/
lemma eps_summand_factor {n : ℕ} (p q : Fin (n + 1) → ℕ) (ε : ℚ) :
    (∑ i, (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
        affineSlackRat (Fin.removeNth i (p + q)) (p i + q i + 2) ε)
      = (∏ j, (((p + q) j).factorial : ℚ)) *
          ∑ i, (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
            ∑ m ∈ Finset.range (p i + q i + 2 + 1),
              affineConstFactor n (∑ j, (p + q) j) m ε * affineLocalFactor (p i) (q i) m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [affineSlackRat_removeNth_factor p q i ε]
  ring

/-- The **per-cell ε numerator factor** at marked cell `cb = (a,b)`, joint-type degree `d`:
`1/((a+1)(b+1))·∑ₘ affineConstFactor·affineLocalFactor`. The ε-analog of `markedCellFactor`. -/
noncomputable def epsMarkedCell (n d : ℕ) (cb : ℕ × ℕ) (ε : ℚ) : ℚ :=
  (1 : ℚ) / (((cb.1 + 1 : ℕ) : ℚ) * ((cb.2 + 1 : ℕ) : ℚ)) *
    ∑ m ∈ Finset.range (cb.1 + cb.2 + 2 + 1),
      affineConstFactor n d m ε * affineLocalFactor cb.1 cb.2 m

/-- The **ε numerator pair weight** of a joint multiset `X` at degree `d`: `jointWeight X` times the
multiset sum of `epsMarkedCell`. The ε-analog of `pairWeight`; for an orbit pair `d = |α|+|β|`. -/
noncomputable def epsPairWeight (n d : ℕ) (X : Multiset (ℕ × ℕ)) (ε : ℚ) : ℚ :=
  jointWeight X * (X.map (fun cb => epsMarkedCell n d cb ε)).sum

/-- **ε-numerator per-(p,q) summand = ε pair weight of the joint multiset.** For an orbit pair
(`p∈orbit α`, `q∈orbit β`, so `|p+q| = |α|+|β|`), the marked sum depends on `(p,q)` only through
`jointMultiset q p`, equalling `epsPairWeight` at the constant degree `|α|+|β|`. The ε-analog of
`numerator_summand_eq_pairWeight` — the bridge that lets the ε double orbit sum regroup over the
(p,q) joint type. -/
lemma eps_numerator_summand_eq_pairWeight {n : ℕ} (α β : MultiIndex (n + 1)) (ε : ℚ)
    {p q : MultiIndex (n + 1)} (hp : p ∈ monoOrbit α) (hq : q ∈ monoOrbit β) :
    (∑ i, (1 : ℚ) / (((p i + 1 : ℕ) : ℚ) * ((q i + 1 : ℕ) : ℚ)) *
        affineSlackRat (Fin.removeNth i (p + q)) (p i + q i + 2) ε)
      = epsPairWeight n (α.degree + β.degree) (jointMultiset q p) ε := by
  rw [eps_summand_factor p q ε]
  have hdeg : (∑ j, (p + q) j) = α.degree + β.degree := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [monoOrbit_mem_degree α hp, monoOrbit_mem_degree β hq]
  rw [hdeg]
  unfold epsPairWeight
  rw [← prodFactorial_eq_jointWeight q p]
  simp only [Pi.add_apply]
  congr 1
  unfold epsMarkedCell jointMultiset
  rw [Multiset.map_map]
  rfl

end OrbitFree

end BoundedGaps
