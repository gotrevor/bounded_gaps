/-
scratch_mertens.lean — try-to-fail on the sieve-side multi-month nut's prerequisite.

Target (classical Mertens-type): ∑_{n≤N} μ²(n)/φ(n) ~ log N.
We attempt the LOWER bound  log N ≤ ∑_{n≤N} μ²(n)/φ(n)  (the unconditional,
EH-free half), to read off how much mathlib v4.29.1 carries vs how much is real
work. Standalone file at repo root — NOT in the lakefile lib, so it does not
touch the fleet's BoundedGaps/ build. Build: `lake env lean scratch_mertens.lean`.
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecificLimits.Basic

open ArithmeticFunction Finset

/-- The Mertens summand `μ²(n)/φ(n)` (zero off the squarefree numbers). -/
noncomputable def mertensSummand (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

/-- **THE NUT.** `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)`.

Classical proof: `μ²(n)/φ(n)` is multiplicative with `g(p)=1/(p-1)` and
`g(p^k)=0` (k≥2); expand `1/(p-1)=∑_{j≥1}p^{-j}` so that
`g(q)=∑_{m: rad(m)=q} 1/m`, whence
`∑_{q≤N} g(q) = ∑_{m: rad(m)≤N} 1/m ≥ ∑_{m≤N} 1/m` (since `rad m ≤ m`).

mathlib has the two ENDPOINTS (geometric series, harmonic↔log) but NOT this
rearrangement: there is no `radical : ℕ → ℕ`, and the Euler-product expansion of
a multiplicative function as `∑∏ = ∏∑` over `primeFactors` would have to be
built. This single lemma is the genuine multi-day-to-week core. -/
theorem mertens_crux (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n := by
  sorry

/-- Mechanical: `harmonic N` (a ℚ range-sum) equals the ℝ `Icc 1 N` sum of `1/n`.
Reindex `range N` (term `1/(i+1)`) ↔ `Icc 1 N` (term `1/n`), then cast ℚ→ℝ.
Pure plumbing, no mathematical content. -/
theorem harmonic_eq_icc_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
  sorry

/-- The EItHER-FREE endpoint: `log N ≤ harmonic N`. This part is essentially a
mathlib one-liner (`log_le_harmonic_floor` + `Nat.floor_natCast`). -/
theorem log_le_harmonic (N : ℕ) : Real.log N ≤ (harmonic N : ℝ) := by
  have h := log_le_harmonic_floor (N : ℝ) (by positivity)
  rwa [Nat.floor_natCast] at h

/-- **Assembled lower bound.** `log N ≤ ∑_{n≤N} μ²(n)/φ(n)`.
Endpoint (`log_le_harmonic`) is real and compiles; the two `sorry`s above mark
exactly where the work is (one mechanical, one the multi-month nut). -/
theorem mertens_lower (N : ℕ) :
    Real.log N ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n :=
  calc Real.log N ≤ (harmonic N : ℝ) := log_le_harmonic N
    _ = ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := harmonic_eq_icc_sum N
    _ ≤ ∑ n ∈ Finset.Icc 1 N, mertensSummand n := mertens_crux N
