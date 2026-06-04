# Handoff: bounded_gaps — `Mk_ge_polynomialMkF` DONE (axiom-clean cutoff lemma)

**Date**: 2026-05-31 ~03:30 UTC · **Branch**: `path-a-selberg-nu` (13 commits, local-only in the **lean-yolo-box** — no push/PR here)

*Supersedes `HANDOFF-SESSION-2026-05-31-0210.md`. The cutoff thread that doc started is now finished.*

## 🎯 What we're doing
Formalizing Polymath8b (bounded gaps) in Lean 4 / mathlib v4.29.1, discharging sieve `sorry`/`axiom`/`opaque` leaves to genuine citations. **The real metric is `#print axioms` on flagships (no `sorryAx`).**

## ✅ This session: the entire `Mk_ge_polynomialMkF` cutoff lemma — proven, axiom-clean
The previous handoff budgeted **2-3 sessions** for this; it's done in one. Commit `5c02aed`.

- **`SievePolynomial.Mk_ge_polynomialMkF`** (`Sieve.Mk k ≥ Sieve.MkF k P.toFun`) is now a real proof. `#print axioms` = `[propext, Classical.choice, Quot.sound]` — **no sorryAx, no project axioms.**
- **Sorries 6 → 5.** Remaining: `Prerequisites:90/96`, `Polymath8b:794` (twin/Goldbach §8), `Zhang:34`, `SievePolynomial:154` (`polynomialMkF_eq_MkF`). **None on the H_m path; none on `Mk_ge_polynomialMkF` any more.**
- **Full library build green: 8260 jobs** (box still OOMs randomly on Polymath8b/Maynard/TwinPrimes — `Cannot allocate memory` — retry 1-3×).
- All the new machinery lives in `SievePolynomial.lean` (namespace `BoundedGaps.SievePolynomial`), inserted as a `## Discharge …` section before `## Reducing`. `SievePolynomial.lean` now also `import BoundedGaps.SimplexCutoff` and `open MeasureTheory Filter Topology / open Sieve / open scoped ContDiff`.

### What got built (all reusable, all axiom-clean)
- `toFun_contDiff`/`toFun_continuous`/`toFun_bounded` — `P.toFun` is `C^∞`, continuous, bounded on the compact simplex.
- `Fapprox P n := χ_n · P`, `Fapprox_contDiff`, `Fapprox_support`, `Fapprox_mem_MkSet`; `denom_nonneg`/`numer_nonneg`/`MkSet_nonneg`/`Mk_nonneg`.
- **Geometry (conull open simplex):** `convex_simplex`, `interior_simplex_subset` (interior ⊆ open simplex, via a `Metric.mem_nhds_iff` perturbation `t ± (ε/2)·e_i` that leaves the simplex), `simplex_diff_open_null` (= 0, via `Convex.addHaar_frontier` + `IsClosed.frontier_eq`), `ae_open_simplex`.
- **`denom_tendsto`** — denominator DCT `∫_simplex (χ_n·P)² → ∫_simplex P²` (`tendsto_integral_of_dominated_convergence`; arg order is `meas, bound_integrable, h_bound, h_lim`).
- **`insertNth` transport:** `insertNth_sum` (`∑ = ti + ∑s`), `continuous_insertNth_right`, `insertNth_mem_simplex`, `insertNth_mem_open`.
- **`innerInt_tendsto`** — inner `ti`-layer DCT (for `s` in the open simplex).
- **`J_i_tendsto`** — outer `s`-layer DCT. The one hard sub-goal (parametric-integral **measurability** with a variable upper bound) is solved by `intervalIntegral.continuous_parametric_primitive_of_continuous`: rewrite `∫ ti in Icc 0 (1-∑s)` as `∫ ti in 0..(1-∑s)` (valid a.e. on the simplex, where `1-∑s ≥ 0`) and note the integrand is jointly continuous.
- **`numer_tendsto`** (= `∑ i, J_i_tendsto`), then the `Mk_ge_polynomialMkF` assembly (`le_of_tendsto` + `le_csSup (MkSet_bddAbove)`).

## 🧠 Context to carry forward
- **The H_m program + this cutoff lemma close everything reachable on this thread** except `polynomialMkF_eq_MkF` and the unrelated §8/Zhang/Prerequisites leaves.
- **`Mk_gt_four_of_polynomial_witness` still needs `polynomialMkF_eq_MkF`** (the OTHER `SievePolynomial` sorry, line 154). So the full polynomial-witness route (`H1 ≤ 240`) is not yet wired — `Mk_ge_polynomialMkF` is half of it; `polynomialMkF_eq_MkF` is the other half.
- **`polynomialMkF_eq_MkF` needs the simplex Dirichlet integral `∫_Δ ∏ tᵢ^{αᵢ} = ∏αᵢ!/(k+|α|)!`, which mathlib LACKS** — a separate from-scratch build (the closed-form must be derived, then matched termwise against `mkF_numerator`/`mkF_denominator`). This is the genuinely hard remaining analysis on this thread and is **not** de-risked the way the cutoff was. Estimate: multi-session; consider whether it's the best next target vs. an anti-[[sum-product]] pivot (see `erdos-formalization-hunt`).
- **The sieve core (`s1`/`s2` axioms) stays cited** — infeasible offline (no Mertens/Selberg/singular-series in mathlib). ROADMAP Bucket D.

## 🎬 Next actions (pick one)
1. **`polynomialMkF_eq_MkF`** (`SievePolynomial:154`) — the last piece to make `Mk_gt_four_of_polynomial_witness` usable. Build the simplex Dirichlet/Beta integral closed form, then match termwise. Start in a fresh `BoundedGaps/Scratch.lean` (import `BoundedGaps.SievePolynomial`). **Warning:** unlike the cutoff, the key lemma (`∫_Δ monomial = Dirichlet`) is not in mathlib and isn't a quick citation; scope it before committing a session.
2. **Off-thread:** an anti-[[sum-product]] Erdős target from `erdos-formalization-hunt` (#403 carry-ceiling is the warmest), or the §8 `Polymath8b:794` twin/Goldbach leaf.

## ⚠️ Gotchas (Lean, v4.29.1, box)
- **Push/PR is host-only** (no `gh`/`ssh`/egress in box). Trevor pushes the 13-commit branch.
- **`Fin.insertNth` family inference fails** in bare statements/`have`s — ascribe `(i.insertNth ti s : Fin (m+1) → ℝ)`, or wrap a goal as `… ∈ {t : Fin (m+1) → ℝ | …}` to pin it. Prove its continuity **componentwise** (`continuous_pi` + `Fin.exists_succAbove_eq` for the `≠ i` case), not via `Continuous.finInsertNth` (which leaves the family a metavariable).
- **`rcases eq_or_ne j i with rfl` substitutes `j` away** → "unknown identifier j" downstream. Use `by_cases hj : j = i` + `subst hj` / `Fin.exists_succAbove_eq`.
- `tendsto_integral_of_dominated_convergence` goal order: **bound (positional) → `F_measurable` → `bound_integrable` → `h_bound` → `h_lim`** (integrable BEFORE the pointwise bound).
- `integrableOn_const` needs `(hs := measure_…_lt_top.ne)` (the `finiteness` autoparam doesn't always fire); `IsCompact.measure_lt_top` for the simplex, `measure_Icc_lt_top` for intervals.
- Parametric-integral measurability with a variable bound: `intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := 0)`; **pin `μ` explicitly** (else "typeclass instance stuck"). Convert `Set.Icc 0 b` ↔ `0..b` via `intervalIntegral.integral_of_le` + `MeasureTheory.integral_Icc_eq_integral_Ioc`; `dsimp only` to beta-reduce `(fun s => …) s` before the rewrite.
- `MeasureTheory.restrict_Ioo_eq_restrict_Icc` (namespace `MeasureTheory`, **not** `.Measure.`) switches the conull endpoints.
- `lake env lean` doesn't write oleans — `#print axioms` needs `lake build` first. `~/personal` read-only; `~/src` writable.

## 📁 Key files
- `BoundedGaps/SievePolynomial.lean` — **`Mk_ge_polynomialMkF` (done, ~line 506) + all cutoff machinery (157-485)**; `polynomialMkF_eq_MkF` (154, the remaining sorry) + `Mk_gt_four_of_polynomial_witness`.
- `BoundedGaps/SimplexCutoff.lean` — the `χ_n` cutoff (chi_*), unchanged.
- `BoundedGaps/Sieve.lean` — `simplex`, `MkF`/`Mk`/`MkSet`, `mkF_numerator`/`_denominator`, `J_i`, `MkSet_bddAbove`/`_nonempty`, `isCompact_simplex`.
- `ROADMAP.md` — tiers + axiom buckets.

---
**→ Next session: the cutoff thread is closed. Either take `polynomialMkF_eq_MkF` (scope the missing simplex Dirichlet integral FIRST — it's not a citation) or pivot to an anti-[[sum-product]] target. Don't re-open `Mk_ge_polynomialMkF` or the H_m program — both are done and axiom-clean.**
