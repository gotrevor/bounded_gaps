# Handoff: bounded_gaps — `polynomialMkF_eq_MkF` DONE (k-dim simplex Dirichlet integral built)

**Date**: 2026-05-31 ~05:30 UTC · **Branch**: `path-a-selberg-nu` (14 commits, local-only in the **lean-yolo-box** — no push/PR here). HEAD = `0687c32`.

*Supersedes `HANDOFF-SESSION-2026-05-31-0330.md`. That doc closed `Mk_ge_polynomialMkF`; this one closes the OTHER half, `polynomialMkF_eq_MkF`. The full polynomial-witness route is now sorry-free + axiom-clean.*

## 🎯 What we're doing
Formalizing Polymath8b (bounded gaps) in Lean 4 / mathlib v4.29.1, discharging sieve `sorry`/`axiom`/`opaque` leaves to genuine citations. **The real metric is `#print axioms` on flagships (no `sorryAx`).**

## ✅ This session: the entire `polynomialMkF_eq_MkF` bridge — proven, axiom-clean
The 0330 handoff budgeted this as "the genuinely hard remaining analysis, not de-risked... multi-session" and flagged the missing **k-dim simplex Dirichlet integral** as the wall. It's done in one session. Commit `0687c32`.

- **`polynomialMkF_eq_MkF`** (`Sieve.MkF k P.toFun = (polynomialMkF P : ℝ)`) is a real proof. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- **`Mk_gt_four_of_polynomial_witness` is now FULLY axiom-clean** too (`[propext, Classical.choice, Quot.sound]`) — both halves of the polynomial-witness route (`Mk_ge_polynomialMkF` from last session + this bridge) are sorry-free. The `H1 ≤ 240` route is wired modulo plugging in an actual `P : PolynomialSieveWeight 49` with `polynomialMkF P > 4` (the "numerics here" target, untouched).
- **Sorries 5 → 4.** Remaining real `:= sorry`: `Prerequisites:90/97` (GEH→EH, EH→MPZ), `Polymath8b:796` (twin/Goldbach §8), `Zhang:36` (70M). **None on the polynomial-witness / H_m path.**
- **Full library build green: 8252 jobs.**

### What got built (all in `SievePolynomial.lean`, `section DirichletBridge`, before `Mk_gt_four_of_polynomial_witness`)
mathlib LACKS the k-dim Dirichlet integral `∫_Δk ∏ tᵢ^{αᵢ}(1-∑t)^β = ∏αᵢ!·β!/(k+|α|+β)!`; built bottom-up, all axiom-clean:
- **`dirichlet_1d`** — 1-D Beta keystone `∫₀^c tᵃ(c-t)ᵇ = c^{a+b+1}·a!b!/(a+b+1)!`. Induction on `b` via `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (IBP, `u=(c-t)^{b+1}`, `v'=tᵃ`, boundary terms vanish, recurrence `D(a,b+1)=(b+1)/(a+1)·D(a+1,b)`); base from `integral_pow`. Pure ℝ — sidesteps mathlib's ℂ-valued `betaIntegral` entirely.
- **`simplex_fubini`** — `∫_Δ(n+1) G = ∫_{s∈Δn}∫_{ti∈[0,1-∑s]} G(insertNth i ti s)` for continuous G. Via `integral_insertNth_eq` (already in `Sieve.lean`) + `Set.indicator` of the simplex; the membership iff `insertNth i ti s ∈ Δ(n+1) ↔ ti ∈ [0,1-∑s]` (given `s ∈ Δn`) collapses the inner integral; off-simplex `s` contributes 0.
- **`dirichlet_slack`** — the master k-dim integral, induction on dimension (`generalizing β`, since the slack grows per layer): inner layer = `dirichlet_1d`, outer = IH. Base `k=0` via `MeasureTheory.integral_unique` + `volume_pi` (the `Fin 0 → ℝ` point has measure 1).
- **`monomialIntegral_eq`** (β=0 case), **`dirichletSlack_eq`** — real-valued closed forms matching the ℚ defs.
- **`inner_eq`** — the inner `ti`-integral of `P.toFun∘insertNth` factored: `∑_p c_p (∏ s^{p'}) T^{p_i+1}/(p_i+1)`.
- **`denom_bridge`** (`mkF_denominator = polynomialMaynardDenominator`) — expand `(∑ c_p∏tᵖ)²` via `Finset.sum_mul_sum`, termwise integrate (`integral_finset_sum`), apply `monomialIntegral_eq`.
- **`Ji_bridge`** + **`numer_bridge`** — square the inner, integrate over Δn via `dirichlet_slack`, match `dirichletIntegralWithSlack(removeNth i (p+q), p_i+q_i+2)` termwise; sum over `i`.

## 🧠 Context to carry forward
- **The polynomial-witness route is structurally COMPLETE.** What's left for `H1 ≤ 240` is purely the numerics: exhibit a concrete `P : PolynomialSieveWeight 49` and prove `polynomialMkF P > 4` (rational `decide`/`native_decide`/interval arith). That's Polymath8b §6's Maple computation — a big finite object, not analysis. No more missing mathlib theory on this path.
- **The sieve core (`s1`/`s2` axioms) stays cited** — infeasible offline (no Mertens/Selberg/singular-series in mathlib). ROADMAP Bucket D. The 4 remaining sorries are §8 twin/Goldbach + Zhang 70M + the GEH/EH/MPZ prerequisites — all off the H_m/polynomial path.

## 🎬 Next actions (pick one)
1. **Numerics for `polynomialMkF P > 4`** — the §6 Maple polynomial for `M_49`. Big finite/rational computation; would close `H1 ≤ 240` end-to-end given the now-complete bridge. Scope the Polymath8b §6 explicit `F` first.
2. **Off-thread:** an anti-[[sum-product]] Erdős target from `erdos-formalization-hunt` (#403 carry-ceiling is the warmest), or the §8 `Polymath8b:796` twin/Goldbach leaf.

## ⚠️ Gotchas (Lean, v4.29.1, box) — new this session
- **`Fin.prod_univ_succAbove (fun a => …) i` fails to `rw`** (leaves the `insertNth` args as metavars). Use **`Fin.prod_univ_succAbove _ i`** (underscore for `f`) — it infers `f` from the goal product.
- **`integral_finset_sum`/`integrable_finset_sum` want `Integrable f (μ.restrict s)`, NOT `IntegrableOn f s`** — same defn but the head symbol blocks unification. State the integrability helper with the `Integrable (… ) (volume.restrict (simplex n))` head (a `simplexIntegrable {f} (hf : Continuous f)` wrapper around `.integrableOn_compact`), then `simplexIntegrable (by fun_prop)` lets `f` unify from the expected type and `fun_prop` prove continuity of the concrete integrand.
- **`integral_indicator` / `integral_congr_ae` are AMBIGUOUS** when both `MeasureTheory` and `intervalIntegral` are open — qualify `MeasureTheory.integral_indicator` etc.
- **`Set.indicator_of_not_mem` was renamed `Set.indicator_of_notMem`** (the `_notMem` camelCase sweep).
- Base case of a dimension induction over `simplex 0`: `simplex 0 = univ`, `MeasureTheory.integral_unique` (the space is `Unique`), `volume (univ : Set (Fin 0 → ℝ)) = 1` via `simp [measureReal_def, MeasureTheory.volume_pi]`.
- After `setIntegral_congr_fun`, the per-point goal is a `(fun s => …) s` beta-redex — `dsimp only` before `rw`.
- `push_cast`/`simp only [Rat.cast_mul]` to split `↑(p.2 * q.2)` so `ring` (which doesn't know `Rat.cast_mul`) can match `↑p.2 * ↑q.2`.

## 📁 Key files
- `BoundedGaps/SievePolynomial.lean` — `section DirichletBridge` (all the above, ~line 518) + `polynomialMkF_eq_MkF` + `Mk_gt_four_of_polynomial_witness` (now uses it). The forward-pointer note is at the old `## The bridge` heading (~line 142).
- `BoundedGaps/Sieve.lean` — `simplex`, `MkF`/`mkF_numerator`/`_denominator`, `integral_insertNth_eq`, `isCompact_simplex`/`isClosed_simplex`.
- `ROADMAP.md` — tiers + axiom buckets.

---
**→ Next session: the polynomial-witness route is structurally done and axiom-clean. Either chase the §6 numerics (`polynomialMkF P > 4` for an explicit `M_49` witness) to close `H1 ≤ 240` end-to-end, or pivot to an anti-[[sum-product]] target. Don't re-open `polynomialMkF_eq_MkF` or `Mk_ge_polynomialMkF` — both done, both axiom-clean.**
