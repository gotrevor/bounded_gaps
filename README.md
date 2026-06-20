# bounded_gaps 🎯

Lean 4 / mathlib scaffold for **Zhang's bounded gaps between primes** and its progeny (Maynard, Polymath8b → 246, twin primes conjecture).

Top-level theorem statements are in place; **all proofs are `sorry`**. The point is to make the shape of the program — and the dependencies on hard analytic-NT prerequisites — machine-checkable, so individual leaves can be filled in incrementally.

Context, math background, and "what would you actually do" notes:
[~/personal/claude/knowledge/core/projects/lean-journey/side-quests/bounded-gaps.md](../../personal/claude/knowledge/core/projects/lean-journey/side-quests/bounded-gaps.md).

Papers (PDFs + arXiv LaTeX source where available) live in
[papers/](papers/README.md) — gitignored, fetch with the `curl` recipes in that README.
Grep the `.tex` sources to lift exact theorem statements when formalizing.

## Build

```bash
cd ~/src/bounded_gaps
lake build           # mathlib cache already populated; ~1-2 min full build
```

Mathlib pinned at `v4.29.1` to match `~/personal/lean-sandbox/`. Lean toolchain in `lean-toolchain`.

## Module map

| File | Contents | Decls | Sorries |
|------|----------|-------|---------|
| `BoundedGaps/Basic.lean` | Admissible k-tuples, narrowness $H(k)$, `liminfGap m : ℕ∞` matching literature $H_m$, `DHL[k, j]`, equivalences. `primeAt` wired to `Nat.nth Nat.Prime`. `admissibleTuple` concrete for $k \le 3$. **`admissibleTuple_3_admissible` ($p = 2, 3, 5$ cases proven; $p \ge 7$ sorry). `narrowness_3_le_six` fully proven.** | 16 | 5 |
| `BoundedGaps/Prerequisites.lean` | Parameterized `EH ϑ`, `GEH ϑ`, `MPZ ϖ δ`. Bombieri-Vinogradov, Generalized BV, Polymath8a's MPZ result, GEH ⇒ EH. | 8 | 5 |
| `BoundedGaps/Sieve.lean` | **`lambdaF` real body (Möbius divisor sum). `maynardWeight` real body (square of product of `lambdaF`).** Maynard ratio $M_k$ and $M_{k,\varepsilon}$, the four Polymath8b criterion theorems (maynard-thm, maynard-trunc, epsilon-trick, epsilon-beyond), Lemma crit. | 12 | 10 |
| `BoundedGaps/Maynard.lean` | Maynard's Theorem 1.2 (5 statements: $H_1 \le 600$, $H_m$ asymptotic, plus $H_1 \le 12$ / $H_2 \le 600$ / $H_m$ refined under EH). | 5 | 5 |
| `BoundedGaps/Zhang.lean` | Zhang's $H_1 \le 70M$. | 1 | 1 |
| `BoundedGaps/Polymath8b.lean` | The full Theorem 1.3 (13 numerical bounds), Theorem main-dhl (12 DHL claims), Theorem hk-bound, parity_barrier, twin-primes-or-Goldbach disjunction. `narrowness_3 = 6` now structured as ≤ (✓) ∧ ≥ (sorry). | 43 | 40 |
| `BoundedGaps/TwinPrimes.lean` | Twin primes conjecture, $H_1 = 2$ equivalence. | 3 | 1 |
| `BoundedGaps/Engelsma.lean` | **Explicit narrow admissible tuples** for $k = 50$ (diameter 246, Polymath8b), $k = 49$ (diameter 240), $k = 48$ (diameter 236). Length / diameter / sortedness all `native_decide`-verified. Full admissibility on all primes is the one remaining `sorry` per tuple (reduces to a finite check on primes $\le k$). | 12 | 3 |
| `BoundedGaps/Targets.lean` | **The bound-tightening surface.** `H1_le_of_Mk_witness` bridge: admissible $k$-tuple + $M_k > 4$ ⇒ $H_1 \le \text{diameter}$. Instantiated to give `H1_le_246` (current, $k = 50$), `H1_le_240_if_Mk_49_witness` (would improve by 6), `H1_le_236_if_Mk_48_witness` (would improve by 10). | 5 | 1 |
| `BoundedGaps/SievePolynomial.lean` | **Polynomial sieve weights** on the $k$-simplex with rational coefficients. `monomialIntegral` (Dirichlet beta formula). `polynomialMkF` as a rational expression. `Mk_gt_four_of_polynomial_witness`: given a polynomial $P$ with verified rational `polynomialMkF P > 4`, conclude `Sieve.Mk k > 4`. This is the plug-in point for future numerical work. | 11 | 4 |
| `BoundedGaps.lean` | Top-level import surface. | 0 | 0 |
| **TOTAL** | | **116** | **75** |

**116 declarations, 75 sorries, `lake build` green.** Real bodies (not just `sorry`) for: `primeAt`, `lambdaF`, `maynardWeight`, `admissibleTuple` (k ≤ 3), `admissibleTuple_length`, `narrowness_3_le_six`, 3/4 cases of `admissibleTuple_3_admissible`, **all three explicit Engelsma tuples** (length + diameter + sortedness fully verified), the three target theorems wiring the bridge to specific numerical witnesses, and the polynomial-sieve-weight scaffolding.

## The bound-tightening menu

| Bound | Hypothesis | Status | Theorem |
|-------|-----------|--------|---------|
| $H_1 \le 246$ | $M_{50} > 4$ | published 2014 (Polymath8b) | `Targets.H1_le_246` |
| $H_1 \le 240$ | $M_{49} > 4$ | **open** — would improve by 6 | `Targets.H1_le_240_if_Mk_49_witness` |
| $H_1 \le 236$ | $M_{48} > 4$ | **open** — would improve by 10 | `Targets.H1_le_236_if_Mk_48_witness` |
| $H_1 \le 12$ | $\text{EH}[\vartheta]$ for all $\vartheta < 1$ | conjectural (Maynard) | `Maynard.H1_le_12_under_EH` |
| $H_1 \le 6$ | $\text{GEH}[\vartheta]$ for all $\vartheta < 1$ | conjectural, parity-tight (Polymath8b) | `Polymath8b.H1_le_6_under_GEH` |

The 240 and 236 open doors reduce purely to a numerical question on a polynomial sieve weight. The path: build a `PolynomialSieveWeight 49` (or 48), compute `polynomialMkF` rationally, prove the rational inequality $> 4$, then apply `SievePolynomial.Mk_gt_four_of_polynomial_witness` and `Targets.H1_le_240_if_Mk_49_witness`. Polymath8b §7 item 2 explicitly identifies improved polynomial bases (piecewise polynomial supports) as the natural next attempt — this scaffolding makes that work directly composable.

## The dependency graph

```
              Mathlib (entire library, via `import Mathlib`)
                              │
                ┌─────────────┴─────────────┐
                ▼                           ▼
          Basic.lean              Prerequisites.lean
       (Admissible, H(k),         (EH ϑ, GEH ϑ, MPZ ϖ δ,
        DHL[k,j], liminfGap)       BV, GBV, GEH ⇒ EH)
                │                           │
                └──────────┬────────────────┘
                           ▼
                     Sieve.lean
              (M_k, M_{k,ε}, Lemma crit,
               4 DHL-criterion theorems)
                           │
                ┌──────────┼──────────┐
                ▼          ▼          ▼
             Maynard    Zhang     Polymath8b
              (600,    (70M from   (246, parity
              12-EH)     MPZ)     barrier, disj)
                                      │
                                      ▼
                                  TwinPrimes
```

## What's the simplest sorry left to close?

Roughly in order of difficulty:

1. **`Basic.admissibleTuple_3_admissible` — the $p \ge 7$ case.** Needs `Fact (p.Prime)` instance plumbing and `ZMod.val_cast_of_lt` to show that for $a \in \{0, 2, 6\}$ with $a < p$, $(a : \mathrm{ZMod}\ p) = 1 \iff a = 1$. Then witness $r = 1$ misses all three. Maybe 20-30 lines.
2. **`Polymath8b.narrowness_3` — the $\ge 6$ direction.** Once you can decide admissibility for small tuples, enumerate diameters 0-5 and show none is admissible. Could be `decide`-able if `Admissible` instance is given. ~40 lines.
3. **`Basic.admissibleTuple_admissible (k : ℕ)`** — generic. Pick a real construction (e.g., "first $k$ primes after $k$", which is always admissible) and prove it. Needs `Nat.nth Nat.Prime` reasoning. Medium-hard.
4. **`Prerequisites.eh_implies_mpz`** — once the bodies of `EH` and `MPZ` are real (not opaque `axiom : Prop`), this is a direct unfold + the restriction-of-moduli lemma. Currently blocked: bodies are opaque.
5. **`Prerequisites.geh_implies_eh`** — Vaughan's identity decomposition. Mathlib doesn't have Vaughan; would need to land it first.

The huge ones (Maynard's theorem, Polymath8b's variational lower bounds, Zhang's MPZ-dependent argument) stay `sorry` for a long time — they need the full sieve-theoretic + analytic-NT infrastructure that PNT+ is trying to build.

## PNT+ as a future import source

`~/src/PrimeNumberTheoremAnd` exists locally. **Not currently importable** because:
- Version mismatch: PNT+ on Lean v4.29.0, mathlib v4.29.0; we're on v4.29.1. Lake refuses.
- PNT+ doesn't have Bombieri-Vinogradov yet either — they're building toward it via `MobiusLemma`, `Chebyshev`, `Mertens`, `PerronFormula`, `ZetaBounds`, `Wiener`, `MediumPNT`, `StrongPNT`. The analytic-NT stack is being laid; BV would be downstream of `StrongPNT` plus dispersion-method machinery they haven't started.

When versions align *and* BV lands in PNT+, the natural wire-in points would be:
- `Prerequisites.EH` body → could be stated in terms of PNT+'s discrepancy machinery
- `Prerequisites.BombieriVinogradov` → could become a real theorem citing PNT+
- `Sieve.lambdaF` → already uses `Mathlib.NumberTheory.ArithmeticFunction.Moebius` (same as PNT+'s `MobiusLemma`), so no migration needed there

Until then, treat PNT+ as a *parallel* effort to read for inspiration, not as a dependency.

The hard ones (Maynard's main theorem, Zhang's MPZ-dependent argument) stay `sorry` until either the project matures or PNT+ lands the analytic prerequisites.

## Related Lean projects

- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) — local checkout at `~/src/PrimeNumberTheoremAnd`. Building toward Bombieri-Vinogradov; the prereq stack for this project.
- [mathlib4](https://github.com/leanprover-community/mathlib4) — local checkout at `~/src/mathlib4`.

## Status: 🟡 scaffold

Last touched 2026-05-24. Created in one sitting as a "minimum compiling skeleton" so subsequent work has a target structure rather than a blank page.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
