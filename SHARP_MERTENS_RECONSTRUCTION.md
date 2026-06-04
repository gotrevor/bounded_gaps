# Sharp Mertens `∑_{n≤x} μ²(n)/φ(n) = log x + O(1)` — reconstructed proof

**Date**: 2026-06-04. Reconstructed locally (the route the prior handoffs missed).
This is the elementary, Lean-friendly Dirichlet-convolution proof. It supersedes
the open `ON-LINE-REQUEST.md` sharp-Mertens item (which can stay open only as a
cross-check; we no longer block on it).

## The missing idea: factor out `ζ(s+1)`, not `ζ(s)`

Write `g(n) = μ²(n)/φ(n)` (the Selberg/sieve summand). The prior laps tried
`g = 1 ⋆ a` (factor `ζ(s)`); that fails because `a(p)=1/(p-1)−1≈−1` makes
`∑a(d)/d` diverge. The correct comparison is with `ζ(s+1)` (whose coefficients are
`1/n`, NOT `1`). The Dirichlet series

  `D(s) = ∑ g(n) n^{−s} = ∏_p (1 + 1/((p−1)p^s))`

has the SAME simple pole at `s=0` as `ζ(s+1) = ∏_p (1−p^{−(s+1)})^{−1}`. So set

  `G(s) := D(s)/ζ(s+1) = ∏_p (1 + 1/((p−1)p^s))·(1 − p^{−(s+1)})`,

which converges in a neighborhood of `s=0`. Then `D = ζ(s+1)·G` means, at the
level of arithmetic functions (Dirichlet coefficients):

  `g = u ⋆ B`,   where `u(n) = 1/n`  (coeffs of `ζ(s+1)`),
                       `B`     = coeffs of `G(s)`.

Equivalently, with `B := μ ⋆ (id·g)` (Möbius inverse of `n·g(n)`):

  **`∑_{e|n} B(e) = n·g(n) = n·μ²(n)/φ(n)`.**     (★)  [this is `ζ⋆B = id·g`]

`B` is multiplicative; its prime-power values (verified by hand, and to be checked
in Lean on prime powers) are

  `B(1)=1,  B(p)=1/(p−1),  B(p²)=−p/(p−1),  B(p^k)=0 (k≥3)`.

Set `b(e) := B(e)/e`, so `b(1)=1, b(p)=1/(p(p−1)), b(p²)=−1/(p(p−1)), b(p^k)=0`.

Sanity (verified): n=1,2,3,4 all satisfy (★). E.g. n=4: `∑_{e|4}B(e)=B(1)+B(2)+B(4)=1+1−2=0=4·g(4)` since `g(4)=μ²(4)/φ(4)=0`. ✓

## The summation

From (★), for `n ≥ 1`: `g(n) = (1/n) ∑_{e|n} B(e)`. Reindex `n=em`:

  `S(x) := ∑_{n≤x} g(n) = ∑_{e≤x} (B(e)/e) · H(⌊x/e⌋)`,    `H(M):=∑_{m≤M} 1/m`.

Use the two-sided harmonic bound (mathlib `log_le_harmonic`, `harmonic_le_one_add_log`):
`H(⌊x/e⌋) = log(x/e) + R_e` with `|R_e| ≤ 1 + log 2 ≤ 2` uniformly for `1 ≤ e ≤ x`
(since `⌊x/e⌋ ≥ 1` and `(x/e)/⌊x/e⌋ ≤ 2`). Hence

  `S(x) = log x · ∑_{e≤x} b(e)  −  ∑_{e≤x} b(e) log e  +  ∑_{e≤x} b(e) R_e`.

Three facts finish it (each an absolutely-convergent-series tail estimate):

1. **`∑_e b(e) = 1`** with tail `∑_{e>x}|b(e)| = O(x^{−1/2})` (dominant tail term is
   `b(p²)`, `p>√x`, giving `≪ 1/(√x log x)`). The full sum is `1` because the local
   Euler factor telescopes: `1 + b(p) + b(p²) = 1 + 1/(p(p−1)) − 1/(p(p−1)) = 1`.
   Thus `log x · ∑_{e≤x}b(e) = log x · (1 − O(x^{−1/2})) = log x + o(1)`.
2. **`∑_e |b(e)| log e < ∞`** (terms `≪ p^{−2} log p`), so `∑_{e≤x} b(e) log e = O(1)`.
3. **`∑_e |b(e)| < ∞`** (terms `≪ p^{−2}`), so `∑_{e≤x} b(e) R_e = O(∑|b(e)|) = O(1)`.

Therefore **`S(x) = log x + O(1)`**, i.e. leading coefficient exactly 1 — precisely
what GPY/Maynard sub-step (c) needs (`∑μ²/φ ∼ log x`, hence `α = I(F)`). The sharper
`log x + C + o(1)` would follow from `H(M)=log M+γ+O(1/M)` + full tail control, but the
two-sided `+O(1)` already pins the coefficient.

## Formalization status (2026-06-04, `BoundedGaps/SharpMertens.lean`) — DONE except 2 leaves

**The full reduction is formalized and axiom-clean.** `sharp_mertens_tendsto`:
`(∑_{n≤N} μ²(n)/φ(n)) / log N → 1` (leading coefficient EXACTLY 1) — conditional ONLY
on two summability facts. Chain (all `#print axioms` = `[propext, Classical.choice,
Quot.sound]`):

- ✅ **Algebraic core (★)** — `idG := pmul idR g`, `BSharp := μ * idG`,
  `zeta_mul_BSharp`, `sum_divisors_BSharp` (★), `BSharp` multiplicativity + explicit
  prime-power values (`BSharp_prime/_sq/_pow_high`).
- ✅ **Reindex** — `sum_divisorpairs` (generalized Dirichlet swap) +
  `sum_g_eq_weighted_harmonic`: `S(N) = ∑_{e≤N}(B(e)/e)·H(⌊N/e⌋)`.
- ✅ **Harmonic remainder** — `harmonic_remainder_mem`: `r_e = H(⌊N/e⌋)−log(N/e) ∈ [0,1]`.
- ✅ **Decomposition** — `sum_g_decomp`: `S(N) = P(N)·log N − Q(N) + R(N)`.
- ✅ **Main coefficient `P(N) → 1`** — `bAF := B/e`, local Euler factor `∑'_e b(p^e)=1`
  (`tsum_bAF_primePow`), mathlib `eulerProduct_tprod` ⇒ `∑'_n b(n)=1`
  (`tsum_bAF_eq_one`), partial sums `P(N) → 1` (`P_tendsto_one`).
- ✅ **`Q/log, R/log → 0`** — `abs_remainder_term_le`, `abs_logweighted_term_le` +
  squeeze, all inside `sharp_mertens_tendsto`.
- ✅ **Summability discharge** — `summable_norm_bAF_of_bound` /
  `summable_norm_bAF_log_of_bound`: reduce the two hypotheses to uniform partial-sum
  bounds `∑_{e≤N}|b(e)| ≤ C`, `∑_{e≤N}|b(e)||log e| ≤ C`.

**The two open leaves** (both elementary Euler-product bounds, Aristotle-shaped):
1. `∑_{e≤N} |b(e)| ≤ 8` — Aristotle job `830e5129` (in flight). `b(e)≠0 ⟺` all
   prime exponents `≤2`; `|b|=∏_{p|·}1/(p(p-1))`; bounded by `(∑_{sqfree}∏1/(p(p-1)))²
   ≤ (exp 1)² < 8`.
2. `∑_{e≤N} |b(e)|·|log e| ≤ C` — the `log`-weighted companion (same shape; `log e`
   spreads over prime factors via `log(ab)=log a+log b`, each prime contributes
   `log p · |b|`-weight, still `≪ p^{-2}log p` summable).

Porting either bound (replay on the concrete `bAF` using `bAF_prime/_sq/_pow_high`)
→ feed `summable_norm_bAF_…_of_bound` → makes `sharp_mertens_tendsto` unconditional.
