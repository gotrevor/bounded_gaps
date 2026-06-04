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

## Formalization plan (status: algebraic core being formalized this lap)

- **Algebraic core (★)** — `BoundedGaps/SharpMertens.lean`:
  `idG := pmul id g`, `BSharp := μ * idG`, `zeta_mul_BSharp : ζ * BSharp = idG`
  (pure Dirichlet algebra via `coe_zeta_mul_coe_moebius`), and `sum_divisors_BSharp`
  giving (★). Prime-power values + multiplicativity of `BSharp`. ← THIS LAP.
- **Reindex** `S(x) = ∑_{e≤x}(B(e)/e)H(⌊x/e⌋)` — divisor-pair swap (n=em), a
  `dirichlet_hyperbola`-style interchange.
- **Three tail estimates** (1)(2)(3) — multiplicative-function convergence; each a
  good self-contained Aristotle target.
- **Assembly** — combine with mathlib harmonic bounds → `log x + O(1)`.
