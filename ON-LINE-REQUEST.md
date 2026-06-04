# Online research requests (bounded_gaps)

A networked host session fulfills these: commit an `ON-LINE-FINDINGS-<date>-<topic>.md`,
delete the answered item here, and remove this file once nothing is left open.

---

## 2026-06-04 — Sharp Mertens-type asymptotic `∑_{n≤x} μ²(n)/φ(n) = log x + O(1)`

> **RESOLVED LOCALLY (2026-06-04, lap on `path-a-selberg-nu`).** Reconstructed the
> proof myself (the `ζ(s+1)`-factorization route: `g = u ⋆ B`, `B = μ ⋆ (id·g)`) and
> FORMALIZED it: `BoundedGaps.SharpMertens.sharp_mertens_tendsto` proves
> `(∑_{n≤N} μ²/φ)/log N → 1`, axiom-clean, conditional only on two elementary
> Euler-product partial-sum bounds (one on Aristotle). See
> `SHARP_MERTENS_RECONSTRUCTION.md`. **No longer blocking** — a textbook cross-check
> (Montgomery–Vaughan §2 / Tenenbaum) of the constant `C` would be a nice confirmation
> but is optional. Lower priority.

**What I need.** A clean elementary proof (textbook/paper, with the exact
identity/decomposition used) of the *sharp coefficient-1* asymptotic

  `∑_{n ≤ x} μ²(n)/φ(n) = log x + C + o(1)`   (leading coefficient exactly 1),

or at minimum the two-sided `log x + O(1)`. Ideally the version that is friendly
to a Lean formalization (a Dirichlet-convolution / hyperbola identity I can iterate
on), not an analytic (contour / Perron) proof.

**Why it unblocks me.** This is THE blocker for GPY/Maynard sub-step (c) (the
`s1`/`s2` sieve asymptotics in `Sieve.lean`). The sieve main term needs the
**leading coefficient exactly 1**, i.e. `∑μ²/φ ∼ log x`. What I already have
unconditionally in `BoundedGaps.Mertens` is only the *crude two-sided* bound
`mertens_theta_log`: `log N ≤ ∑μ²/φ ≤ K·log N` with `K = exp(...) ≈ e^γ·(stuff) ≫ 1`
(the upper half goes through `∑μ²/φ ≤ ∏_{p≤N}(1+1/(p-1)) ∼ e^γ log N`, which is
lossy — coefficient `e^γ ≈ 1.78`, not 1). I cannot get the GPY constant `α = I(F)`
from a Θ-bound; I need the genuine `∼ log x`.

**What I've tried / ruled out (so you don't re-derive).**
- The identity `n/φ(n) = ∑_{d∣n} μ²(d)/φ(d)` is PROVEN in-repo
  (`BoundedGaps.SingularSeries.self_div_totient_eq_sum_moebiusSq_div_totient`),
  and the Dirichlet hyperbola `∑_{n≤N}∑_{d∣n} g d = ∑_{d≤N} g d·⌊N/d⌋` too. But these
  give the summatory function of `n/φ(n)` (→ `∑μ²/(φ·d) → A`, a *different* sum),
  NOT `∑μ²/φ` directly.
- The Mobius-inverse decomposition `g = 1 ⋆ a` with `a(p)=1/(p-1)-1 ≈ -1` makes
  `∑ a(d)/d` diverge, so the naive `∑a(d)⌊x/d⌋ = x∑a(d)/d + O(∑|a|)` route fails.
- So I specifically need the *correct* elementary identity/decomposition that
  isolates `∑_{n≤x} μ²(n)/φ(n)`'s `log x` main term with a controlled error.

**Pointers that would most help:** the exact statement+proof from Montgomery–Vaughan
*Multiplicative Number Theory I* (the `μ²/φ` summation, around the Mertens / GPY
material), or Tenenbaum, or the relevant lemma in a Maynard/GPY paper (the
"singular series average"), with the explicit intermediate sums so I can formalize
each step.
