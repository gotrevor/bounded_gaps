# Online research requests — bounded_gaps

## 2026-06-05 — The y-space smoothing residual (Möbius-mean / PNT-strength)

**Context.** As of lap 8 the contour-free y-space `s1` MAIN TERM is fully machine-checked and
unconditional for primorial `W` (`hBaseW` discharged in `CoprimeMertens.lean`; see
`PENDING_WORK.md` lap-8). The SOLE remaining `s1` input is the off-diagonal correction `hcorr`,
whose two SIZE estimates both reduce to the **smoothing estimate** for the y-space sieve coefficient
`yLambda R F L d = d·∑_{s∈R, d∣s} μ(s/d)·F(log s/L)/φ(s)`.

This lap I proved the ELEMENTARY first reduction (`S1Correction.yLambda_factor`):
`yLambda R F L d = (d/φ(d))·∑_{s∈R, d∣s} μ(s/d)·F(log s/L)/φ(s/d)` for `R` squarefree, `d ≥ 1`.
Reindexing `t = s/d`, the residual is `R_d(F) := ∑_{t : dt∈R} μ(t)·F(log(dt)/L)/φ(t)`, and the
smoothing claim is `R_d(F) ≈ (1/φ(d))·(−F′)/log R`-type — i.e. a **Möbius-weighted (μ/φ) average
with cancellation**, of PNT/`1/ζ(1+w)` strength. The lap-4 verdict (`s1-derivative-landmine`
memory) concluded this is genuinely PNT-strength and that THIS mathlib (v4.29.1) has no quantitative
PNT (`ψ(x)~x`) nor Möbius mean (`∑_{n≤x}μ(n)/n → 0`).

**What I need (any of):**
1. Is there, in *current* mathlib (master, not just v4.29.1), a quantitative **Möbius-mean** result
   `∑_{n≤x} μ(n)/n → 0` (or `= O(1/log x)`), or the **PNT** `ψ(x)~x` / `π(x)~x/log x`, that could be
   imported to discharge the smoothing? Name the exact declaration(s) and file.
2. Is there an existing **Lean formalization** of the GPY/Maynard `PartialSummation` /
   `S1Summation2` smoothing step (or of the prime-number theorem with a `O(1/log)` Möbius bound) in
   any public repo (e.g. `PrimeNumberTheoremAnd`, Kontorovich et al.) that could be ported? Give repo
   + theorem name.
3. Failing a full PNT: is there an *elementary* (Selberg-symmetry / no-contour) bound that yields the
   `o(M (log R)^k)` SIZE estimate for the s1 off-diagonal correction WITHOUT the sharp constant —
   e.g. a second-moment / large-sieve majorant for `∑_{d,e} |λ_d λ_e|/[d,e]` over the y-space `λ`?
   (The naive `|yLambda| ≤ d·C·∑1/φ` bound is off by `(log R)²` per coordinate, so cancellation is
   required.) Cite the precise inequality + source if one exists.

**Why it unblocks:** any of these discharges `hcorr` → the contour-free y-space `s1` becomes fully
unconditional, leaving only the `B^{±k}` flip (Trevor's architectural call) and `s2`/BV.
