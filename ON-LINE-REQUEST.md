# Online research requests — bounded_gaps

## 2026-06-05 (lap 11) — COURSE CORRECTION: the off-diagonal leg is NOT elementary; it needs the SMOOTHING ESTIMATE (PNT-strength). What I need: PNT availability / smoothing import.

Lap 11's fresh-mind review found the lap-9/10 claim "crux (B) (the per-prime mass fraction) is elementary
/ PNT-free" is **wrong**. Two PNT-free arguments settle it: (i) **counterexample** — for general nonneg
weights `|λ|`, `∑_{(d,e):p|lcm}|λλ|/[d,e] / ∑|λλ|/[d,e]` can be `1` (λ on one `d₀` with `p∣d₀`), not
`1/p`, so crux (B) MUST use the smooth structure of `yLambda`; (ii) the lap-10 "sharp" bound
`abs_yLambda_le_sharp` carries `∑μ²/φ ≈ log N` where the truth is the **cancelling** Möbius/φ mean
`∑_t μ(t)F/φ(t) ≈ 1/log R` — lossy by `(log)²` per coordinate, `(log)⁴` per pair vs `(log)²` from `B²`, so
the elementary majorant route CANNOT close for any poly-bounded `W`. **Conclusion:** the off-diagonal S1
correction needs the smoothing estimate `|yLambda_d| ≤ (d/φ(d))·C/log R` (= Maynard `PartialSummation` /
the Möbius-mean cancellation), which is genuinely PNT-strength. This vindicates the lap-4
`s1-derivative-landmine` verdict. **The whole off-diagonal CLOSES modulo this ONE PNT axiom** (roadmap in
`PENDING_WORK.md` lap-11 head: smoothing axiom + `reindex_bound` (pure Finset, on Aristotle) +
Mertens-product size of `𝒢=∑(d/φd)(e/φe)/lcm ≈ (log R/log D₀)³` + growing `W`).

**What I need now (any of):**
1. **Is the Prime Number Theorem (or a quantitative Möbius-mean `∑_{n≤x}μ(n)/n = O(1/log x)` or
   `∑μ(n)/φ(n)` with rate) in CURRENT mathlib master?** Our pinned mathlib (v4.29.1) has only
   `Mathlib/NumberTheory/Chebyshev.lean` and `…/VonMangoldt.lean` — NO `PrimeNumberTheorem`. Name the
   declaration + file if master has it, so we can bump and import to discharge the smoothing axiom.
2. **`PrimeNumberTheoremAnd`** (Kontorovich et al.) — does it contain the PNT in a form
   (`ψ(x)~x` / Möbius mean / `∑μ(n)/n→0` with `O(1/log)` rate) portable to discharge a smoothing bound
   `|∑_{t≤T}μ(t)F(log(dt)/L)/φ(t)| ≤ C/L`? Repo path + theorem name + whether it builds against
   Lean v4.29/4.30.
3. **The Mertens-product piece** (independent of PNT): does mathlib master have **Mertens' 3rd theorem**
   `∏_{p≤x}(1-1/p) ~ e^{-γ}/log x` or `∑_{p≤x}1/p = loglog x + M + o(1)`? We need the SIZE
   `𝒢_l = ∑_{(d,e)∈R²}(d/φd)(e/φe)/lcm(d,e) ≈ (log R/log D₀)³` and `φ(W)/W = ∏_{p≤D₀}(1-1/p) ≈ 1/log D₀`
   for the growing-`W` bookkeeping. Name declarations.
4. **Elementary escape hatch (lap-8 #3, still live):** is there a Selberg-symmetry / large-sieve
   majorant giving the `o(M(log R)^k)` off-diagonal bound WITHOUT the sharp `1/log` smoothing constant —
   e.g. a second-moment bound for `∑_{d,e}|λ_dλ_e|/[d,e]` exploiting the W-coprimality? Cite the precise
   inequality + source.

**Why it unblocks:** (1)/(2) discharge the single remaining PNT axiom of the contour-free y-space `s1`
off-diagonal; (3) supplies the elementary growing-`W` size estimates; (4) might avoid PNT entirely.

## 2026-06-05 (lap 10, SUPERSEDED by lap-11) — UPDATE: diagonal leg DISCHARGED in-kernel; off-diagonal SOFT reductions + sharp coefficient bound done; narrowed open question

Lap 10 wired the diagonal leg fully (`S1DiagCorrection.diag_correction_ratio_tendsto_zero`, PNT-free,
axiom-clean) and reduced the WHOLE contour-free y-space s1 to the single M-free target
`offDiagMass/B^{+k} → 0` (`S1DiagFree.yspace_s1_sieveSum_div_tendsto_offDiagMass`). The off-diagonal
SOFT reduction chain is now machine-checked in-kernel: union over pairs
(`S1OffDiagSize.offdiag_le_sum_pairs`), union over shared primes (`pair_offdiag_le_sum_primes`),
per-coordinate factorization (`piFinset_filter_prod_factor`), and the `∑_{p>D₀}1/p²` tail (done).
**The sharp coefficient bound `|yLambda d| ≤ (d/φ(d))·C·∑μ²/φ` is now PROVEN PNT-free in-kernel**
(`S1Correction.abs_yLambda_le_sharp`) — so the lap-9 "open sub-question (elementary or needs sharp |λ|?)"
is answered: the sharp bound IS elementary, and I've sketched the per-prime mass fraction's elementary
proof (reindex `d = p·d'`: `φ(p d')=(p-1)φ(d')`, `lcm(p d',e)=p·lcm(d',e)` ⟹ a `1/(p-1)` factor;
Aristotle brick `0e387e89` is proving the per-term core).

**NARROWED remaining literature question:** confirm (1) the exact growth rate `D₀(N)` in Maynard's S1
off-diagonal (e.g. `log log log N`?) and the precise inequality/Lemma number, and (2) that the
elementary per-prime `1/(p-1)` route above matches the standard treatment (vs needing the singular
series's exact Euler product). The PNT request below is fully MOOT.

## 2026-06-05 (lap 9) — REVISES the PNT request below: the real blocker is the off-diagonal S1 leg with a GROWING modulus `W`, not PNT

**Context update.** Lap 9 re-analysed the s1 correction `hcorr` (see `PENDING_WORK.md` lap-9 head).
The correction's bound (`S1Correction.yspace_correction_abs_bound_explicit`) splits into:
* a **diagonal leg** (count error `≤1`, no `M` factor) — now shown **PNT-FREE**: the y-space
  coefficient `ℓ¹`-mass is bounded by a fixed polynomial in the level `N` independent of the sieve
  scale `x` (`S1Correction.sum_abs_yLambda_le_level` / `diag_weight_yLambda_le_poly`), so taking `x`
  polynomially large in `N` (the main-term chain already permits any `x ≥ W·N+2`) kills it. No
  Möbius cancellation needed. The lap-8 PNT request below is therefore **moot for the diagonal leg.**
* an **off-diagonal leg** that scales with `M` (cancels vs the main term, so the scale trick is
  useless). Its size is `≈ ε(D₀)·main` with `ε(D₀) = ∑_{p>D₀}1/(p−1)²` — a fixed positive constant
  for **fixed** modulus `W = ∏_{p≤D₀}p`, hence `Θ(main)`, so `hcorr` is effectively **false for fixed
  `W`**. The classical fix is a **growing** `D₀ = D₀(N) → ∞` (so `W = W(N) → ∞`, `ε(D₀(N)) → 0`).

**What I now need (any of):**
1. In Maynard "Small gaps between primes" (and GPY), the S1 sum is computed with `W = ∏_{p≤D₀}p` and
   `D₀ → ∞` slowly. **Confirm the exact growth rate `D₀(N)` used** (e.g. `log log log N`?), how the
   off-diagonal/error term is bounded there (Lemma number + the inequality), and whether that bound is
   elementary (no PNT) given the W-coprimality. This tells me the target `W(N)` regime to re-state the
   y-space limit theorems against.
2. Is there an **existing Lean formalization** (PrimeNumberTheoremAnd, Kontorovich et al., any public
   repo) of the Maynard/GPY S1 *off-diagonal* error bound, or of the **per-prime singular-series mass
   bound** `∑_{d,e: p|[d,e]} |λ_d λ_e|/[d,e] ≤ (C/p)·∑_{d,e}|λλ|/[d,e]` for Selberg-type `λ`? Repo +
   theorem name.
3. Does current mathlib (master) have any **average/maximal order bound** usable here:
   `∑_{n≤N} σ(n)/φ(n) = O(N·polylog)`, `n/φ(n) = O(log log n)`, or `∑_{n≤N} 1/φ(n) = O(log N)`? (These
   would let me sharpen the crude `λ`-mass bound from `C·N³` toward the true `O(N·polylog)`, useful
   but NOT required for the diagonal leg.) Name the declaration(s).

**Why it unblocks:** (1)+(2) give the off-diagonal leg with growing `W` — the sole remaining
contour-free y-space s1 obligation after the diagonal leg (PNT-free) is wired.

---

## 2026-06-05 (lap 8, SUPERSEDED by the lap-9 note above) — The y-space smoothing residual (Möbius-mean / PNT-strength)

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
