# ON-LINE FINDINGS — PNT / Möbius-mean / Mertens availability (mathlib master vs PrimeNumberTheoremAnd)

Fulfils the **lap-11** request in `ON-LINE-REQUEST.md` (the smoothing-axiom / PNT-import question;
supersedes the moot lap-8/9/10 PNT asks). Companion to
`archive/findings/ON-LINE-FINDINGS-2026-06-04-gpy-diagonal-asymptotic.md` (Path Y vs Path D).

**Method.** Four host research passes, each reading **raw source** (not memory): mathlib4 `master`
at commit `7013b4ce…` (toolchain **v4.31.0-rc1**, 2026-06-05) and
`AlexKontorovich/PrimeNumberTheoremAnd` `main` at commit `58ad140e…` (2026-06-05). Every
declaration name + line below was read out of a fetched file. `sorry`-status was confirmed from
source. Where a thing is absent it was searched-for and is marked **NOT FOUND** with the search.

---

## TL;DR (the four answers)

1. **mathlib master has NOTHING PNT-strength.** No PNT, no Möbius mean, no Mertens asymptotic —
   **not even** the elementary `|∑_{n≤x} μ(n)/n| ≤ 1`. You get only the Chebyshev layer (ψ/θ defs +
   constant-factor bounds), `AbelSummation`, `vonMangoldt_sum`, `eulerMascheroniConstant`, and the
   *abstract* `SelbergSieve`. So **bumping your pinned mathlib alone buys you zero** of what you need.
2. **PrimeNumberTheoremAnd HAS the qualitative Möbius mean** (`mu_pnt_alt : ∑_{n≤x}μ(n)/n = o(1)`)
   and full PNT (`WeakPNT''`, `pi_alt'`, `MediumPNT`) — **but the `O(1/log)` RATE for the Möbius mean
   does NOT exist anywhere**, and there is **no μ/φ-weighted machinery at all**. It pins **Lean/mathlib
   v4.30.0** (you're on 4.29.1) → can't `require` without a mathlib bump; Apache-2.0 → porting is fine.
3. **Mertens 2nd (sum) is available** sorry-free in PNTAnd with the `O(1/log)` rate you want
   (`E₂p.bound`). **Mertens 3rd (the product `∏(1−1/p)~e^{−γ}/log x`) is *stated but `sorry`-blocked**
   (`E₃.bound''` rests on the open `E₃.abs_le`). mathlib master has neither (only `not_summable` +
   `eulerMascheroniConstant`).
4. **Elementary escape hatch — the majorant/large-sieve route is a DEAD END** (a majorant bounds
   `|λ|`, can't capture cancellation; your own lap-11 counterexample is the proof). **The ONE real
   PNT-free route is the polynomial-`F` telescoping** (`μ ∗ log = Λ`), and it now has a **sorry-free,
   PNT-free anchor**: `sum_mangoldt_div_eq_log` (`∑_{n≤x}Λ(n)/n = log x + O(1)`). If your
   `mk_eps_50_witness` `F` is a polynomial (Maynard's optimiser is), **this is the route that keeps you
   on v4.29.1 with no PNT.** Detailed below — read §4 before committing to importing PNT.

---

## 1. mathlib master (v4.31.0-rc1) — what's there, what's NOT

### PNT — **NO**
- No `Mathlib/NumberTheory/PrimeNumberTheorem*.lean`, no `ψ~x` / `θ~x` / `π~x/log x` anywhere.
- The strongest asymptotic in master is the **Chebyshev** bound, constant **log 4 ≈ 1.386, not 1**:
  `Chebyshev.eventually_primeCounting_le` — `∀ᶠ x, π⌊x⌋₊ ≤ (log 4 + ε)·x/log x`
  (`Mathlib/NumberTheory/Chebyshev.lean`). Docstring: "Chebyshev's upper bound." Not PNT.
- Present & usable (the scaffolding, all real): `Chebyshev.psi`, `Chebyshev.theta`,
  `Chebyshev.psi_le_const_mul_self` (ψ upper bound), `theta_le_log4_mul_x`, `psi_ge`/`theta_ge`,
  `psi_eq_log_lcmUpto`, `abs_psi_sub_theta_le_sqrt_mul_log`,
  `primeCounting_sub_theta_div_log_isBigO` (π−θ/log x = O(x/log²x)). All `Mathlib/NumberTheory/Chebyshev.lean`.

### Möbius mean — **NO** (not even the elementary bound)
- `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean` has only POINTWISE/algebraic facts:
  `abs_moebius_le_one` (`|μ n| ≤ 1` for a single `n`), Möbius inversion
  (`sum_eq_iff_sum_smul_moebius_eq` etc.), `moebius_mul_coe_zeta`, `isMultiplicative_moebius`.
- ❌ `|∑_{n≤x} μ(n)/n| ≤ 1` — **NOT in mathlib.** (It IS elementary — `∑_{n≤x}μ(n)⌊x/n⌋=1` — just
  not formalised here. PNTAnd has it: see §2.)
- ❌ `∑_{n≤x}μ(n)/n → 0`, ❌ `∑μ(n)=o(x)` (no `Mertens` declaration exists in master at all).

### Mertens 1/2/3 — **NO**
- The only `mertens` string in all of mathlib is a `-- TODO` about the unrelated *Dedekind–Mertens*
  polynomial lemma. `docs/1000.yaml` lists `Mertens's theorems` with **no `decl:`** (= unformalised).
- Mertens 2nd: only **divergence**, no rate — `not_summable_one_div_on_primes`,
  `Nat.Primes.not_summable_one_div`, `Nat.Primes.summable_rpow` (`Mathlib/NumberTheory/SumPrimeReciprocals.lean`).
- Mertens 3rd: absent. The constant exists in isolation: `Real.eulerMascheroniConstant`
  (`Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`) — not tied to any prime sum/product.

### `∑μ²/φ ~ log N` — **NO** (you already have your own `sharp_mertens_unconditional`)
- Not in master. `SelbergSieve.lean` is the **abstract** sieve only (`BoundingSieve`, `siftedSum`,
  `siftedSum_le_mainSum_errSum_of_upperMoebius`); it does not prove the concrete `μ²/φ` estimate.

### What master DOES give you to BUILD on — **YES, mature**
- `Mathlib/NumberTheory/AbelSummation.lean` — full partial-summation toolkit:
  `sum_mul_eq_sub_sub_integral_mul` (two-endpoint Abel), `sum_mul_eq_sub_integral_mul`,
  `…₀`/`…₁` (assume `c 0`/`c 1 = 0`), `tendsto_sum_mul_atTop_nhds_one_sub_integral`,
  `summable_mul_of_bigO_atTop`.
- `ArithmeticFunction/VonMangoldt.lean`: `vonMangoldt_sum` (`∑_{d|n}Λ(d)=log n`),
  `log_mul_moebius_eq_vonMangoldt` (`μ ∗ log = Λ`), `vonMangoldt_le_log`. **Note path change**:
  top-level `Mathlib/NumberTheory/VonMangoldt.lean` is now a `deprecated_module` stub → use the
  `ArithmeticFunction/` path.

> **Verdict on your Q1 (mathlib master):** nothing to import. The PNT/Mertens layer simply isn't
> upstreamed yet (only Chebyshev θ/ψ defs + bounds landed, via PRs #35573 and #38986, the latter
> co-authored by Tao). Bumping your mathlib pin does not unblock the smoothing axiom.

---

## 2. PrimeNumberTheoremAnd — exact decls, sorry-status, version

Repo `AlexKontorovich/PrimeNumberTheoremAnd`, `main`, **Apache-2.0**, last push 2026-06-05.
Statements are over **standard mathlib objects** (`open scoped Chebyshev` for ψ/θ,
`ArithmeticFunction.vonMangoldt`/`.moebius` for Λ/μ) — good for porting.

### PNT-strength (all in `Consequences.lean` / `MediumPNT.lean`)
| decl | file:line | statement |
|---|---|---|
| `WeakPNT''` | `Consequences.lean:105` | `ψ ~[atTop] (·)`  (ψ ~ x) |
| `chebyshev_asymptotic` | `Consequences.lean:177` | `θ ~[atTop] id` |
| `pi_alt'` | `Consequences.lean:901` | `π⌊x⌋₊ ~[atTop] x/log x` |
| `MediumPNT` | `MediumPNT.lean:3710` | `∃c>0, (ψ−id)=O(x·exp(−c(log x)^{1/10}))` — classical error term, **>> O(x/log x)** |

### Möbius mean — present but **only `o(1)`, no rate**
| decl | file:line | statement |
|---|---|---|
| `mu_pnt_alt` | `Consequences.lean:2403` | `(∑_{n<⌊x⌋₊} μ(n)/n) =o[atTop] 1`  ← **`∑μ(n)/n→0`, qualitative** |
| `mu_pnt` | `Consequences.lean:1955` | `(∑_{n<⌊x⌋₊} μ(n)) =o[atTop] x`  (`M(x)=o(x)`) |
| `sum_mobius_div_self_le` | `Consequences.lean:1590` | `|∑_{n∈range N} μ(n)/(n:ℚ)| ≤ 1`  ← **the elementary bound** |

⚠️ **There is NO `O(1/log)` rate for the Möbius mean.** `mu_pnt_alt` is plain `o(1)`. I grepped the
Möbius/Mertens files: the `O(1/log)` rate exists **only for Mertens SUM error terms** (§3), not for
`∑μ/n`. So the exact thing your smoothing axiom wants —
`|∑_{t≤T} μ(t) F(log(dt)/L)/φ(t)| ≤ C/L` (a μ/**φ**-weighted Möbius mean with an `O(1/L)` rate) —
**is not present in any form** here: no rate, and no μ/φ weighting at all (see §2-gap).

### μ/φ machinery — **NOT FOUND** (searched whole 83-file clone)
No `∑μ(n)/φ(n)`, no `∑μ(n)/φ(n)·(test fn)`, no `∑ n/φ(n)=O(x)`, no `∑1/φ(n)=O(log x)`. `totient`
co-occurs with Möbius nowhere. (`LSeries_totient_eq` is `∑φ(n)n^{−s}=ζ(s−1)/ζ(s)` — wrong shape.)

### Version / dependency verdict
- `lean-toolchain` = **`leanprover/lean4:v4.30.0`**; `lake-manifest.json` mathlib `inputRev v4.30.0`
  (rev `c5ea0035…`). **You're on v4.29.1.** mathlib pins are single-valued → you **cannot `require`
  PrimeNumberTheoremAnd while staying on mathlib 4.29.x**; importing it forces a 4.29→4.30 bump.
- It's a proper Lake lib (`[[lean_lib]] PrimeNumberTheoremAnd`) **but a heavy blueprint monolith**:
  83 files, root imports everything incl. an `IEANTN/` analytic subtree + **vendored mathlib patches**
  under `PrimeNumberTheoremAnd/Mathlib/…` + 4 extra deps (`LeanArchitect`, `checkdecls`, `leancert`,
  `PrimeCert`). **Recommendation: hand-port the one/two theorems you need** (Apache-2.0 permits it with
  attribution), targeting the standard `ψ/θ/Λ/μ` defs, rather than `require`-ing the package.

---

## 3. Mertens for the growing-`W` bookkeeping (your Q3)

All in `PrimeNumberTheoremAnd/IEANTN/Mertens.lean` (`namespace Mertens`).

| decl | line | statement | `sorry`? |
|---|---|---|---|
| `E₂p.bound` | 1047 | `∑_{p≤x}1/p = log log x + M + E₂p`, **`E₂p = O(1/log x)`** (Mertens 2nd, sum) | sorry-free |
| `E₂Λ.bound` | 827 | `∑Λ(d)/(d log d) = log log x + γ + E₂Λ`, `E₂Λ=O(1/log x)` | sorry-free |
| `prod_one_minus_div_prime_eq` | 1215 | `∏_{p≤x}(1−1/p) = e^{−γ}·exp(E₃ x)/log x` (exact identity) | **sorry-free** |
| `E₃.bound''` | 1259 | `∏_{p≤x}(1−1/p) ~ e^{−γ}/log x` (**Mertens 3rd asymptotic**) | ⚠️ rests on `E₃.abs_le` **sorry** (line 1240) |
| `E₃.bound'''` | 1272 | `∏(1−1/p) − e^{−γ}/log x = O(1/log²x)` | **sorry** (1273) |

Also a sharper Mertens-2nd-sum with explicit `O(1/log³x)` in `IEANTN/TMEEMT.lean:568`
(`|∑_{p≤x}1/p − loglog x − B| ≤ 4/log³x`).

**For your `φ(W)/W = ∏_{p≤D₀}(1−1/p) ≈ 1/log D₀`:** the *algebraic* product identity
`prod_one_minus_div_prime_eq` is sorry-free, but the **asymptotic** `∏(1−1/p)~e^{−γ}/log x` is
`sorry`-blocked (`E₃.abs_le`). So don't count on importing Mertens-3rd-asymptotic unconditionally.
**Better:** for a *fixed finite* `W=∏_{p≤D₀}p`, `φ(W)/W` is a finite product you can evaluate
directly; the size `≈1/log D₀` in `D₀` is exactly the Mertens-3rd asymptotic — derive it yourself
from the sorry-free `E₂p.bound` (`∑1/p`) + `log(1−1/p)=−1/p+O(1/p²)` + the convergent
`∑1/p²` (you already have the `∑_{p>D₀}1/p²` tail from lap 10), rather than waiting on `E₃.abs_le`.

For the size `𝒢_l = ∑_{(d,e)∈R²}(d/φd)(e/φe)/lcm(d,e)`: nothing library-ready; it's an Euler-product /
`μ²/φ`-ladder computation in your own machinery (`sharp_mertens_unconditional` + the 2-D ladder).

---

## 4. The elementary escape hatch (your Q4) — READ THIS BEFORE IMPORTING PNT

### (a) Majorant / large-sieve route: **DEAD END** (~90% confidence)
A large-sieve / Selberg majorant bounds `∑_{d,e}|λ_d λ_e|/[d,e]` **from above**. Your off-diagonal
`hcorr` is a **signed** quantity that must be `o(main)` — it needs **cancellation**. A majorant, by
construction, throws away sign and gives `O(main)`, never `o(main)`. **Your own lap-11 counterexample
is the theorem here:** for general nonneg `|λ|` the per-prime mass fraction can be `1`, not `1/p`, so
no `|λ|`-only bound exploiting W-coprimality can deliver the `o`. Stop pursuing this; it cannot close.

### (b) The polynomial-`F` telescoping: **the ONE real PNT-free route**, now with a sorry-free anchor
The cancellation you need lives in the *signed Möbius structure*. For a **polynomial** test function it
telescopes to (higher) von Mangoldt and closes on **Mertens-elementary** sums — **no contour, no PNT.**
This is the escape hatch flagged in the 2026-06-04 findings (§c, "the one elementary escape hatch"),
now made concrete by the research:

- `μ ∗ log = Λ` **exactly** (`log_mul_moebius_eq_vonMangoldt`, in mathlib master). So the degree-1 part
  of `∑_{d|n} μ(d)·(poly in log(R/d))` is a von-Mangoldt sum, and the relevant size is governed by
  **`∑_{n≤x} Λ(n)/n = log x + O(1)`**.
- **That sum is PROVEN, sorry-free, PNT-free, in PNTAnd:** `sum_mangoldt_div_eq_log`
  (`IEANTN/Mertens.lean:367`) — `x≥1 → |∑_{d≤x}Λ(d)/d − log x| ≤ log 4 + 4`. Its whole dependency
  chain (`E₁Λ.le` via `Chebyshev.psi_le_const_mul_self`, `E₁Λ.ge`, `sum_log_eq_sum_mangoldt`) is
  sorry-free and elementary. (Sister: `sum_mangoldt_div_eq_log' : ∑Λ(d)/d ~ log x`.)
- **It ports onto YOUR mathlib 4.29.1** with no PNT dep: it needs only `∑_{d|n}Λ=log n`
  (`vonMangoldt_sum`, you have it) + the **Chebyshev ψ UPPER bound** `psi_le_const_mul_self`. ⚠️ Verify
  your pinned 4.29.1 `Chebyshev.lean` carries `psi_le_const_mul_self` (the upper bound predates the
  May-2026 lower-bound PR, so it's very likely present); if not, the Chebyshev upper bound is itself
  elementary (`∑Λ⌊x/n⌋ = log⌊x⌋!`) and portable. Either way you stay on 4.29.1, PNT-free.

**Caveats — be honest with yourself here:**
1. **Check the witness is polynomial.** Maynard's `M_k` optimiser lives in the polynomial space, so
   `mk_eps_50_witness`'s `F` almost certainly is — but confirm it before betting the route on it.
2. **The μ/φ→μ/n reduction.** Your residual is μ/**φ**-weighted, not μ/n. Use
   `μ(t)/φ(t) = (μ(t)/t)·(t/φ(t))` with `t/φ(t)=∑_{a|t}μ²(a)/φ(a)` to peel the totient into the
   **positive** `μ²/φ` structure you already control (`sharp_mertens_unconditional`), leaving a
   **signed μ/n** core — which is exactly where the von-Mangoldt telescoping bites. This reduction is
   the load-bearing step to verify carefully; it's the y-space reindexing in disguise and is fully
   consistent with the committed **Path Y** (positive `μ²/φ`, constant `∫F²`, contour-free).
3. **Degree > 1 needs higher von Mangoldt `Λ_k = μ ∗ log^k`.** These are **NOT** in any library
   (NOT FOUND in mathlib or PNTAnd: no `Λ_2`/`generalizedVonMangoldt`, no Selberg symmetry formula),
   but their sums `∑Λ_k(n)/n` are **elementary** (Selberg's elementary method, induction, PNT-free).
   Building the `Λ_k` `/n`-asymptotics is real but bounded work, far below the PNT wall. The j=1
   anchor (`sum_mangoldt_div_eq_log`) is the template.

### (c) If you decline the polynomial route — then it IS PNT, and there's no free lunch
If `F` is non-polynomial (or the `Λ_k` build is judged too costly), the smoothing estimate is
genuinely PNT-strength and the **only** source is PrimeNumberTheoremAnd: port `MediumPNT` + the
Mertens-`O(1/log)` machinery and *derive* the μ/φ-weighted `O(1/L)` rate yourself (the μ/φ statement
isn't there ready-made — see §2-gap). That forces the mathlib 4.29→4.30 bump. There is **no** PNT,
Möbius-mean, or μ/φ shortcut in mathlib master to avoid this.

---

## Recommendation (priority order)

1. **Pursue the polynomial-`F` telescoping FIRST** (§4b). It is PNT-free, keeps you on v4.29.1, and
   has a sorry-free anchor to port (`sum_mangoldt_div_eq_log`). Step 0: confirm `mk_eps_50_witness`'s
   `F` is polynomial. Step 1: port/prove `∑Λ(n)/n = log x + O(1)`. Step 2: do the μ/φ→μ/n reduction
   (§4b-2). This is the highest-leverage path and stays inside the committed Path-Y frame.
2. **Do the growing-`W` size estimates elementarily** (§3): get `φ(W)/W ≈ 1/log D₀` from the sorry-free
   `E₂p`-style `∑1/p` + `∑1/p²` tail (you have it), **not** from the sorry-blocked Mertens-3rd product.
3. **Only if (1) is genuinely blocked**, port `MediumPNT` from PrimeNumberTheoremAnd and accept the
   mathlib 4.30 bump — and budget the extra work to derive the μ/φ-weighted `O(1/log)` rate, since no
   library states it. Treat the PNT smoothing as a 🔴 deep axiom (debt, not destination): keep it as a
   narrow cited axiom while you push the polynomial route, per the axiom-discharge doctrine.

This vindicates lap-4's `s1-derivative-landmine` verdict (the *signed* general-`F` route is PNT) while
showing the *polynomial-`F`* sub-case is **not** — which is the practically relevant case.

---

## Verified sources
- mathlib4 `master` @ `7013b4ce…` (v4.31.0-rc1): `Mathlib/NumberTheory/{Chebyshev, SumPrimeReciprocals,
  AbelSummation, SelbergSieve, PrimeCounting}.lean`, `ArithmeticFunction/{Moebius,VonMangoldt}.lean`,
  `Harmonic/EulerMascheroni.lean`, `Data/Nat/Totient.lean`, `docs/1000.yaml`. Upstream PRs #35573,
  #38986 (Chebyshev, latter co-auth Tao).
- `AlexKontorovich/PrimeNumberTheoremAnd` `main` @ `58ad140e…` (Lean/mathlib **v4.30.0**, Apache-2.0):
  `Consequences.lean` (WeakPNT''/pi_alt'/mu_pnt/mu_pnt_alt/sum_mobius_div_self_le), `MediumPNT.lean`,
  `IEANTN/Mertens.lean` (E₁Λ/E₂Λ/E₂p/E₃ + **`sum_mangoldt_div_eq_log:367`**), `IEANTN/TMEEMT.lean:568`,
  `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`, `LICENSE`.

— host, 2026-06-05

---

## ADDENDUM 2026-06-06 (host) — Step 0 CONFIRMED: the witness IS polynomial ✅

The §4b recommendation's gating precondition ("confirm `mk_eps_50_witness`'s `F` is
polynomial before betting the route on it") is now **verified from source**. The
PNT-free telescoping route is GREEN-LIT.

- `PolynomialSieveWeight k` (`BoundedGaps/SievePolynomial.lean:54`) is literally a
  finite `Finset (MultiIndex k × ℚ)`; `toFun t = ∑ c_α ∏ᵢ tᵢ^(αᵢ)` — a finite sum of
  monomials with rational coefficients (a polynomial by construction).
- The §6 witness is `symWeight R c` (`SymmetricReductionOrbitFree.lean:1024`), which
  **produces** a `PolynomialSieveWeight` — a symmetric polynomial, rational coeffs,
  monomial/orbit basis.
- Discharge chain: `mk_eps_50_witness_of_symWeight`
  (`SymmetricReductionEpsOrbitFree.lean:379`) → `mk_eps_50_witness_of_poly`
  (`EpsBridge.lean:539`) feeds exactly that polynomial. `mk_eps_50_witness` itself is
  still an axiom, but its discharge route is `native_decide`-ready over a polynomial `P`.

**Nuance (carry into the reduction):** the function entering the smooth class `MkSet`
is `Fapprox = χₙ · P` (smooth simplex cutoff × polynomial; `SievePolynomial.lean:162`,
ε-analog `FapproxEps` `EpsBridge.lean:201`), NOT the bare polynomial. But the cutoff is
only a limiting device — `χₙ → 1` on the simplex interior, `Mk ≥ MkF(P)` via DCT — so
`F` is **"polynomial on its support"** (a truncated polynomial; the `d ≤ R` support
restriction is intrinsic to the sieve anyway). That is precisely the standard Maynard
situation the `μ ∗ log = Λ` telescoping handles. ~90% confidence the cutoff does not
obstruct the route; the residual is the usual "check the boundary/support terms when
you do the μ/φ→μ/n reduction (§4b-2)."

Also re-verified live against GitHub this session: `sum_mangoldt_div_eq_log`
(the sorry-free PNT-free anchor, with the `log 4 + 4` bound) in
`PrimeNumberTheoremAnd/IEANTN/Mertens.lean`, and `log_mul_moebius_eq_vonMangoldt`
(`log * μ = Λ`) in mathlib `ArithmeticFunction/VonMangoldt.lean`. Both present.

— host, 2026-06-06
