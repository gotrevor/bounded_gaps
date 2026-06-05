# ON-LINE FINDINGS — GPY/Maynard diagonal asymptotic of `∑_r (φ(r)/r²) z_r²`

> ## ✅ DECISION (Trevor, 2026-06-04): **Path Y + antiderivative convention — SETTLED.**
> The s1/s2 discharge commits to **Path Y** (y_r-space, positive `μ²/φ`, contour-free) with the
> **antiderivative convention**: feed `lambdaTransform`/`selberg_nu` the antiderivative `𝔉` of the
> variational `F` (`𝔉' = F`), keeping the s1 constant `∫F²` and the entire `M_k`/witness layer
> (incl. `mk_eps_50_witness`, `narrowness_*`) **UNTOUCHED**.
> - ❌ Do NOT restate the constant as `∫(F')²` (Option B — would re-key the near-done witness thread).
> - ❌ Do NOT take Path D / evaluate the signed `z_r` (imports a PNT-strength axiom `∑μ(s)/s→0`,
>   which works *against* the "rely only on BV" goal).
> - ✅ Build order: (1) antiderivative operator at the sieve-weight boundary + the FTC bridge
>   `∫₀¹ 𝔉'(x)² dx = ∫₀¹ F(x)² dx`; (2) the `μ²/φ` k-D ladder (mirror of the bare ladder, using
>   `perturbed_riemann_muphi`); (3) compose with Maynard `S1Summation2` / the `gpy_diagonal_asymptotic_form`
>   algebraic bridge to land `s1` (then `s2` as its sister). Reuses the already-axiom-clean
>   `sharp_mertens_unconditional` + `riemann_sum_log_weight` + `weighted_riemann_2d_of_inner`.
> Rationale + trade-offs: this doc's §(c) (Path Y vs D) + the LANDMINE section below. The bare k-D
> ladder + the `μ²/φ` engine that already landed are Path-Y machinery, not wasted. KB: `[[s1-derivative-landmine]]`, decisions.md.

Fulfils the 2026-06-04 request in `ON-LINE-REQUEST.md` (the "GPY port", leaf 1's last
piece). Sources read directly from `papers/src/` (LaTeX, not the web): Polymath8b
(`polymath8b-1407.4897/newergap-submitted.tex`), Maynard "Small gaps between primes"
(`maynard-1311.4600/Small_gaps_between_primes.tex`), Soundararajan's GPY survey
(`soundararajan-math-0605696/main.tex`). Equation labels below are the paper's own.

---

## TL;DR (the precise statement you asked for)

For the **pure arithmetic quadratic form** your `gpy_diagonal_asymptotic_form` isolates —
`g(d) = F(log d / log R)`, `F` smooth, supported in `[0,1]` so `F(1)=0`:

```
∑_{d,e ≤ R, sf}  μ(d)μ(e)/[d,e] · F(log d/log R) F(log e/log R)
   =  ∑_{r ≤ R, sf}  (φ(r)/r²) · z_r²                         (your proven identity)
   ~  (1/log R) · ∫₀¹ F'(x)² dx          as R → ∞.            (★)
```

- **The constant is `∫₀¹ F'(x)² dx` — a DERIVATIVE, exactly as you anticipated.** Power of
  `log R` is **−1** (one over `log R`). Singular series for the bare single-linear-form model
  is **𝔖 = 1** (the `W`-trick contributes `W/φ(W)`, which is absorbed into the normalisation
  `B = φ(W)/W · log x`; see §b).
- This is **Polymath8b Theorem `nonprime-asym`, eqn `lflg` + `c-def`**, specialised to `k=1`,
  `F = G`. Their `λ_F(n) := ∑_{d|n} μ(d) F(log d / log x)` (eqn `lambdaf-def`) **is your
  `lambdaTransform` verbatim**, and `nuform` is your `selberg_nu`.

```
Polymath8b lflg  (k-dim, the s1 / non-prime sum):
  ∑_{x≤n≤2x, n≡b(W)}  ∏_{i=1}^k λ_{F_i}(n+h_i) λ_{G_i}(n+h_i)  =  (c + o(1)) B^{-k} · x/W
  c := ∏_{i=1}^k ( ∫₀¹ F'_i(t) G'_i(t) dt )          ← "F' denotes the derivative of F" (their words)
  B := φ(W)/W · log x
```

For **one coordinate, diagonal** (`k=1`, `F=G`, drop the tuple): main term `(c+o(1))·B⁻¹·x/W`
with `c = ∫₀¹ F'(t)² dt`. Stripping the `n`-average and the `W`-trick leaves exactly (★).

---

## ⚠️ LANDMINE — verify this before you state anything (this is the "incorrect statement" risk)

Your **`s1_holds_from_nonprime_asym`** axiom (Sieve.lean ~2503) claims
`α = I(F) = ∫_{simplex} F²` — **no derivative**. But `selberg_nu` is built from
`lambdaTransform` = Polymath8b `λ_F`, whose non-prime constant (`c-def`) is
`∏ ∫ F'_i G'_i` — **with derivatives**. These are reconcilable **only** via a change of
function:

> **Maynard's final remark (§6, end):** *"Our function `F` corresponds to `f` differentiated
> with respect to each coordinate."*

i.e. the **variational** `F` (the one with `I(F)=∫F²`, `J_i(F)`, `M_k`) is the **derivative**
of the **sieve-weight** function fed to `λ`. Equivalently, if you feed `λ`/`selberg_nu` the
function `𝔉`, then `∫₀¹ 𝔉'(t)² dt = ∫₀¹ F(t)² dt` where `F = ±𝔉'` is the variational function.

**Action:** check what `selberg_nu k J c Fs H R` receives in `Fs` versus what `mkF_denominator
k F`/`I(F)` receives. If the **same symbol** is passed to both, the axiom is **off by a
derivative and false as stated**. Two fixes:
1. Feed `lambdaTransform` the **antiderivative** of the variational `F` (the GPY weight is
   `μ(d)·𝔉(log d/log R)` with `𝔉' = F`), keeping `I(F)=∫F²`; or
2. Keep feeding `F` to `λ` and **restate** the constant as `∫(F')²` (= `∫(∂₁…∂_k F)²` in
   `k`-dim). Maynard's `I_k`/`J_k` machinery would then be in `𝔉`-space, not `F`-space.

Cross-checks that this derivative is real, not a typo: Polymath8b states it **three times** —
`c-def`, the probabilistic remark (`mean (∫₀¹ F'_j G'_j + o(1))·B⁻¹`), and the parenthetical
"Here of course `F'` denotes the derivative of `F`." Soundararajan eqn (9) has `P^{(k)}` (the
`k`-th derivative). Maynard's whole `y_r`-space exists precisely to *move* the derivative onto
the test function so the integral becomes `∫F²`.

---

## (a) Exact constant + power of `log R`

(★): `∑_{d,e} μ(d)μ(e)/[d,e] · F(·)F(·) ~ (1/log R) ∫₀¹ F'(x)² dx`.

Two independent derivations, both giving the same `1/log R · ∫ F'²`:

**(a1) From Soundararajan eqn (9)** (GPY survey, denominator of the ratio). With
`λ_d = μ(d) P(log(R/d)/log R)`, `P` vanishing to order `k` at `0`:
```
∑_n (∑_{d|P(n)} λ_d)²  ~  x/(log R)^k · 𝔖(H) · ∫₀¹ (y^{k-1}/(k-1)!) P^{(k)}(1-y)² dy.
```
At `k=1`, single form, `𝔖=1`: `~ (x/log R) ∫₀¹ P'(1-y)² dy = (x/log R) ∫₀¹ P'(u)² du`. The
arithmetic form drops the `x` density: `∑_{d,e} μ(d)μ(e)/[d,e] P(·)P(·) ~ (1/log R)∫₀¹P'²`.
Setting `F(t) := P(1−t)` (so `F(log d/log R) = P(log(R/d)/log R)`) gives `∫P'² = ∫F'²`, and
"`P` vanishes to order 1 at 0" becomes "`F(1)=0`". ⟹ (★). ∎

**(a2) Directly from your `z_r` form** (the mechanism, see §b for the one PNT-strength step):
```
z_r ~ (r/φ(r)) · ( −F'(log r/log R) ) / log R                      ... (†) [PNT-strength]
(φ(r)/r²) z_r²  ~  (φ(r)/r²)(r²/φ(r)²) F'(·)²/(log R)²  =  (μ²(r)/φ(r)) · F'(·)²/(log R)²
∑_{r≤R} (μ²(r)/φ(r)) F'(log r/log R)²  ~  log R · ∫₀¹ F'(x)² dx    [sharp Mertens, 𝔖=1]
  ⟹  ∑_r (φ(r)/r²) z_r²  ~  log R·∫F'² / (log R)²  =  (1/log R)∫₀¹ F'(x)² dx.            ∎
```
The `r/φ(r)` in (†) cancels the leading part of `φ(r)/r²` to leave `μ²(r)/φ(r)`, whose smooth
sum has **logarithmic density 1** — which is exactly your axiom-clean
`SharpMertens.sharp_mertens_unconditional` (`(∑_{n≤N} μ²/φ)/log N → 1`).

**With the `W`-trick / `n`-average** (the form your sieve actually uses): main term
`(∫F'² + o(1)) · B⁻¹ · x/W = (∫F'² + o(1)) · x/(φ(W) log x)`, with `B = φ(W)/W·log x`.

Required hypotheses (Polymath8b `nonprime-asym` case (i), "trivial case"): `F,G` smooth
compactly supported, `S(F)+S(G) < 1` (supports sum below 1 — the `k=1` simplex condition; this
is the **unconditional** case, needs no EH). `F(1)=0` follows from support in `[0,1]`.

---

## (b) The singular series 𝔖 and how `z_r` produces it

**For your bare `k=1` single-form model, 𝔖 = 1** (one linear form ⟹ `ν(p)=1` residue killed
per prime; `𝔖 = ∏_p (1−1/p)(1−1/p)⁻¹ = 1`). The `W`-trick's `W/φ(W)` factor is bookkeeping,
folded into `B`. So you do **not** owe a nontrivial singular series at leaf-1's smooth core —
good news.

**General `k`-tuple** (for orientation): `𝔖(H) = ∏_p (1 − ν_H(p)/p)(1−1/p)^{−k}`, `ν_H(p) =
#{distinct h_i mod p}`. It enters from the **local lattice-point densities** (the count of
`n∈[x,2x]` with `[d_i,e_i] | n+h_i` is `~ x/∏[d_i,e_i] · ∏_p(local factor)`), and the `∏_p`
of local factors is `𝔖`.

**Mechanism in the diagonal `z_r` form** — the workhorse is **Maynard Lemma `PartialSummation`
(= GGPY Lemma 4)**, the elementary (no-contour) Mertens-type asymptotic:
```
∑_{d<z} μ²(d) g(d) G(log d / log z)  =  𝔖 · log z · ∫₀¹ G(x) dx  +  O(𝔖 L G_max),
  g totally-mult, g(p) = γ(p)/(p−γ(p)),   𝔖 = ∏_p (1 − γ(p)/p)⁻¹ (1 − 1/p).
```
The multiplicative coefficient (`φ(r)/r²` for s1, `φ(r)²/(g(r)r²)` for s2) has an Euler
product = (density part giving the `log z`) × (convergent fluctuation `∏_p(1+O(1/p²))` = the
local 𝔖 factors). `z_r` "produces" 𝔖 because (†) replaces `z_r` by `(r/φ(r))·(−F'/log R)`, and
`r/φ(r) = ∏_{p|r}(1−1/p)⁻¹` is precisely the per-prime factor whose product over the support is
resummed into 𝔖 by `PartialSummation`. For `k=1`/`γ(p)=1` this telescopes to `𝔖=1`, i.e. your
`sharp_mertens_unconditional`.

---

## (c) The Möbius/hyperbola route — elementary vs contour, and where `weighted_riemann_2d` fits

**First, an honest warning about the two papers you named:**

- **Polymath8b §`sieving-sec` (Lemma `mul-asym`) is a CONTOUR proof** — it goes through
  `ζ_{WN}(1 + (1+iξ)/log x)` and a Fourier kernel `K(ξ₁,…)` (lines ~1138–1153). That is the
  Mellin/Perron machinery you explicitly want to avoid. **Do not port Polymath8b's proof.** Use
  it only for the *statement* (`lflg`/`c-def`).
- **Maynard §5–6 IS the elementary route.** Three moves, no contour:
  1. **Hyperbola/totient decoupling** (Maynard §5, proof of `S1Expression1`):
     `1/[d,e] = (1/de) ∑_{u | (d,e)} φ(u)` (since `∑_{u|n} φ(u)=n`). This splits the `d`–`e`
     dependence — it's the same identity your `gpy_diagonal_asymptotic_form` already uses to
     reach `∑_r (φ(r)/r²) z_r²`.
  2. **Change of variables** `y_r` (`eq:YLambdaDef`) diagonalises (you have the analogue).
  3. **Close with `PartialSummation`** (§b) — a **positive** `μ²·g`-weighted Mertens sum → an
     integral. No `1/ζ`, no contour.

**The catch, stated plainly:** Maynard's elementary route lives in the **`y_r`-space**, where
the sums are **positive** (`μ²(r)/φ(r)`) and the constant is **`∫F²`**. Your literal
`∑_r (φ(r)/r²) z_r²` lives in the **`d`-space**, and its `∫F'²` constant hides the **signed**
inner sum `z_r`. Step (†) — `∑_{(s,r)=1} μ(s)/s · F(log rs/log R) ~ (r/φ(r))(−F'/log R)` — is
**PNT-strength** for a general smooth `F` (it is the `1/ζ(1+w) ~ (w−1)` behaviour). There is no
contour-free, Mertens-only evaluation of the *signed* `z_r` for arbitrary smooth `F`; the
contour in Polymath8b is exactly packaging PNT. (The one elementary escape hatch: for
**polynomial** `F`, `∑_{d|n} μ(d) log^j(R/d)` telescopes via `μ ∗ log = Λ` and closes on
`∑_n Λ(n)/n ~ log` — Mertens, not PNT. That only covers polynomial weights.)

**So how does your `weighted_riemann_2d` actually help?** It is the right mechanisation of the
**positive** side (`PartialSummation` / the `y_r`-space iterated integral), **not** of the
signed `z_r`. Two concrete paths:

- **Path Y (recommended — contour-free, uses lemmas you already have).** Re-target leaf 1 to
  the **`y_r`-space** Maynard statement: the s1 main term is
  `∑_{r≤R, (r,W)=1} (μ²(r)/φ(r)) · F(log r/log R)² ~ (φ(W)/W) log R · ∫₀¹ F² ` (`PartialSummation`
  with `γ(p)=1_{p∤W}`). Your `SharpMertens.sharp_mertens_unconditional` **is** the `𝔖=1` core of
  this (`∑μ²/φ /log → 1`); compose it with `riemann_sum_log_weight` (smooth-weight version,
  weight `1/n`, `→ ∫₀¹F`) the same way `WeightedMertens` already bootstraps. The 2-D
  `weighted_riemann_2d_of_inner` is then exactly the `S₂`/marginal piece
  `J_k^{(m)} = ∫(∫F dt_m)²` — the `∫₀^{1−x}` inner simplex integral it returns is the
  marginal `∫₀¹ F(…,t_m,…) dt_m` restricted by the simplex. **In this space there is no `z_r`
  and no PNT** — and it forces you to resolve the landmine in the right direction (variational
  `F`, constant `∫F²`).
- **Path D (keep `z_r`, owe a PNT-strength lemma).** If you insist on the `d`-space `∫F'²`,
  you must add an input of the form `∑_{s≤y, (s,r)=1} μ(s)/s → 0` (uniformly enough), which is
  **not** in the repo and is genuinely PNT-hard. Then `sharp_mertens_unconditional` closes the
  outer sum and you land on `∫F'²`. Aristotle-bait only if you accept a PNT-level prerequisite
  as an axiom.

**Recommendation:** take **Path Y**. It is contour-free, reuses `sharp_mertens_unconditional`
(already axiom-clean) + `riemann_sum_log_weight` + `weighted_riemann_2d_of_inner`, gives the
`∫F²` your `s1` axiom already advertises, and dodges the `z_r`/PNT wall entirely. The
`gpy_diagonal_asymptotic_form` `z_r` identity stays useful as the *algebraic* bridge, but the
**asymptotic** should be taken in `y_r`-space, not by evaluating `z_r²` directly.

---

## Exact references (so you can verify, not trust me)

| Fact | Source (in `papers/src/`) | Label / line |
|---|---|---|
| `λ_F(n)=∑_{d\|n}μ(d)F(log d/log x)` (= your `lambdaTransform`) | polymath8b | `lambdaf-def` |
| `ν` form (= your `selberg_nu`) | polymath8b | `nuform` |
| s1 / non-prime asymptotic, `c=∏∫F'_iG'_i`, `B=φ(W)/W·log x` | polymath8b | Thm `nonprime-asym`, `lflg`, `c-def`, `bnorm` |
| "`F'` denotes the derivative of `F`" + mean `∫F'_jG'_j·B⁻¹` | polymath8b | after `c-def`; remark |
| their proof IS contour (`ζ_{WN}`, Fourier `K`) — avoid | polymath8b | §`sieving-sec` |
| hyperbola identity `1/[d,e]=(1/de)∑_{u\|(d,e)}φ(u)` | maynard | §5, proof of `S1Expression1` |
| `y_r` change of variables | maynard | `eq:YLambdaDef`, `eq:LambdaYDef` |
| elementary Mertens workhorse (= GGPY Lemma 4) | maynard | Lemma `PartialSummation` |
| s1 → `I_k(F)=∫F²` in `y_r`-space | maynard | Lemma `S1Summation2` |
| **variational `F` = sieve weight `f` differentiated** | maynard | final remark of §6 |
| `k=1` ⟹ `∫P'(1−y)²` = `∫F'²` | soundararajan | eqn (9), (15) |

In-repo lemmas to compose (Path Y): `SieveExpansion.gpy_diagonal_asymptotic_form` (algebra),
`SharpMertens.sharp_mertens_unconditional` (`∑μ²/φ /log→1`), `WeightedMertens.riemann_sum_log_weight`
(`1/n`-weight → `∫₀¹F`), `WeightedRiemann2D.weighted_riemann_2d_of_inner` (2-D simplex),
`PolyaUniform.polya_uniform` (monotone → uniform, already used for the inner-uniform reduction).

— host, 2026-06-04
