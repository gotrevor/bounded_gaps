# Papers 📚

Local copies of the bounded-gaps literature. PDFs + arXiv LaTeX source where available. Gitignored — fetch via `download.sh` or one-off curls.

The literature uses **$H_m \coloneqq \liminf_{n \to \infty} (p_{n+m} - p_n)$** as the standard quantity. Our Lean `BoundedGap H` predicate is the set-infinite version; equivalent, but the literature's `H_m` notation is the one you'll see when reading these papers.

## The chain

```
GPY (2009) ──► Zhang (2014) ──┐
   │                          ├─► H_1 finite
   └──► Maynard (2014) ───────┘   ↓
              │                  Polymath8b (2014) ──► H_1 ≤ 246
              │                          │
              ├──► Granville (2015) ◄────┘  (survey)
              ▼
         H_1 ≤ 600 (unconditional)
         H_1 ≤ 12  (under EH)
```

## Catalog

| Paper | Year | arXiv | PDF | LaTeX source | Role |
|-------|------|-------|-----|--------------|------|
| **Zhang**, "Bounded gaps between primes" (Annals) | 2014 | — (Annals only) | [pdf/zhang-2014-bounded-gaps.pdf](pdf/zhang-2014-bounded-gaps.pdf) | not available | The breakthrough. $H_1 \le 7 \times 10^7$. Introduces the MPZ distributional estimate. |
| **Maynard**, "Small gaps between primes" (Annals) | 2014/15 | [1311.4600](https://arxiv.org/abs/1311.4600) | [pdf/maynard-2015-small-gaps.pdf](pdf/maynard-2015-small-gaps.pdf) | [src/maynard-1311.4600/](src/maynard-1311.4600/) (`Small_gaps_between_primes.tex`) | The multidimensional sieve. $H_1 \le 600$ unconditional; $H_m < \infty$ for all $m$; $H_1 \le 12$ under EH. Stays inside Bombieri-Vinogradov — no MPZ needed. **Recommended formalization on-ramp.** |
| **Polymath8b** (Tao, Maynard, et al.), "Variants of the Selberg sieve…" | 2014 | [1407.4897](https://arxiv.org/abs/1407.4897) | [pdf/polymath8b-2014-variants.pdf](pdf/polymath8b-2014-variants.pdf) | [src/polymath8b-1407.4897/](src/polymath8b-1407.4897/) (`newergap-submitted.tex`) | The 246 paper. $H_1 \le 246$ unconditional; $H_1 \le 6$ under **generalized** EH (not plain EH); explicit `H(50) = 246` admissible 50-tuple. |
| **Granville**, "Primes in intervals of bounded length" (BAMS) | 2015 | [1410.8400](https://arxiv.org/abs/1410.8400) | [pdf/granville-2015-survey.pdf](pdf/granville-2015-survey.pdf) | [src/granville-1410.8400/](src/granville-1410.8400/) (`main.tex`) | **Survey**. Post-Zhang/Maynard, expository. Best entry point if you haven't read the literature before. |
| **Goldston-Pintz-Yıldırım**, "Primes in Tuples I" (Annals) | 2009 | [math/0508185](https://arxiv.org/abs/math/0508185) | [pdf/gpy-2009-primes-in-tuples-I.pdf](pdf/gpy-2009-primes-in-tuples-I.pdf) | [src/gpy-math-0508185/](src/gpy-math-0508185/) (`main.tex`) | The precursor. $\liminf (p_{n+1}-p_n)/\log p_n = 0$. Introduces the sieve that Maynard later generalizes. Conditional bound $H_1 \le 16$ under EH. |
| **Polymath8a** (Tao, Castryck, Fouvry, Harcos, et al.), "New equidistribution estimates of Zhang type" | 2014 | [1402.0811](https://arxiv.org/abs/1402.0811) | [pdf/polymath8a-2014-zhang-type-equidistribution.pdf](pdf/polymath8a-2014-zhang-type-equidistribution.pdf) | [src/polymath8a-1402.0811/](src/polymath8a-1402.0811/) (`main.tex`) | The intermediate step: Zhang's 70M → 4680. Establishes $\MPZ[\varpi,\delta]$ for $600\varpi + 180\delta < 7$. Critical prereq for Polymath8b bounds (ii)-(vi). |
| **Pintz**, "Polignac Numbers, Conjectures of Erdős…" | 2013 | [1305.6289](https://arxiv.org/abs/1305.6289) | [pdf/pintz-2013-polignac-post-zhang.pdf](pdf/pintz-2013-polignac-post-zhang.pdf) | [src/pintz-1305.6289/](src/pintz-1305.6289/) (`main.tex`) | Immediate post-Zhang response: arithmetic progressions of bounded-gap prime pairs, density of Polignac numbers. Many "would have been science fiction a year ago" corollaries. |
| **Maynard**, "Dense clusters of primes in subsets" | 2016 | [1405.2593](https://arxiv.org/abs/1405.2593) | [pdf/maynard-2016-dense-clusters.pdf](pdf/maynard-2016-dense-clusters.pdf) | [src/maynard-1405.2593/](src/maynard-1405.2593/) (`Subsets.tex`) | Maynard sieve applied to subsets — refined bounds for primes in restricted sets, e.g. arithmetic progressions. The "sieve as Swiss-army knife" demonstration. |
| **Banks-Freiberg-Maynard**, "On limit points of the sequence of normalized prime gaps" | 2016 | [1404.5094](https://arxiv.org/abs/1404.5094) | [pdf/banks-freiberg-maynard-2016-limit-points.pdf](pdf/banks-freiberg-maynard-2016-limit-points.pdf) | [src/bfm-1404.5094/](src/bfm-1404.5094/) (`banks-freiberg-maynard-…tex`) | Shows the set of limit points of normalized prime gaps has positive Lebesgue measure. Another Maynard-sieve corollary. |
| **Maynard**, "Primes with restricted digits" | 2019 | [1604.01041](https://arxiv.org/abs/1604.01041) | [pdf/maynard-2019-restricted-digits.pdf](pdf/maynard-2019-restricted-digits.pdf) | [src/maynard-1604.01041/](src/maynard-1604.01041/) | Different problem (digit restrictions), same sieve technology. Cited here as evidence the Maynard sieve has applications well beyond bounded gaps. |
| **Soundararajan**, "Small gaps between prime numbers: the work of Goldston-Pintz-Yıldırım" (BAMS) | 2007 | [math/0605696](https://arxiv.org/abs/math/0605696) | [pdf/soundararajan-2007-gpy-survey.pdf](pdf/soundararajan-2007-gpy-survey.pdf) | [src/soundararajan-math-0605696/](src/soundararajan-math-0605696/) (`main.tex`) | Pre-Zhang/Maynard expository survey of the GPY method. Shorter and more focused than Granville. |

## How to use these when formalizing

- **Statement-hunting**: grep the LaTeX. `grep -A 10 "begin{theorem}" src/polymath8b-1407.4897/newergap-submitted.tex` gives you every theorem with its statement, ready to translate.
- **Definition-hunting**: search for `coloneqq` / `:=` / `\\newcommand`. The literature notation (`H_m`, `H(k)`, `EH[\vartheta]`, `MPZ[\varpi,\delta]`) is reasonably consistent across these papers.
- **Conjecture references**: when a theorem says "assume EH" or "assume GEH", grep `\\EH\b` / `\\GEH\b` in the source to find the exact formal claim.

## Resolved on the 2026-05-24 deep read

All three of the previously-listed discrepancies have been addressed:

- ✅ `Polymath8b.H1_le_6_under_GEH` now takes `GEH`, not `EH`. `Prerequisites.lean` has parameterized `EH ϑ`, `GEH ϑ`, `MPZ ϖ δ`.
- ✅ `Maynard.H2_le_600_under_EH` added.
- ✅ `Basic.liminfGap m : ℕ∞` defined with the literature $\liminf$ semantics; downstream theorems use it.

## What's still missing

- **Zhang's LaTeX source** — not on arXiv, Annals doesn't publish source. PDF is the best we can do.
- **Tao's blog series** on Zhang/Maynard/Polymath8 — easier-than-papers exposition at terrytao.wordpress.com, not collected as PDFs anywhere.
- **Friedlander-Iwaniec** (a^2 + b^4 primes, cited in Polymath8b §7) — only relevant if pursuing the parity-barrier discussion in detail.
- **Pintz post-Zhang followups** beyond 1305.6289 — there's a small flurry of Pintz papers in 2013-14, not all critical for the 246 path.
