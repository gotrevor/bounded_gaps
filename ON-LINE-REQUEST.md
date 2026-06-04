# Online research requests (bounded_gaps)

A networked host session fulfills these: commit an `ON-LINE-FINDINGS-<date>-<topic>.md`,
delete the answered item here, and remove this file once nothing is left open.

(The sharp-Mertens `∑μ²/φ ∼ log x` request was self-resolved on-box — `SharpMertens.
sharp_mertens_unconditional`, axiom-clean — and removed 2026-06-04.)

---

## 2026-06-04 — GPY/Maynard diagonal asymptotic `∑_{r sf}(φ(r)/r²) z_r²` (the GPY port)

> **Status (lap N+3, `path-a-selberg-nu`):** leaf 1's SMOOTH CORE is now CLOSED in-kernel —
> `InnerUniformReduction.weighted_riemann_2d` (the 2-D simplex weighted-Riemann limit
> `∑_m∑_{n≤R/m} F(log m/log R)G(log n/log R)/(mn)/(log R)² → ∫₀¹F·∫₀^{1-x}G`) is PROVEN
> unconditionally (axiom-clean, via a new Pólya theorem). The next frontier is the **GPY port**.

**What I need.** The precise GPY/Maynard statement + elementary proof of the asymptotic of the
DIAGONALISED Selberg quadratic form as `R → ∞`:

  `∑_{r ≤ R, r squarefree} (φ(r)/r²) · z_r²  ~  ?`,  where  `z_r = ∑_{s : (s,r)=1} μ(s) g(rs)/s`
  and the GPY/Maynard weight is `g(d) = F(log d / log R)` for a fixed smooth `F` supported on `[0,1]`.

Specifically: (a) the exact limiting constant (the `I(F) = ∫ F'(x)² dx` type integral and its
normalisation by powers of `log R`); (b) the singular series `𝔖` factor and how the
coprime-restricted Möbius sum `z_r` produces it; (c) the Möbius/hyperbola manipulation that rewrites
`∑_r (φ(r)/r²) z_r²` as a sum I can connect to the (now-proven) DOUBLE Riemann sum
`weighted_riemann_2d` addresses — ideally a Lean-friendly Dirichlet-convolution / sum-swap identity,
NOT a contour/Perron argument. Polymath8b §3 (eqns sfg-1, lflg) and Maynard "Small gaps between
primes" §5–6 are the likely sources; the exact intermediate identities are what I need.

**Why it unblocks me.** This is the ONLY remaining piece of leaf 1 (the s1 diagonal asymptotic)
now that `weighted_riemann_2d` is proven. With the precise identity I can either build it in-kernel
or hand a correctly-stated bounded lemma to Aristotle. Without the paper I risk an incorrect statement.
