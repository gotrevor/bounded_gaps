# Symmetric-function reduction for `polynomialMkF` — scoping verdict

**Date** 2026-05-31 · prototype: `tools/mk/mk_sym.py` (closed form) validated against
`tools/mk/mk5_sym.py` (brute monomial reduction).

## The question
Can we extend the M_5 explicit-witness discharge (`Mk5Witness.lean`) to the larger
`Mk k` targets, by computing the Rayleigh quotient of a *symmetric* polynomial test
function from its ~O(#partitions) orbit coefficients with closed forms in `k`, instead
of enumerating O(#monomials) terms (which explodes: ~177M monomials at k=54 deg 7)?

## Answer: the math works, validated. The closed form is real.

For partitions `lam, mu` (the orbit basis), place their labelled parts into distinct
slots of `Fin k`. The integrand depends only on the **overlap pattern** = a partial
matching `M` pairing some lam-parts with some mu-parts (same slot). With
`T = r_lam + r_mu - |M|` occupied slots:

```
  Mr[lam][mu](k) = (1/aut) * Σ_M ff(k,T)·W(M)              / (k+|lam|+|mu|)!     (denominator)
  Ar[lam][mu](k) = (1/aut) * Σ_M ff(k,T)·W(M)·(Gocc(M)+(k-T)·2) / (k+|lam|+|mu|+1)!  (numerator)
```
- `aut = aut(lam)·aut(mu)`, `aut(λ) = Π_v (mult_v)!`
- `ff(k,T) = k(k-1)···(k-T+1)` — falling factorial; a **polynomial in k** (this is the key)
- `W(M) = Π_{paired (a,b)} (a+b)! · Π_{lam-only a} a! · Π_{mu-only b} b!`
- `g(a,b) = (a+b+2)!/((a+1)(b+1)(a+b)!)`, `Gocc(M) = Σ_{occupied tokens} g(·)`, `g(0,0)=2`

**Validation**: `python3 mk_sym.py validate` → closed form == brute monomial oracle
*exactly* for all k=2..9 at degrees 2 and 3. The denominator-factor `(k+c)!` is constant
across each orbit pair (numerator: `(k-1)+|rem|+β = k+|lam|+|mu|+1`, also constant — clean).

## The numbers (sup of M_k over degree-≤D symmetric polynomials) — EXACT

⚠️ **All values below are from EXACT rational LDL-inertia, not float.** A float
generalized-Rayleigh power iteration is *worthless* here: the orbit basis spans ~10^89
in L²-norm at k=50 (factorial scaling), so float linear algebra silently corrupts. A
first pass reported a bogus "deg7 sup ≈ 4.36"; exact arithmetic shows deg7 is < 4. Trust
only `inertia(A − cM)` (sign of exact pivots, Sylvester's law).

| deg D | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|-------|---|---|---|---|---|---|---|---|
| #orbits | 2 | 4 | 7 | 12 | 19 | 30 | 45 | 67 |
| exact M_50 sup | 2.83 | 3.14 | 3.33 | 3.45 | 3.55 | <4 | <4 | <4 |

`#orbits = Σ_{j≤D} p(j)`. Increments **decay** (+0.31, +0.20, +0.12, +0.10, …): the
truncation creeps toward the true `M_50`, which Polymath8b established sits *just* above 4
(this is exactly why they needed k=50 specifically). So:

- **Degree 8 (67 orbits) does NOT clear 4** — exact `inertia(A−4M) = (+0, −67, 0)`, i.e.
  `A − 4M` is negative definite, at BOTH **k=50 and k=54** (verified 2026-06-01, exact LDL).
  Degree 7 (45 orbits) likewise negative-definite at both k.
- The crossing degree is therefore **≥ 9** (was only known `≥ 8` before), and because the true
  value is so close to 4, likely well into the teens. No clean low-degree witness exists in
  this regime. (Degree ≥ 9 is the `matchings(r,r)` enumeration wall for `mk_sym.py` as written:
  the all-ones partition `1⁹` alone costs `9!` matchings per matrix entry — a smarter
  overlap-count would be needed to push the exact table further.)

## What it would actually discharge — IMPORTANT caveat

The `mk_*` axioms split in two:

1. **Unconditional flagship (246)** routes through `mk_eps_50_witness` → `Sieve.Mk_eps 50`
   (the ε-trick / enlarged-simplex functional). **No polynomial bridge exists for `Mk_eps`**
   — `Mk_ge_polynomialMkF` is plain-`Mk` only. This reduction does **NOT** touch it.
   (`Targets.H1_le_246` is already a *conditional* theorem taking `Mk 50 > 4` as hypothesis.)

2. **EH-conditional plain-`Mk` ladder** — the vein this unlocks:
   - `mk_54_witness_under_EH`  : `Mk 54 > 4`   (degree ~7, 45 orbits)  ← first rung
   - `mk_5511_witness_under_EH`: `Mk 5511 > 6` (higher degree — M_k~log k, log 5511≈8.6)
   - `mk_41588_witness_under_EH`: `Mk 41588 > 8`
   - `mk_309661_witness_under_EH`: `Mk 309661 > 10`

   Same EH-conditional vein as the already-done `mk_5_witness_under_EH` (M_5 > 2).
   The identity is parametric in k, so k=5511 etc. are "free" once proven — **but the
   truncation degree (hence orbit count) grows per rung**, so each higher rung needs a
   bigger witness. And per the exact table above, even the FIRST rung (M_54 > 4) needs a
   high-degree witness (≥ 8, likely teens) because the true M_54 is only marginally > 4.

## The real Lean cost (why it's multi-session, not `native_decide`)

You **cannot materialize** the witness's monomial `Finset` (e.g. orbit `(1⁷)` alone is
C(54,7) ≈ 177M monomials, and the required degree is higher still).
So `polynomialMkF` (the `Finset` double-sum) is uncomputable for the witness, and
`native_decide` on the explicit form is hopeless — *the same wall as the monomial method*.

The proof must operate at **orbit level, parametric in k**:
1. Define a *symmetric* sieve weight by orbit coefficients `c : Partition → ℚ` (its
   associated `PolynomialSieveWeight k` exists abstractly as a `Finset.biUnion` over
   orbits — never enumerated).
2. Prove `polynomialMaynardDenominator P_sym = Σ_{λ,μ} c_λ c_μ · Mr[λ][μ](k)` and the
   numerator analog — **the matching/overlap closed form, proven generally in k**. This is
   a symmetric-function integration identity: mathlib-grade combinatorics, the genuine
   multi-session theory build.
3. Only then: at fixed k (54), plug in → `native_decide` the N×N rational form > 4, where
   N = #orbits at the required (high) degree.
4. Chain `Mk_ge_polynomialMkF` + `mkF_*_eq` → `Mk 54 > 4` → discharge the axiom.

Step 2 is **not Aristotle-shaped** (it's a general theorem, not a bounded decidable leaf).
The closed form is now *derived and validated* (de-risked), but formalizing the parametric
identity is the work.

## Bottom line / recommendation

The reduction is **correct and de-risked** (matching closed form validated exactly vs the
brute oracle). But three facts together push toward **bank, don't build** unless the
EH-conditional ladder is specifically wanted:

1. It buys only the **EH-conditional** `mk_*` ladder, NOT the unconditional flagship (246),
   which needs an independent `Mk_eps` polynomial bridge.
2. The core deliverable is a **parametric-in-k symmetric-function integration identity**
   (the matching closed form, in Lean) — mathlib-grade combinatorics, multi-session,
   degree-independent in difficulty.
3. Even the first rung (M_54 > 4) needs a **high-degree** witness (≥8, likely teens),
   because the true M_54 is only marginally above 4 — so the final `native_decide` is on a
   large form and the witness must be extracted in **exact** arithmetic (float is useless).

If built, the leverage play is: prove the parametric identity ONCE, then every rung
(54, 5511, 41588, 309661) is an `native_decide` away — but each at its own (growing) degree.

## ⭐ The CONTINGENCY-TABLE closed form (2026-06-01 — validated, the Lean target)

The Lean port should NOT formalize the bespoke "partial matching" type of `mk_sym.py`. There is a
cleaner, equivalent closed form in terms of **contingency tables** (margin-constrained `ℕ`-matrices),
which is far more Lean-tractable. Validated exactly vs brute force on 25 structured + random cases by
`tools/mk/validate_contingency.py`.

The Lean tower (`SymmetricReduction.lean`: `orbitPair_denominator_eq` + `orbitPair_core_const` +
`group_sum_eq_stab_smul_orbitSum`) reduces every cross-orbit denominator matrix entry to one
single-orbit core sum

    S(α,β) := ∑_{p ∈ orbit α} ∏ᵢ (pᵢ + βᵢ)!        (β fixed; orbit = distinct rearrangements over Fin k)

and the validated closed form is

    S(α,β) = ∑_X ( ∏_t multinomial(n_t ; x_{·,t}) ) · ∏_{u,t} ((c_u + b_t)!)^{x_{u,t}}

where, over ALL k slots (zeros included):
  • `c_u` (mult `m_u`) = distinct α-values; `b_t` (mult `n_t`) = distinct β-values; `∑m_u = ∑n_t = k`.
  • `X` ranges over `r×s` nonneg-int matrices with **row sums `m_u` and column sums `n_t`**
    (`x_{u,t}` = #slots with α-value `c_u` AND β-value `b_t`). A SMALL, k-bounded set: only the
    nonzero-value sub-block is free; the zero row/col entries are fixed by the margins.
  • `multinomial(n_t; x_{·,t}) = n_t! / ∏_u x_{u,t}!` = ways to fill β-group `t`'s `n_t` slots.

The `ff(k,T)=k.descFactorial T` of the matching form re-emerges from the zero-margin multinomials
(`n_0! / (x_{0,0}! · …)` with `n_0 = k − |β-support|`); at FIXED `k=50/54` the table sum is a concrete
finite rational, so `native_decide`-able directly — no need to factor out `ff(k,T)` abstractly.

**Two clean theorems decompose the Lean proof of `S(α,β) = ∑_X …`:**
1. *Weight depends only on the joint type* — `∏ᵢ G(pᵢ)(βᵢ) = ∏_{vt} G(vt.1)(vt.2)^{#{i:(pᵢ,βᵢ)=vt}}`.
   ✅ **DONE**: `prod_eq_prod_pow_joint` (`SymmetricReduction.lean`, axiom-clean). With `G a b = (a+b)!`
   this is exactly the `∏_{u,t} ((c_u+b_t)!)^{x_{u,t}}` factor.
2. *Fiber count* — `#{p ∈ orbit α : joint-type(p,β) = X} = ∏_t multinomial(n_t; x_{·,t})` for a table
   `X` with the right margins (else 0). ← the remaining combinatorial heart; a product-of-multinomials
   count (mathlib has `Nat.multinomial`). Then `Finset.sum_fiberwise` over the joint-type map assembles
   `S(α,β) = ∑_X (fiber count)·(weight)`. **Decomposes into three sub-pieces:**
   - (a) **orbit↔fiber-sizes bridge** — ✅ **DONE** `mem_monoOrbit_iff` (`SymmetricReduction.lean`,
     axiom-clean): `p ∈ monoOrbit α ↔ ∀ v, #{i:pᵢ=v} = #{i:αᵢ=v}`. Forward `Equiv.sum_comp`; reverse
     glues per-value fiber equivs (`Fintype.equivOfCardEq`) via `Equiv.ofFiberEquiv`. This converts the
     `monoOrbit` membership into the function-counting world.
   - (b) **margin lemma** — ✅ **DONE** `card_filter_eq_sum_joint`: `#{i:pᵢ=c} = ∑_b #{i:pᵢ=c ∧ βᵢ=b}`.
     With (a) this pins `X`'s row margins to α's fiber sizes (fiber empty otherwise); column margins are
     β's fiber sizes by symmetry.
   - (c) **keystone counting lemma** — ✅ **DONE** `card_fiberwise_eq_multinomial`
     (`SymmetricReduction.lean`, axiom-clean). `#{f : ι → V | ∀ v, #{i:f i=v} = h v} =
     Nat.multinomial univ h` when `∑ h = |ι|`. **Proven natively (NOT via Aristotle)** by
     orbit–stabilizer: `σ ↦ f₀ ∘ σ` surjects `Perm ι` onto the fiber set with fibers = stabilizer
     cosets, so `|ι|! = #{fibers=h}·∏(h v)!` (`DomMulAct.stabilizer_card`); cancel against
     `Nat.multinomial_spec`. Witness from `exists_fiberwise`; surjectivity from `Equiv.ofFiberEquiv`.
     (Aristotle project `15ba0cd4` was cancelled — landed by hand first, no v4.28→29 port needed.)
   - (e) **compose** — ✅ **DONE** `card_jointType_eq_prod_multinomial`: `#{f:ι→V | J_g(f)=X} =
     ∏_b multinomial(univ, X(·,b))`, given column margins `∑v X v b = |{i//g i=b}|`. The general
     contingency-table closed form, over arbitrary Fintypes. **The full general fiber count is
     complete.**
   - (d) **β-group product** — ✅ **DONE** `card_jointType_eq_prod` (`SymmetricReduction.lean`,
     axiom-clean, general over Fintypes `ι,V,B`): `#{f:ι→V | ∀ v b, #{i:f i=v ∧ g i=b}=X v b} =
     ∏_b #{q:{i//g i=b}→V | ∀ v, #{j:q j=v}=X v b}`. Via `fiberRestrictEquiv` ((ι→V)≃∀b,(fiber_b→V),
     from `sigmaFiberEquiv`+`piCurry`) + `Fintype.card_pi` + `subtypePiEquivPi`; per-coordinate fiber
     identity by `subtypeSubtypeEquivSubtypeInter`. **Stated over a Fintype codomain `V` — so it
     composes directly with the keystone (c) (also Fintype codomain): the integration wrinkle is
     resolved by taking `V = ↥(image α)` (the finite value-set) throughout.**
   - (f) **value-restriction bridge** — ⏳ **the only remaining piece**: connect `monoOrbit α |>.filter
     (joint-type vs β = X)` (codomain ℕ) to (d)'s Fintype form with `V=↥(image α)`, `B=↥(image β)`.
     Uses (a) `mem_monoOrbit_iff` (every `p ∈ monoOrbit α` has values in `image α`, and for a *realized*
     `X` the orbit constraint is redundant — the row margins force it). Then `Finset.sum_fiberwise`
     over the joint-type map assembles `S(α,β) = ∑_X (fiber count)·(weight from prod_eq_prod_pow_joint)`.

## Lean foundation status (2026-05-31, updated session 2)

`BoundedGaps/SymmetricReduction.lean` (axiom-clean, green):
- `permWeight σ P` — the coordinate-permutation action on a polynomial sieve weight.
- `polynomialMaynardDenominator_permWeight` — **denominator** permutation-invariance (`a54d04e`).
- ✅ **`polynomialMaynardNumerator_permWeight`** + **`polynomialMkF_permWeight`** — DONE (`aa92ad5`).
  Full Rayleigh-ratio invariance. The "restrict to symmetric F is WLOG" bedrock is now COMPLETE.
  Done via `removeNth_sum_comp_perm`/`removeNth_prodFactorial_comp_perm` (deleting position `i`
  from `w∘σ` vs position `σi` from `w` drop the same value `w(σi)`, so share `∑` and `∏(·)!`;
  cancel `w(σi)` directly — no induced perm on `Fin n`) → `dirichletIntegralWithSlack` invariance
  → reindex outer `i`-sum by σ (`Fintype.sum_equiv`).
- ✅ **`placement_count`** (`9a74394`): `Fintype.card (Fin T ↪ Fin k) = k.descFactorial T` — the
  `ff(k,T)` factor of the matching closed form (bijective core; source of polynomial-in-`k`).

`BoundedGaps/EpsScaling.lean` (new, axiom-clean, green) — the **`Mk_eps` polynomial bridge** (the
only path to the unconditional flagship H₁≤246). **Both Rayleigh sides now reduced to closed form:**
- ✅ `simplex_eps_eq_smul` / `monomialIntegral_eps` : `∫_{simplex_eps} ∏ tᵢ^αᵢ = (1+ε)^(k+|α|) ·
  monomialIntegral α` — the homothety scaling law (the denominator is a pure dilation).
- ✅ `mkF_eps_denominator_poly` : `∫_{(1+ε)R_k} P² = Σ_{p,q} c_p c_q (1+ε)^{k+|p+q|} monomialIntegral(p+q)`.
- ✅ **`dirichlet_affine_slack`** (the ε-numerator KEYSTONE): `∫_{(1-ε)R_n} ∏sⱼ^aⱼ (1+ε-∑s)^β =
  (1-ε)^{n+|a|} Σ_m C(β,m)(2ε)^m(1-ε)^{β-m} dirichletIntegralWithSlack(a,β-m)`. The slack base 1+ε
  ≠ domain bound 1-ε, so not a single standard Dirichlet integral; rescale `s=(1-ε)σ`, then
  `1+ε-(1-ε)∑σ = 2ε+(1-ε)(1-∑σ)` and `add_pow` expands into standard slack-Dirichlet integrals.
- ✅ `inner_eq_eps` / `Ji_bridge_eps` / `mkF_eps_numerator_poly` : the `Mk_eps` numerator for a
  polynomial weight = triple sum of those affine-slack integrals (ε-analogs of `inner_eq`/`Ji_bridge`).

Remaining Lean steps (genuinely multi-session each; host-better — box builds OOM-retry):
1. **The matching closed-form identity** (the real combinatorial kernel): prove
   `polynomialMaynardDenominator P_sym = Σ_{λ,μ} c_λ c_μ · S_den(λ,μ,k)/(k+|λ|+|μ|)!` (and the
   numerator analog) for an orbit-symmetric weight, with `S_*` the matching/overlap sums in
   `mk_sym.py`. Needs: an orbit→labelled-placement bijection counted by `placement_count`, the
   weight `W(M)`, and `monomialIntegral`'s dependence only on the overlap type. Mathlib-grade.
2. **Finish the `Mk_eps` bridge** — the closed forms above are in; what remains is the *assembly*:
   define a rational `polynomialMkF_eps` (for rational ε), prove `polynomialMkF_eps_eq_MkF_eps`
   (the numerator+denominator bridges feed straight in), and the cutoff/DCT
   `Mk_eps_ge_polynomialMkF_eps` — a mirror of `SievePolynomial`'s DCT development
   (`denom_tendsto`/`J_i_tendsto`/`numer_tendsto`/`Mk_ge_polynomialMkF`) over the ε geometry, then
   `Mk_eps_gt_of_polynomial_witness`. This unlocks discharging `mk_eps_50_witness` → H₁≤246.

## Files
- `mk_sym.py` — closed-form reduction (scales to any k); `validate` subcommand.
- `_exact.py`, `_ldl.py` — exact LDL-inertia sup / threshold tests (the trustworthy path).
- `mk5_sym.py` — original brute monomial reduction (validation oracle, k≤~10).
- `mk50_p1.py` — the earlier P_1-only probe (plateau ≈3.23).

## Orbit-free re-index status (2026-06-02) — DENOMINATOR done, NUMERATOR partial

`BoundedGaps/SymmetricReductionOrbitFree.lean` (new, sorry-free, axiom-clean):
- **Denominator: COMPLETE & fully orbit-free.** `orbitCore_eq_multinomial_sum_orbitFree`
  (S(α,β) re-indexed over `MarginCorrectTables`, a Fintype-bounded contingency Finset),
  `orbitPair_denominator_shapeForm` (whole entry = `multinomial(β fibers) • table-sum /
  (k+|α|+|β|)!`, NO monoOrbit). Realizability converse `joint_realizability` was formalized
  by **Aristotle** (job 38089125) and ported v4.28→v4.29 with zero edits
  (`BoundedGaps/JointRealizability.lean`). `monoOrbit_card_eq_multinomial` kills the last
  orbit reference.
- **Numerator: constant factored only.** `orbitPair_numerator_eq` factors out the constant
  Dirichlet denominator `(n+1+|α|+|β|+1)!` (the clean first step, mirrors
  `orbitPair_denominator_eq`).

**KEY FINDING — the numerator q-collapse FAILS (so it's NOT a denominator mirror).** The
summand `1/((pᵢ+1)(qᵢ+1))·dirichlet(removeNthᵢ(p+q))(pᵢ+qᵢ+2)` couples `p`, `q`, and the
marked coordinate `i` at the same index. Reindexing `q=β∘τ` alone sends `qᵢ→β(τi)` but leaves
`pᵢ` pinned, so `∑ᵢ g(i,p,β∘τ) ≠ ∑ᵢ g(i,p,β)` — the inner sum is NOT orbit-β-constant for
fixed p (unlike the denominator's `∑ₚ∏(pᵢ+βᵢ)!`). So `orbitPair_core_const` has no numerator
analog. The numerator orbit-free form needs the **joint route**: lift both orbit sums to the
full symmetric group (`group_sum_eq_stab_smul_orbitSum`, divide by stabilizers), reindex
`(p,q,i)` together, and land on a **pointed contingency table** (joint type of (p,q) PLUS the
value pair at the marked coordinate i). This is the genuine multi-session theory build.

### CORRECTION (2026-06-02, later) — numerator is denominator-grade after all
The "q-collapse fails → multi-session pointed build" pessimism above is SUPERSEDED.
`numerator_summand_factor` (SymmetricReductionOrbitFree.lean): the removeNth-product times
the slack factorial factors as `(∏ₘ(p+q)ₘ!) · (pᵢ+qᵢ+2)!/(pᵢ+qᵢ)!` — a joint-type weight
times a LOCAL factor in (pᵢ,qᵢ) only. So `∑ᵢ` of the local factor = `∑cells Y_{a,b}·M(a,b)`
for the (p,q) joint type Y, and the numerator double-sum regroups over the SAME (p,q)
joint-type contingency tables as the denominator (margins = α-fibers × β-fibers), with
summand = [∏cells ((a+b)!)^{Y}] · [∑cells Y·M(a,b)] · (pair-count). The q-collapse still
fails, but the joint-type regrouping does NOT need it. Next: a `MarginCorrectTables`-style
sum for the numerator + the pair-count (card_jointType machinery). Denominator-grade, not a
new theory.

## NUMERATOR DONE (2026-06-02, later still) — both matrix entries orbit-free + native_decide-ready

`BoundedGaps/SymmetricReductionOrbitFree.lean` (sorry-free, axiom-clean):
- **Numerator: COMPLETE & fully orbit-free.** `orbitPair_numerator_orbitFree`: the full
  off-diagonal numerator (marked-coordinate triple sum of `dirichletIntegralWithSlack`) =
  `(∑_{T∈MarginCorrectTables} multinomial(T cells)·pairWeight(tableToMultiset T)) /
  (n+1+|α|+|β|+1)!`. **No monoOrbit on the RHS, and — unlike the denominator — NO orbit
  cardinality factor**: the numerator regroups over the full (p,q) joint type, so the
  q-collapse is never invoked. `orbitPair_numerator_computable` is the `native_decide`-ready
  restatement (`pairWeightC` = computable twin of `pairWeight`; verified `pairWeightC
  {(2,1),(1,1),(0,0)} = 100` in-kernel).
- The re-index keystone `numerator_orbitFree` reuses the denominator's table bijection via
  `pair_image_eq` (the product-orbit joint-type image collapses to the single-orbit image,
  realizing the column vector as `q=β`) + `pair_fiber_card_eq_multinomial` (pair-fiber count =
  full-cell 2-D multinomial, the numerator analog of the denominator fiber count). New
  general-column joint machinery: `joint_sum_over_col/_row`, `joint_entry`,
  `joint_multisetToTable_mem`, `tableToMultiset_jointTable`.
- **Both Rayleigh matrix entries are now orbit-free closed forms computable from α,β shapes
  alone.** This finishes the orbit-free re-index milestone (Coding Step 1–3 of the prior plan).

## BOTH PIPELINES COMPLETE + VALIDATED (2026-06-02, final) — only data + native_decide remain

**EH path (`mk_54_witness_under_EH` → H₁≤246) AND the ε path (`mk_eps_50_witness` → unconditional
H₁≤246) are both built, axiom-clean, and validated end-to-end.** The ε analog is in
`BoundedGaps/SymmetricReductionEpsOrbitFree.lean`: `gramDenEntryEps`/`gramNumEntryEps` (computable
ε Gram entries — the ε-numerator via `affineSlackRat_removeNth_factor`, which is denominator-grade
per binomial index `m` thanks to the `(pᵢ+qᵢ)` cancellation), `polynomialMkF_eps_symWeight_computable`,
`mk_eps_50_witness_of_symWeight`, `Mk_eps_gt_of_symWeight_witness_computable` (generic). Validated:
committed `example` proves `Mk_eps 3 (1/10) > 1`, both `native_decide`s firing (ε quotient ≈1.048).

The EH matrix assembly and the entire chain to `mk_54_witness_under_EH` in
`BoundedGaps/SymmetricReductionOrbitFree.lean`:
- **Gram entries** `crossDenominator` / `crossNumerator` (bilinear forms on two weights) +
  `cross*_orbitSum_computable` (= the orbit-free closed forms). Computable twins `gramDenEntry` /
  `gramNumEntry` (`#eval`: `gramDenEntry ![2,1,0] ![1,1,0] = 11/3360`, `gramNumEntry = 7/2160`).
- **Bilinear expansion**: `symWeight R c` (= `∑_λ c_λ orbitSum λ`, disjoint-union terms) and
  `polynomialMaynard{Denominator,Numerator}_symWeight` = `∑_{a,b∈R} c_a c_b cross*(a)(b)`; ratio
  `polynomialMkF_symWeight`.
- **Witness chain**: `Mk_gt_of_symWeight_witness(_computable)` (Gram quotient `> T` ⟹ `Mk(n+1) > T`,
  via the real `Mk_ge_polynomialMkF`), `exists_theta_of_Mk_gt` (⟹ the `∃ϑ, Mk > T/ϑ` shape),
  `mk_54_witness_under_EH_of_symWeight_computable` and the uniform `mk_witness_under_EH_of_symWeight_computable`
  (all 5 EH witnesses, `T = 2m`).
- **`hR` mechanized**: `disjoint_of_histogram R (by native_decide)` (orbits partition;
  `monoOrbit` is noncomputable so the histogram form is the decidable route).
- **END-TO-END VALIDATED**: a committed `example` proves `Mk 3 > 1` through the whole pipeline,
  both `native_decide`s firing (R = {![2,1,0],![1,1,0]}, c≡1, quotient 2063/2060).

### The ONLY remaining step (host/data-side)
Produce the optimal `k=54` data `(R, c)` from `mk_sym.py` / `_ldl.py` (orbit reps + LDL coeffs,
degree ≥9), then in `BoundedGaps/Polymath8b.lean`:
```
theorem mk_54_witness_under_EH := OrbitFree.mk_54_witness_under_EH_of_symWeight_computable
  R c (OrbitFree.disjoint_of_histogram R (by native_decide)) (by native_decide)
```
The two `native_decide`s are the same ones validated at k=3; at k=54 they are heavy
(degree-9 contingency-table enumeration) — **host-better, may OOM the box**. If too slow, fall
back to a `Fin`-indexed table reformulation of `gram*Entry`. No more theory is required.
