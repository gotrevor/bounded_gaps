# PENDING WORK — open axioms, attack paths, and the numerical-endgame diagnosis

Last updated: 2026-06-05. Branch `path-a-selberg-nu`.

## ✅✅✅✅✅✅ PROGRESS 2026-06-05 (lap 6) — y-space S1 crystallised to ONE conditional theorem + correction is UNCONDITIONAL (not BV-gated)

Three axiom-clean commits (`648d461`, `e02d2cb`, `4643f46`), full build green (8296 jobs) at every
gate. This lap (a) crystallised the whole contour-free y-space S1 chain into a single top-level limit
about the **actual** sieve sum, (b) discharged the unconditional diagonal half of the correction, and
(c) **corrected a strategic error in the handoffs**: the s1 correction is *not* BV-gated.

### NEW files (all axiom-clean `[propext, Classical.choice, Quot.sound]`)
- **`S1MainLimit.lean`** — the heuristic-main limit, B^{+k} normalisation:
  - `yspace_box_quadform_div_tendsto` (J=1 instance of `yspace_kd_box_product_tendsto`):
    `∏ᵢ quadForm/(log N)^k → (φW/W)^k·mkF_den`.
  - **`yspace_s1_heuristic_main_div_sieveB_tendsto`**: with level `R=N`, scale `x=W·N+2`, the y-space
    heuristic main `/ (sieveB W N ^ k · M) → mkF_denominator k (∏Fs)` — **α exactly `mkF_denominator`,
    no leftover factor** (the (φW/W)^k singular series and (log N)^k all absorbed into B^{+k}). The
    contour-free analog of `alphaBound`'s `(α+o(1))·B^{-k}·x/W`.
- **`S1DiagonalSize.lean`** — the diagonal half of `correction = o(main)`, **unconditional**:
  - `ratio_log_pow_tendsto_zero` (`(1+L)^{k-1}/L^k → 0`), `ratio_loglog_tendsto_zero`,
    **`hyperbola_count_div_tendsto_zero`** (`Dₖ(N)/(N·(log N)^k) → 0`), `hyperbola_count_isLittleO`
    (the `IsLittleO` form). Squeezes the k-D Dirichlet count (`Sieve.hyperbola_count_le`) against
    `(1+log N)^{k-1}/(log N)^k`. Convention-independent (count is the same object d-/y-space).
- **`S1FullLimit.lean`** — the honest top-level statement:
  - **`yspace_s1_sieveSum_div_tendsto`**: the *actual* `sieveSum (selberg_nu_yr_sep …)` at scale
    `x=W·N+2`, level `R=N`, `/ (sieveB W N ^ k · M) → mkF_denominator k (∏Fs)`, **conditional ONLY on
    the correction `hcorr : correction/(sieveB^k·M) → 0`** + `hBaseW`. Composes the (unconditional)
    heuristic-main limit with the exact algebraic split
    (`S1YSpace.sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction`).

### ⚠️⚠️ KEY STRATEGIC CORRECTION (lap 6): the s1 correction is UNCONDITIONAL, NOT BV-gated
The lap-4/5 handoffs repeatedly call the s1 off-diagonal `o(main)` correction "BV-gated (gap C)".
**This is wrong — it conflates s1 with s2.** Classically (Maynard, GPY) and per the repo's own
`archive/findings/ON-LINE-FINDINGS-2026-06-04-gpy-diagonal-asymptotic.md` (line 121: the s1 sum "is
the **unconditional** case, needs no EH"), **only S2 (the prime weight `θ`) needs EH/BV** for its
level of distribution; **S1 (the non-prime weight) is elementary** — bounded by divisor sums +
singular-series convergence. So the contour-free y-space S1 can be completed with **no analytic
axioms** (only `hBaseW`, which Aristotle `65d11d89` is computing, + the architectural `B^{±k}` flip).

**Concrete elementary attack for the off-diagonal correction (the `hcorr` of `S1FullLimit`):** with
the W-trick (`W = ∏_{p≤D₀}p`, `D₀ ≥ all hᵢ`), `lattice_count_offdiag_vanish_Wtrick` gives `count_P=0`
for every `¬diag` P (two coordinates sharing a prime `p>D₀`, incompatible shifts). So
`correction = [diagonal O(1) error] − [off-diagonal main ∑_{¬diag}(∏λλ)·M/∏[dᵢ,eᵢ]]`.
- **Diagonal O(1) error** `∑_{diag}|∏λλ|·1`: bounded by the diagonal weight `≤ C²·Dₖ(R)`
  (`Sieve.diagonal_weight_le_count`) `= o(M·(log R)^k)` via **`S1DiagonalSize` (DONE this lap)** — once
  the y-space coefficient `∏ yLambda²` is bounded `≤ C²·∏μ²·F²` (the remaining y-space coeff bound).
- **Off-diagonal main** `M·∑_{¬diag P}|∏λλ|/∏[dᵢ,eᵢ]`: bound `∑_{¬diag} ≤ (∑_{i<j}∑_{p>D₀}1/p²)·∏ᵢQ'ᵢ`
  where `Q'ᵢ = ∑_{d,e}|λλ|/[d,e] = O(log R)`; the shared-prime restriction gives the `∑_{p>D₀}1/p²`
  factor `→ 0` as `D₀→∞` (Mertens-level, **in mathlib** — no BV). ⟹ `= o(M·(log R)^k) = o(main)`.

So the next lap's S1 endgame is **two elementary, unconditional Lean lemmas** (the y-space coeff bound
+ the shared-prime singular-series `1/p²` tail), feeding `hcorr` → `S1FullLimit` becomes
unconditional, then the architectural `B^{±k}` flip (Trevor) discharges `s1_holds_from_nonprime_asym`.

## ✅✅✅✅✅ PROGRESS 2026-06-05 (lap 5) — box→simplex assembly (gap A4) + count→M candidate-set inclusion DONE

Four axiom-clean commits (`82debdc`…`823303b`), full build green (8292 jobs) at every gate. This lap
discharged the **analytic core of gap A4** (the box→simplex assembly — the second of the two named
`s1` gaps) AND the **candidate-set inclusion** half of count→`M` (the handoff-flagged "delicate bit").
All four results are `[propext, Classical.choice, Quot.sound]`, no `sorry`, no PNT, no BV.

### NEW files / theorems (all axiom-clean)
- **`S1BoxSimplex.lean`** — the box→simplex bridge (gap A4 analytic core):
  - `simplex_subset_box` (`simplex k ⊆ [0,1]^k`), `setIntegral_box_prod` (box Fubini
    `∫_box ∏ᵢgᵢ = ∏ᵢ∫₀¹gᵢ` via `Measure.restrict_pi_pi` + `integral_fintype_prod_eq_prod`),
    `mkF_denominator_eq_box` (`∫_simplex F² = ∫_box F²` for simplex-supported `F`).
  - **`box_product_eq_mkF_denominator`**: `∑_{j,j'}cⱼcⱼ'∏ᵢ∫₀¹Fs_{j,i}Fs_{j',i} = mkF_denominator k F`.
    The separable sieve's box-product main constant **IS** the Maynard simplex denominator (because the
    witness `F` is simplex-supported, so `∫_box F² = ∫_simplex F²`). Pure analysis, unconditional.
- **`S1KDBox.lean`** — the full k-D box-product `s1` main-term limit:
  - `quadForm` (the 1-D y-space bilinear Selberg form over `R_N`), `quadForm_div_log_tendsto`
    (wraps `yspace_sieve_quadform_bilinear_tendsto`), `intervalIntegral_eq_setIntegral_Icc`
    (`∫ 0..1 = ∫ in Icc 0 1`, reconciling the interval/set integral forms).
  - **`yspace_kd_box_product_tendsto`**: `(∑_{j,j'}cⱼcⱼ'∏ᵢ quadForm W Fs_{j,i} Fs_{j',i} N)/(log N)^k
    → (φW/W)^k · mkF_denominator k F`. The COMPLETE contour-free k-D `s1` main-term limit for the
    separable y-space sieve, over the clean index `R_N = {r≤N: sf ∧ (r,W)=1}`. Assembled from the
    per-coordinate bilinear tendsto (`tendsto_finset_prod` over coords, `tendsto_finset_sum` over
    `(j,j')`) + the box→simplex bridge. Conditional only on `hBaseW` (Aristotle `65d11d89`).
- **`S1CandidateSet.lean`** — the count→`M` candidate-set inclusion (the "delicate bit"):
  - **`exists_n_interval_crt`**: for `(W,r)=1` and an interval `≥ W·r` long, ∃ `n` in residue class
    `b (mod W)` with `r ∣ n+h` (Chinese remainder `Nat.chineseRemainder` + representative landing).
  - **`mem_sieveDivisors_of_coprime`**: hence every small sf `W`-coprime `r ∈ sieveDivisors`.
  - **`filter_Icc_subset_filter_sieveDivisors`**: `{r≤N: sf ∧ (r,W)=1} ⊆ Rset_i` when the interval is
    `≥ W·N` long — the inclusion the count→`M` reconciliation consumes. Pure NT, unconditional.

### Where `s1` stands NOW (refined map — TWO of the named gaps advanced this lap)
- **Gap A4 (box→simplex assembly) — analytic core DONE.** `box_product_eq_mkF_denominator` +
  `yspace_kd_box_product_tendsto` land the separable-sieve box-product main term on
  `(φW/W)^k·mkF_denominator`. (Earlier lap's `s1_yr_mainTerm_eq_mkF_denominator_decomp` is the
  *simplex-nested* analog; this lap's is the *box-product* form the capstone
  `yr_heuristic_main_eq_muphi` actually produces.)
- **Count→`M` — main density EXISTS, candidate-set inclusion DONE.** The CRT lattice count main term
  `|count − (B−A)/(W·∏q)| ≤ 1` is ALREADY proven (`SieveExpansion.lattice_count_main_term`,
  axiom-clean). This lap added the candidate-set inclusion (`filter_Icc_subset_filter_sieveDivisors`).
  **What's LEFT in count→`M`:** (a) the NORMALISATION glue — match `M·(box product)/(log R)^k` to
  `α·alphaMainTerm = mkF_denominator·B^{-k}·x/W` (the `M`, `B = φW/W·logx`, `(log R)^k`, `(φW/W)^k`
  bookkeeping — careful, do NOT hand-wave; tie `R = x^{θ/2}`, `M = (⌊2x⌋−⌈x⌉)/W`); (b) the
  off-diagonal `correction = o(main)` — **BV-gated** (gap C; `correction_abs_bound` exists).
- **`hBaseW`** (Aristotle brick `65d11d89`, still RUNNING ~1.5h+) ⟹ general-`W` unconditional.
- Then Trevor flips the 3 `s1`/`s2` axioms + `selberg_sieve_data_from_F` to `selberg_nu_yr` (witness
  layer `mkF_denominator`/`Mk_200_gt_4` UNTOUCHED).

### NEXT concrete sub-steps (for whoever continues count→`M`)
1. ✅ **DONE** (`S1CandidateSet.sieve_interval_lower_bound`/`sieve_interval_covers`): for `x ≥ W·N+2`
   the interval `[⌈x⌉,⌊2x⌋]` is `≥ W·N` long (`⌈x⌉<x+1`, `2x<⌊2x⌋+1`) — fires
   `filter_Icc_subset_filter_sieveDivisors` for large `x`.
2. ✅ **DONE** (`S1CandidateSet.coord_sum_restrict_to_Icc`/`_bilinear` +
   `S1CountReconcile.yr_coord_factor_eq_Icc_sum`): `∑_{r∈Rset_i}(μ²/φ)F² =
   ∑_{r∈(Icc 1 N).filter}(μ²/φ)F²` via the inclusion (small `r` appear) + the `F`-level cutoff
   (`F(log r/log R)=0` for `r>N≥⌊R⌋ ⟹ r>R` kills the extra large divisors). The assembled
   `yr_coord_factor_eq_Icc_sum` is the exact per-coordinate bridge from the capstone
   `yr_heuristic_main_eq_muphi` to `yspace_kd_box_product_tendsto` (both single-F and bilinear forms).
3. **Normalisation assembly** (the remaining count→`M` content). With (1)+(2) and
   `lattice_count_main_term` (`|count − (B−A)/(W·∏q)| ≤ 1`, already proven): (a) set the level `R = N`
   (a nat) so the capstone scaling `log R` matches the tendsto scaling `log N`, and `x = x(N)` tied
   `≥ W·N+2`; (b) rewrite the k-D heuristic main `= M·∏ᵢ ∑_{r≤N: sf,coprime}(μ²/φ)Fᵢ²` (capstone +
   `yr_coord_factor_eq_Icc_sum` per coord); (c) divide by `M·(log N)^k` ⟹
   `→ (φW/W)^k·mkF_denominator` (`yspace_kd_box_product_tendsto`); (d) the **careful** bit — match
   `M·(log N)^k·(φW/W)^k` to `alphaMainTerm = (φW/W·log x)^{−k}·(x/W)` (identify `M = (⌊2x⌋−⌈x⌉)/W` and
   `N` vs `x` via `R = x^{θ/2}`; do NOT hand-wave the `(φW/W)`-power and `log` bookkeeping). Then feed
   `alphaBound_of_heuristic_correction`; the off-diagonal `o(main)` correction is the **BV-gated** half.

   ⚠️⚠️ **KEY FINDING this lap (lap 5): step 3d is NOT mere bookkeeping — it is entangled with the
   d-space↔y-space convention flip (Trevor's architectural call), and the `alphaMainTerm` in
   `Sieve.lean` is the WRONG normalisation for the y-space chain.** Worked through honestly:
   - The reconciled y-space heuristic main is `M·∏ᵢ∑_{r≤N}(μ²/φ)Fᵢ²` with `M = (B−A)/W = x/W` the
     lattice density (`lattice_count_main_term`). Each coordinate sum `~ log N·(φW/W)∫Fᵢ²`
     (`yspace_kd_box_product_tendsto`), so the **y-space S1 `~ (x/W)·(log R)^k·(φW/W)^k·∫F²`** — the
     `(log R)^k` grows (matches Maynard/GGPY `S1 ~ (N/W)(log R)^k I_k(F)·𝔖`).
   - But `alphaMainTerm k W x = sieveB^{−k}·(x/W) = (φW/W·log x)^{−k}·(x/W)` carries `(log x)^{−k}`,
     which DECAYS. So `α·alphaMainTerm` has `(log x)^{−k}` while the y-space S1 has `(log R)^{+k}` —
     opposite powers. They cannot match for any constant `α`.
   - **Diagnosis:** `alphaMainTerm = B^{−k}·x/W` is the **d-space** main term (it pairs with the
     d-space `λ_F` whose constant is `∫(F')²` — the off-by-a-derivative landmine; the `B^{−k}` and the
     derivative are two faces of the SAME convention). The y-space construction's main term is
     `B^{+k}·x/W·∫F²` (no derivative, growing `log` power). So flipping `ν → selberg_nu_yr` is NOT
     enough — **`alphaMainTerm` (and `betaMainTerm`) must ALSO be restated to the y-space `B^{+k}`
     normalisation**, or `alphaBound`/`betaBound` rephrased. This is a flagship-touching convention
     change = Trevor's call (consistent with the handoff's "Trevor flips the axioms").
   - **⟹ Concrete recommendation for the flip:** when Trevor re-targets `s1`, introduce
     `alphaMainTerm_yspace k W x := sieveB^{(k:ℤ)}·(x/W)` (note `+k`) and prove
     `alphaBound k (selberg_nu_yr …) b W x (mkF_denominator k F)` against THAT. The machine-checked
     y-space chain (capstone → `yr_heuristic_main_eq_Icc_product` → `yspace_kd_box_product_tendsto` →
     `box_product_eq_mkF_denominator`) then lands `~ (x/W)(log R)^k(φW/W)^k∫F²` directly, with `M`
     genuinely `= x/W` and NO fudge factor. Everything feeding this is now machine-checked; only the
     `B^{±k}` normalisation choice (architectural) + the BV-gated `o(main)` correction remain.

## ✅✅✅✅ PROGRESS 2026-06-05 (lap 4) — contour-free Path-Y `s1` ANALYTIC MAIN TERM FULLY ASSEMBLED + FIRM `s1` verdict

Eight axiom-clean commits (`4bf8830`…`bc6317e`), full build green (8288 jobs) at every gate. The
**entire analytic backbone** of the contour-free Path-Y `s1` main term is now machine-checked: from
the explicit y-space sieve coefficient through the diagonalization to the `(φ(W)/W)·∫F²` limit, with
NO PNT. What remains is purely structural (the `selberg_nu_yr` *definition* + lattice-count
reduction) plus the W-coprime base (Aristotle).

### THE ASSEMBLED CHAIN (all axiom-clean, this lap)
`SieveExpansion.lean`:
- `moebius_div_collapse` (`∑_{e|m}μ(e)=[m=1]`), `inner_moebius_collapse` (`∑_{d|s,r|d}μ(s/d)=[s=r]`),
  **`moebius_inversion_multiples`** (divisor-closed `R`, `a(d)=∑_{s∈R,d|s}μ(s/d)Y(s)` ⟹
  `∑_{d∈R,r|d}a(d)=Y(r)`) — the exact `λ_d ↔ smooth-y_r` duality.
- **`gpy_diagonalize_yform_smooth`** (`λ_d=d·a(d)` ⟹ `∑_{d,e∈R}λ_dλ_e/[d,e]=∑_{r∈R}φ(r)Y(r)²`,
  via `gpy_diagonalize`+inversion) and **`gpy_diagonalize_yform_muphi`** (with `Y(s)=F(log s/L)/φ(s)`
  on squarefree `R`: `= ∑_{r∈R}(μ²/φ)F(log r/L)²`).
- `sieveR_yspace_hyps` (the real sieve index set `R_N={r≤N: sf ∧ (r,W)=1}` is `≥1`, squarefree,
  divisor-closed ⟹ all the above apply to it).
`WeightedMertens.lean`:
- `gMuSqTotientCoprime_sum_eq_filter` (connector: `∑_{n≤N}g_W·G = ∑_{r∈R_N}(μ²/φ)·G`),
- **`yspace_muphi_diagonal_tendsto`**: `(∑_{r∈R_N}(μ²/φ)F(log r/logN)²)/logN → (φ(W)/W)·∫F²`
  = the limit of `gpy_diagonalize_yform_muphi`'s output. **The Path-Y `s1` main term, contour-free.**
  Conditional only on `hBaseW` = W-coprime sharp Mertens (Aristotle brick `65d11d89`, in flight).

### STRUCTURAL SKELETON — now COMPLETE (1-D, all blocks). 13 commits this lap.
The full contour-free chain is machine-checked end-to-end (axiom-clean):
- **`SieveExpansion.sieveSum_genProd_sq_expand`** (DONE this lap): general sieve opening for ANY
  coefficient `lam : Fin k → ℕ → ℝ` — `∑_{n∈block}(∏ᵢ∑_{d|n+hᵢ}lam i d)² = ∑_P(∏ᵢ lam i dᵢ·lam i eᵢ)·count(P)`.
  The structural bridge from a y-space `sieveSum` to the bilinear `∑λλ` form (instantiate `lam i =
  yLambda R_N (Fs i) (log R)`). [Generalises the `lambdaTransform`-only `sieveSum_lambdaProd_expand`.]
- `gpy_diagonalize_yform_muphi(_bilinear)`: `∑_{d,e∈R_N}λλ/[d,e] = ∑_{r∈R_N}(μ²/φ)F²` (after the
  count→`M/[d,e]` density step).
- `S1YSpace.yspace_sieve_quadform_tendsto(_bilinear/_one)`: `(∑λλ/[d,e])/logN → (φ(W)/W)∫F²`. The
  `_one` (W=1) instance is **FULLY UNCONDITIONAL** (base = `sharp_mertens_unconditional`).

### NEXT (the count→density reduction + final glue, then assemble) — ⬇ MUCH is now DONE
**DONE this lap (`S1YSpace.lean`):** `selberg_nu_yr_sep` (the y-space sieve weight) + `_nonneg` +
`sieveSum_selberg_nu_yr_sep_expand` (= `sieveSum_genProd_sq_expand` instance) +
`sieveSum_selberg_nu_yr_sep_eq_heuristic_add_correction` (the `M`/[d,e] split) +
`yLambda_eq_zero_of_not_mem`/`sum_yLambda_eq_of_subset`/`sum_yLambda_bilinear_eq_of_subset`
(candidate-set restriction) + `yr_coord_factor_eq_muphi` (per-coord factor over
`Rset = sieveDivisors.filter(sf∧coprime)` = `∑_{r∈Rset}(μ²/φ)F²`). **FINAL GLUE — ✅ DONE this lap** (`yr_coord_sieveDiv_factor` + **`yr_heuristic_main_eq_muphi`**):
the y-space heuristic main `= M·∏ᵢ ∑_{r≤level, sf, (r,W)=1}(μ²/φ)(r)·Fᵢ(log r/log R)²`, fully
diagonalised & contour-free. **⟹ the entire contour-free `s1` MAIN-TERM core is COMPLETE.** Each
factor `/log R → (φ(W)/W)∫Fᵢ²` (`yspace_muphi_diagonal_tendsto`).

**What's LEFT for `s1` (all BV-gated or simplex-assembly — a fresh structural lap):**
- (i) **count → `M`**: pick `M` = the lattice main density and bound `sieveSum_…_correction` =
  `o(main)` (gap C, **BV-gated**; infra `lattice_count_main_term`, `correction_abs_bound`,
  `hyperbola_count_le`, `diagonal_weight_le_count` exist).
- (ii) **simplex assembly** (gap A4): the heuristic main is `M·∏ᵢ(1-D factor) → (φ(W)/W)^k ∏ᵢ∫Fᵢ²`
  (product of marginals), but `s1`'s constant is `∫_simplex F²`. The simplex (`∏rᵢ≤R`) enters via the
  count `M`/the `n∈[x,2x]` constraint, NOT the diagonalisation — so this couples (i) with the box→simplex
  reconciliation (`weighted_riemann_kd_muphi` consumes the simplex-nested sum). The `j`-sum cross terms
  (`F=∑c∏Fs`) use `gpy_diagonalize_yform_muphi_bilinear`/`yspace_..._bilinear_tendsto` (done).
- (iii) **W-coprime base** `hBaseW` (Aristotle brick `65d11d89`) ⟹ general-`W` unconditional.
- Then Trevor flips the 3 `s1`/`s2` axioms + `selberg_sieve_data_from_F` to `selberg_nu_yr` (witness
  layer `mkF_denominator`/`Mk_200_gt_4` UNTOUCHED).
1. ~~Define `selberg_nu_yr` + expand~~ **DONE** (separable; the general `∑_j c_j` opens to `(j,j')`
   bilinear blocks via `gpy_diagonalize_yform_muphi_bilinear`, also done).
2. **Count → main density**: connect the lattice `count(P) = #{m: dᵢ,eᵢ|m+hᵢ}` to `M/∏[dᵢ,eᵢ]`
   via the EXISTING `lattice_count_main_term` / `lattice_count_eq_modEq` (the CRT count, shared with
   d-space). The diagonal gives `M·∑λλ/[d,e]` → `gpy_diagonalize_yform_muphi` → `yspace_..._tendsto`.
   ⚠️ **CANDIDATE-SET CRUX (worked out lap 4, the delicate bit):** `sieveSum_selberg_nu_yr_sep_expand`
   sums over `d,e ∈ sieveDivisors` (= `⋃ₙ (n+hᵢ).divisors`), but the diagonalization
   `gpy_diagonalize_yform_muphi` is over `R_N` (squarefree, coprime, divisor-closed). RECONCILE by
   choosing **`Rset i := (sieveDivisors H i b W x).filter (Squarefree · ∧ Coprime · W)`** — this IS
   divisor-closed (sieveDivisors is, filters preserve it) and `yLambda (Rset i) … d = 0` for
   `d ∉ Rset i` (the filter `{s∈Rset: d∣s}` is empty unless `d` squarefree-coprime-`∣`-something∈Rset,
   i.e. `d∈Rset` since divisor-closed). So `∑_{d,e∈sieveDivisors} = ∑_{d,e∈Rset}` (extra terms vanish)
   — apply `gpy_diagonalize_yform_muphi` to `Rset`. BUT then the `tendsto` (`yspace_muphi_diagonal_tendsto`)
   is over `(Icc 1 N).filter(sf∧coprime)` ⊋ `Rset` (only `r` dividing some `n+hᵢ`); the gap between
   "all `r≤R`" and "`r` appearing in the sieve" is precisely what `M`/the count absorbs (the level
   `R = x^{θ/2}`, `M = (B−A)/W`). That main-term equivalence + the `o(main)` correction is gap (C),
   **BV-gated** (`correction_abs_bound`, `hyperbola_count_le`, `diagonal_weight_le_count` exist).
   ⚠️ the off-diagonal `correction = o(main)` is **BV-gated** (gap C, shared w/ d-space; infra exists:
   `correction_abs_bound`, `hyperbola_count_le`, `diagonal_weight_le_count`). So even y-space `s1`
   needs BV for the correction — but the MAIN TERM is now contour-free & done.
3. **k-D lift** (per-coord product → `∫_simplex F²` = `mkF_denominator`): the box→simplex coupling
   (gap A4) via `weighted_riemann_kd_muphi`. NB the count ties coords to the simplex `∏rᵢ≤R`.
4. **W-coprime base `hBaseW`** (Aristotle brick `65d11d89`, still RUNNING ~1h) ⟹ general-`W`
   unconditional. Then Trevor flips the 3 `s1`/`s2` axioms + `selberg_sieve_data_from_F` to
   `selberg_nu_yr` (witness layer `mkF_denominator`/`Mk_200_gt_4` UNTOUCHED).

### Reusable lemmas added this lap (for the assembly)
`WeightedMertens`: `weighted_mertens_general(_of_contDiff)`, `gMuSqTotientCoprime`,
`weighted_mertens_coprime(_sq)`, `gMuSqTotientCoprime_sum_eq_filter`, `yspace_muphi_diagonal_tendsto`,
`yspace_muphi_bilinear_tendsto`. `SieveExpansion`: `moebius_div_collapse`, `inner_moebius_collapse`,
`moebius_inversion_multiples`, `gpy_diagonalize_yform_smooth(_bilinear)`, `gpy_diagonalize_yform_muphi(_bilinear)`,
`sieveR_yspace_hyps`, `sieveSum_genProd_sq_expand`. New file `S1YSpace.lean` (`yLambda` + the capstones).

### What landed (`WeightedMertens.lean`) — the abstraction layer
Abstracted the `μ²/φ` weighted-Mertens machinery over an **arbitrary weight `g` with base
log-density `c`** (`(∑_{1≤n≤N} g n)/log N → c`), then specialised to the `W`-trick:
- `weighted_mertens_general` (capstone): for `F` Lipschitz+cont, `(∑ g·F(log n/logN))/logN → c·∫₀¹F`.
  Helpers `BdiscG`/`sum_sub_eq_BdiscG`/`BdiscG_div_log_tendsto_zero`/`abel_tail_majorant_general`/
  `abel_tail_general`/`discrepancy_weighted_general` (general Abel-summation tail). Non-vacuity
  `example` recovers `weighted_mertens` as the `g=μ²/φ, c=1` instance.
- `weighted_mertens_general_of_contDiff` (Lipschitz from `ContDiff ℝ 1`).
- `gMuSqTotientCoprime W n := (μ²/φ)(n)·[(n,W)=1]`; **`weighted_mertens_coprime`** and
  **`weighted_mertens_coprime_sq`**: the Path-Y `s1` main term **WITH the singular series**
  `𝔖 = φ(W)/W` (Maynard `S1Summation2` / GGPY Lemma 4) —
  `(∑_{n≤N,(n,W)=1}(μ²/φ)F²(log n/logN))/logN → (φ(W)/W)·∫₀¹F² = (φ(W)/W)·mkF_denominator|_{k=1}`.
  Conditional only on the **W-coprime sharp Mertens base** `(∑_{n≤N,(n,W)=1}μ²/φ)/logN → φ(W)/W`
  (Aristotle brick `65d11d89`, in flight); the `W=1` case is exactly the existing `weighted_mertens`.

### ⚠️ THE FIRM `s1` ARCHITECTURE VERDICT (don't re-litigate — verified against the papers + mathlib this lap)
The repo's `selberg_nu` is built from `lambdaTransform` = Polymath8b `λ_F` (the **`d`-space** GPY/
Selberg sieve). **Its `s1` constant is `∫(F')²` (a DERIVATIVE), and evaluating it is genuinely
PNT-strength — there is NO contour-free route for the `d`-space construction.** Three independent
confirmations:
1. **Papers** (`archive/findings/…gpy-diagonal-asymptotic.md`): Polymath8b's own `lflg`/`c-def`
   give `c = ∏∫F'_iG'_i`; their proof IS a contour (`ζ_{WN}`, Fourier `K`). The signed inner sum
   `z_r = ∑_{(s,r)=1}μ(s)g(rs)/s ~ (r/φ(r))(−g'/logR)` is the `1/ζ(1+w)~(w−1)` behaviour = PNT.
2. **No mathlib escape**: this mathlib (v4.29.1) has `LSeries/Nonvanishing` (`ζ(1+it)≠0`) and
   `PrimesInAP` (qualitative Dirichlet), but **NO quantitative PNT** (`ψ(x)~x`) and **no Möbius
   mean** `∑μ(n)/n→0`. So the `d`-space `z_r` cannot be discharged in-kernel today. (BV is already
   an axiom and ⟹ PNT in principle, but extracting PNT-from-BV is itself a major formalization.)
3. **The witness FORCES `y`-space**: the `d`-space sieve's RATIO `∑βᵢ/α` is `M_k(F')` (derivative
   space), NOT `M_k(F)`. Our witness proves `M_k(F) > 4` for a *variational* `F` — that is the
   **`y`-space** optimisation. So `s1`'s constant `mkF_denominator = ∫F²` (with the witness `F`) is
   the `y`-space statement, and pairing it with the `d`-space `selberg_nu` is EXACTLY the
   "off-by-a-derivative" landmine. The fix is not the antiderivative *relabel* (its proof is still
   PNT — step (†) is PNT for any smooth weight, `F` or `𝔉`); it is to **change the construction**.

**⟹ CONCRETE NEXT STEP for `s1` (the actual discharge path, contour-free):** define a **`y`-space
sieve weight `selberg_nu_yr`** ALONGSIDE `selberg_nu` (do NOT touch the flagship yet — handoff's
explicit warning): smooth `y_{r} := F(log r/logR)·[r squarefree, (r,W)=1, r≤R]`, `λ_d` its Möbius
inverse, `ν(n)=(∑_{d|n+h_i}λ_d)²`. Re-run a gap-(A)-style diagonalization for THIS `λ` (the existing
`gpy_diagonalize_moebius_*` are for `λ_d=μ(d)g(d)`, not Maynard's `λ_d` — needs a new diagonalization)
to land `sieveSum ~ (count)·∑_r(μ²/φ)y² + corr`; then `∑_r(μ²/φ)y²` is **directly**
`weighted_mertens_coprime_sq` (this lap) → `(φ(W)/W)∫F²`, contour-free. The `k`-D version threads
through the already-proven `weighted_riemann_kd_muphi`. Only AFTER it validates end-to-end does
Trevor flip the 3 `s1`/`s2` axioms + `selberg_sieve_data_from_F` to feed `selberg_nu_yr` (witness
layer `mkF_denominator`/`MkF`/`Mk_200_gt_4` stays UNTOUCHED — it is about `F`, not `ν`).
KB: `[[s1-derivative-landmine]]`, `[[lean-gpy-yform-muphi-bridge]]`, `[[gpy-diagonalization-route]]`.

---

## ✅✅✅ PROGRESS 2026-06-05 (lap 3) — gap (A) algebraic spine now in the Path-Y `μ²/φ` form

Three axiom-clean commits this lap. The diagonalization spine that gap (A) needs is now expressed in
**exactly the Path-Y `μ²/φ` weight** the Riemann ladder / `S1MainTermDecomp` consume — closing the
weight-convention gap between the diagonalized Selberg form (`φ(r)`) and the ladder (`μ²/φ`).

1. **GPY `y_r`-form diagonalization DONE** (`SieveExpansion.lean`, 4 lemmas). The diagonalized form's
   natural weight is `φ(r)`, but the ladder uses `μ²(r)/φ(r)`. The exact bridge: absorb one `φ(r)` into
   each inner divisor sum, `y_{i,r} := φ(r)·∑_{r∣d}μ(d)gᵢ(d)/d`, giving termwise
   `∑_{d,e}μ(d)g₁(d)μ(e)g₂(e)/[d,e] = ∑_r (μ²(r)/φ(r))·y_{1,r}·y_{2,r}` (squarefree: μ²=1; else
   y_{i,r}=0). Lemmas: `gpy_diagonalize_moebius_bilinear_yform`, `gpy_diagonalize_moebius_yform`,
   `heuristic_main_term_diagonalized_bilinear_yform`, **`heuristic_main_selberg_nu_yform`** (the full
   `∑_{j,j'} cⱼcⱼ'` heuristic main term in `∑_{j,j'} cⱼcⱼ'·M·∏ᵢ ∑_r(μ²/φ)y₁y₂` shape — the spine).
2. **y↔z form bridge DONE** (`gpy_diagonal_yform_eq_zform`): the Path-Y `y_r`-form and the Polymath8b
   `z_r`-form agree (`y_r = (μ(r)φ(r)/r)·z_r`). Cross-validates the new diagonalization and records the
   convention split (z route = PNT/contour; y route = contour-free Mertens).
3. **Antiderivative support viability DONE** (`Antiderivative.lean`, 2 lemmas): the antiderivative-fed
   sieve weight keeps its level-`R` cutoff iff `∫₀¹F=0` (automatic when `F=f'` for a bump `f`).
   `antideriv_eq_zero_of_vanishing`, `antideriv_support_subset` (`support(antideriv F) ⊆ [0,1]`).

### gap (A) — REFINED MAP (the algebraic spine is DONE; what remains is analytic)
The full `s1` chain `sieveSum(selberg_nu) ~ mkF_denominator·norm`:
- **(A1)** `sieveSum = heuristic_main + correction` — DONE (`sieveSum_selberg_nu_eq_heuristic_add_correction`).
- **(A2)** `heuristic_main = ∑_{j,j'} cⱼcⱼ'·M·∏ᵢ ∑_r(μ²/φ)y₁ᵢᵣy₂ᵢᵣ` — **DONE this lap**
  (`heuristic_main_selberg_nu_yform`). The exact `μ²/φ` Path-Y shape, per-coordinate-factorized.
- **(A3) SMOOTHING** `y_{i,r} ≈ (μ(r)/log R)·Fⱼᵢ(log r/log R)` (with the antiderivative convention) —
  **gap (B)**, the deep analytic nut. 1-D core ON ARISTOTLE (`678a9ed6`, brick_smooth). NOTE the
  `1/log R` scale: `y_r = O(1/log R)`, NOT `≈ F` directly — feeding the **antiderivative** 𝔉 (𝔉'=F)
  makes `z_r[𝔉]~(r/φ(r))(1/log R)F` so `y_r[𝔉]~(μ(r)/log R)F`, and `∑_r(μ²/φ)y_r²~(1/log R)∫F²`.
- **(A4) box→simplex + Riemann limit** → `∫_{simplex}F²·norm`. The ladder (`weighted_riemann_kd_muphi`,
  DONE) consumes the SIMPLEX-nested `nestedLogSumW`; (A2)'s output is a BOX product `∏ᵢ∑_{rᵢ∈D}`. They
  reconcile because **F's simplex support kills off-simplex (`∏rᵢ>R`) box terms** — but this couples the
  `j`-sum (F's support lives on the full `∑cⱼ∏Fs`, not individual products). NEXT structural lemma.
- **(A5) correction = o(main)** — **gap (C)**, needs BV/EH. Algebraic split DONE
  (`correction_split_offdiag`, `diag_error_bound`, `correction_abs_bound`); the size bounds
  `∑_{diag}|coeff|=o(main)` + off-diagonal singular-series discrepancy remain.

**Axiom restatement caveat (for whoever wires the antiderivative in):** `s1_holds_from_nonprime_asym`
(Sieve.lean:3024) feeds `selberg_nu k J c Fs` directly → constant is `∫(Fs')²` (landmine, FALSE as
stated). To make it TRUE/provable, the axiom + its 2 consumers (`selberg_sieve_data_from_F`,
`_truncated_from_F`, Sieve.lean:3119/3202) must feed `selberg_nu k J c (fun j i => antideriv (Fs j i))`,
keeping `F=∑c∏Fs` and `mkF_denominator k F` for the witness layer (untouched). `s2` needs the same ν.
This is a flagship-touching refactor — do it deliberately, ideally AFTER brick_smooth validates the
chain end-to-end. `antideriv_support_subset` shows the support survives iff `∫Fs=0` per coordinate
(needs Fs to be a derivative — i.e. M_k-optimal F may need its OWN antiderivative-of-antiderivative, or
the moment condition imposed; OPEN sub-question).

---

## ✅✅ PROGRESS 2026-06-05 (lap 2) — s1 ANALYTIC MAIN TERM PROVEN END-TO-END (general-J, axiom-clean)

Four axiom-clean commits this lap (`bd35abf`…`37b42e6`), full build green (8288 jobs). The entire
`s1` **main term** in `y_r`-space is now machine-checked for the actual sieve test-function shape.

1. **Fubini bridge DONE** (`BoundedGaps/S1Fubini.lean`, `simplex_integral_prod_eq_nestedPhi`):
   `∫_{simplex k} ∏ᵢ gᵢ = nestedPhi (ofFn g) 0` for continuous `g`. Proved locally (beating the
   Aristotle `brick_fubini` job, which independently confirmed the same budget-induction strategy)
   via a **head-outer** simplex fibration `simplex_scaled_fubini_head` over the budget simplex
   `Sieve.simplex_scaled`. ⟹ discharged `hFubini` in
   `S1ConnectionK1.s1_yr_mainTerm_eq_mkF_denominator_sep` (now UNCONDITIONAL).
2. **Signed ladder DONE** (`BoundedGaps/WeightedRiemannSigned.lean`,
   `weighted_riemann_kd_muphi_signed`): the k-D `(μ²/φ)` Riemann limit with **no nonnegativity
   hypothesis**, via `signed_expand` (head split `g = g⁺ - g⁻` composes through cons because the
   per-truncation identity holds at ALL `Q` simultaneously). Needed: the `s1` square has SIGNED cross
   terms `∏(Fs_j·Fs_{j'})`.
3. **General-J main term DONE** (`BoundedGaps/S1MainTermDecomp.lean`,
   `s1_yr_mainTerm_eq_mkF_denominator_decomp`): for `F = ∑_j c_j ∏_i Fs_{j,i}`,
   `(∑_{j,j'} c_j c_{j'}·nestedLogSumW(μ²/φ) R (ofFn(Fs_j·Fs_{j'})) R)/(log R)^k
    → mkF_denominator k F = ∫_{simplex} F²`. **The s1 main term in the exact `hFdecomp` shape.**
4. **Antiderivative + FTC bridge DONE** (`BoundedGaps/Antiderivative.lean`): `antideriv`,
   `contDiff_antideriv`, `mkF_denominator_antideriv_sep`. Implements Trevor's settled antiderivative
   convention (`𝔉' = F`, constant stays `∫F²`).

### What REMAINS to discharge `s1_holds_from_nonprime_asym` (3 deep gaps, all need sieve context)
- **(A) Diagonalization bridge**: connect literal `sieveSum (selberg_nu …) b W x` to the double-sum
  `∑_{j,j'} c_j c_{j'}·nestedLogSumW(μ²/φ) R (ofFn(Fs_j·Fs_{j'})) R`. Algebra largely in
  `SieveExpansion.lean` (`sieveSum_selberg_nu_expand`, `lattice_count_main_term`,
  `gpy_diagonalize_moebius`, `gpy_yvar_substitution`). NEXT local step: trace `sieveSum_selberg_nu_expand`
  → `1/[d,e]` lattice main term → `μ²/φ`-weighted `y_r` double sum.
- **(B) Smoothing `y_r ≈ Fs(log r/log R)`** (Maynard `PartialSummation`/`S1Summation2`): the deep
  analytic nut. 1-D Riemann-sum core ON ARISTOTLE (`678a9ed6`, `brick_smooth`).
- **(C) `alphaMainTerm` normalization** + **o(1) correction** (case (ii) needs BV/EH).

The landmine below is RESOLVED by Trevor's antiderivative decision (constant `∫F²`); see
`archive/findings/ON-LINE-FINDINGS-2026-06-04-gpy-diagonal-asymptotic.md` top.

---

## ✅ PROGRESS 2026-06-05 (lap 1) — the `μ²/φ` `y_r`-space k-D Riemann ladder is DONE (axiom-clean)

The Path-Y analytic engine for `s1` is now built end-to-end, unconditional & axiom-clean, in
`BoundedGaps/WeightedRiemannGen.lean`. Rather than copy the 850-line bare ladder, the WHOLE ladder
was abstracted over an arbitrary nonneg weight `w : ℕ → ℝ` (`weighted_riemann_kd_w`, parametrised by
`0 ≤ w` + `Weighted1DLimit w`), reusing the weight-independent limit side (`nestedPhi`, Pólya, …)
from `WeightedRiemannKD`. Instances landed:
- `weighted_riemann_kd_muphi`: `(∑_{∏rᵢ≤R} ∏Gs_i(log rᵢ/log R)·∏(μ²/φ)(rᵢ))/(logR)^k → ∫_simplex ∏Gs`.
- `weighted_riemann_kd_muphi_sep`: the SQUARED/separable form → `nestedPhi (ofFn Fs²) 0` (the s1 const).
- `weighted_riemann_kd_harmonic`: bare 1/n recovered (validation = identical to `weighted_riemann_kd`).
- 1-D input `weighted1DLimit_muphi` from NEW `WeightedMertens.weighted_mertens_continuous` (μ²/φ
  Mertens extended Lipschitz→continuous via Weierstrass + 3ε; axiom-clean).

**REMAINING to connect to `s1` (the ONLY analytic gap left in the s1 MAIN TERM):** the simplex-Fubini
bridge `∫_{simplex k} ∏gᵢ = nestedPhi (ofFn g) 0`. Once it lands, `S1ConnectionK1`'s
`s1_yr_mainTerm_eq_mkF_denominator_sep` (already a COMPLETE theorem taking it as hyp `hFubini`)
discharges → the k-D s1 analytic main term is PROVEN end-to-end. **PROVEN at k=1**
(`s1_yr_mainTerm_eq_mkF_denominator_one`, axiom-clean). **ON ARISTOTLE 2026-06-05** (job
`58f76560-3dbb-46be-98ee-2bdf4325079c`, brick `/tmp/brick_fubini/Fubini.lean`, still IN_PROGRESS @17min).

Three attack paths for the Fubini bridge (k-induction; the crux is ONE Fubini order-swap because
`SievePolynomial.simplex_fubini` peels with the peeled coord INNER, while `nestedPhi`/`simplexPhi` are
HEAD-recursive = peeled coord OUTER):
1. **Order-swap via product indicator** (most direct): express both `∫_{s∈simplex n}∫_{y∈[0,1-∑s]} f`
   and `∫_{y∈[0,1]}∫_{s∈simplexBudget n (1-y)} f` as `∫` over `[0,1]×simplex n` of `R.indicator f`
   (`R = {(y,s): y≥0, s≥0, y+∑s≤1}`), then `MeasureTheory.integral_integral_swap` (f continuous on
   compact ⇒ integrable). ~60–80 lines; the measurability/integrability of the indicator is the fiddle.
2. **Peel LAST coordinate** (`simplex_fubini (Fin.last n)`) → gives the marginal form
   `∫_{simplex n}(∏ first-n)·(∫₀^{1-∑s} g_last)`; then relate to `simplexPhi` by a SEPARATE 1-step
   swap (smaller, but still a swap). Reuses the `Jᵢ`/marginal machinery shape (`Ji_bridge`).
3. **Generalize the repo's `EpsScaling.monomialIntegral_eq`/`dirichlet_slack` reduction** (it already
   does `∫_{simplex} ∏tᵢ^αᵢ` = iterated, by dimension induction) from monomials to general continuous
   `gᵢ` — the same induction skeleton, integrand abstracted. Likely the least new measure theory since
   that proof already crossed the order-swap for monomials.

## ⚠️ CORRECTNESS RISK (recorded 2026-06-04, from `ON-LINE-FINDINGS-2026-06-04-gpy-diagonal-asymptotic.md`)

**`s1_holds_from_nonprime_asym` (Sieve.lean:3024) is very likely OFF BY A DERIVATIVE — false as
stated — and any attempt to DISCHARGE it will hit this wall.** It currently builds only because it
is a *cited* `axiom` (not proven). The bug:
- `selberg_nu` is built from `lambdaTransform g R n = ∑_{d|n} μ(d) g(log d/log R)` — this is exactly
  Polymath8b's `d`-space `λ_F` (eqn `lambdaf-def`), fed the variational functions `Fs`.
- The axiom claims constant `α = mkF_denominator = ∫_{simplex} F²` (**no derivative**).
- But the `d`-space `λ_F` asymptotic constant is `∫ (∂F)²` (**with a derivative**): Polymath8b
  `c-def` says `c = ∏ ∫ F'_i G'_i` ("F' denotes the derivative of F"); Soundararajan eqn (9) has
  `P^{(k)}`; Maynard §6 final remark: *the variational `F` (∫F²) = the sieve weight `f`
  differentiated in each coordinate.* So feeding the SAME symbol `Fs` to both `λ` and `∫F²` is the
  bug. Off by a derivative.

**Fix = Path Y (recommended, contour-free):** re-target s1 to Maynard's **`y_r`-space** statement,
where the constant genuinely IS `∫F²` and the sums are positive (`μ²/φ`):
`∑_{r≤R,(r,W)=1} (μ²(r)/φ(r)) F(log r/log R)² ~ (φ(W)/W) log R · ∫₀¹ F²` (Maynard Lemma
`PartialSummation` = GGPY Lemma 4). The repo already has the `y_r` substitution machinery
(`SieveExpansion`, ~line 501) and `SharpMertens.sharp_mertens_unconditional` (`∑μ²/φ /log→1`, the
𝔖=1 core) + `WeightedMertens.riemann_sum_log_weight` + the k-D Riemann ladder
(`WeightedRiemann{2,3,K}D`) — exactly the Path-Y composition. **DO NOT** evaluate the signed `z_r`
directly (its `∫F'²` is PNT-strength: `1/ζ(1+w)~w-1`; Polymath8b's proof is a contour). The k-D
Riemann thread below is the Path-Y machinery — NOT wasted, regardless of how the convention is
resolved. Distilled in reference corpus `gpy-sieve-dspace-vs-yspace-convention.md`. Architectural
call (re-target vs restate-as-`∫(∂F)²`) is Trevor's; meanwhile keep building the y_r-space machinery.

---

Last updated: 2026-06-03. Branch `path-a-selberg-nu`.

This file is the actionable inventory. The headline finding this lap **corrects two rounds of
handoffs**: the symmetric-reduction numerical endgame was NOT "just data + `native_decide`". The
committed `gram*Entry` defs enumerate `MarginCorrectTables = univ.filter` over
`CTable = img(α)→img(β)→Fin(k+1)`, i.e. `(k+1)^(cells)` tables — astronomically infeasible for
any real witness. This was verified empirically (an img-3 entry `native_decide`/`#eval` does NOT
finish even at `k=6`). Two reformulations now fix the table **count**; the remaining bottleneck is
precisely diagnosed below.

---

## A. The numerical `Mk k > 4` endgame (main thread)

### Mathematical facts established (Python, exact LDL; `tools/mk/`)
- Infinite-dimensional `M_k` crosses `4` only around `k ≈ 50`. So `k = 50, 54` (the named
  flagships) are razor-thin (`M_54 ≈ 4.0024`) → need a **near-optimal high-degree** polynomial.
  No low-complexity witness exists for them.
- For **larger `k`, lower degree suffices**: at symmetric degree `D = 7` (`#orbits = 45`),
  `M_k(7) > 4` for `k ≳ 200` (`M_200(7) ≈ 4.003`, `M_300(7) ≈ 4.011`). The exact LDL witness at
  `k = 300` has Rayleigh quotient `4.00694 > 4` (a genuine rational certificate). `tools/mk/_ldl.py`
  produces the exact integer orbit-coefficient vector `c`.
- A witness needs orbits with **≥ 3 distinct exponent values** (img ≥ 3): an img≤3-only basis
  never clears `4` (checked `D = 7,9,11`, `k` up to 2000). The 3 img-4 orbits at `D = 7`
  (`[4,2,1]`, `[3,2,1,1]`, `[3,2,1]`) are essential.

### What's DONE in Lean (committed, axiom-clean, verified)
- **`SymmetricReductionOrbitFree.lean`**: `Mk_gt_of_symWeight_witness{,_computable}`,
  `mk_*_of_symWeight*`, the full chain `symWeight → Gram quotient → Mk (n+1) > T`. Sound.
- **Margin-bounded reformulation** (`CTableBdd`, `gram*EntryBdd`, `Mk_gt_of_symWeight_witness_bdd`):
  re-types entries to `Fin (min(rowM,colM)+1)` — img-3 enumeration drops `(k+1)⁹ → (k+1)·2⁸`.
- **Fréchet-windowed reformulation** (`CTableW`, `entryW`, `gram*EntryW`,
  `Mk_gt_of_symWeight_witness_W`): `marginCorrect_frechet` caps the dominant `0`-cell free range at
  `k - max(rowM,colM) = #nonzero-positions ≤ 2·deg`, so the table enumeration is **fully
  k-independent** `∏(window+1)`. Verified correct (`11/3360`, `7/2160` at k=3; agrees with Bdd at
  k=12; img-4 accepted-table count = 43).

### The remaining bottleneck — EMPIRICALLY RE-DIAGNOSED 2026-06-03 (this overturns "factor 1 is gating")
Lap 2026-06-03 BUILT and MEASURED all three factors. Findings (timed `native_decide`/`#eval`):

- **Factor 1 (Fin-k scan) — SOLVED.** Committed `card_filter_ofParts` (Aristotle `656d6b54`) +
  `partsHist k L` (= `L.count v + (v=0 ? k - L.length : 0)`, the k-INDEPENDENT margin, no `Fin k`
  scan). The `WH` layer (`entryWH/MarginCorrectTablesWH/gram*EntryWH` + `gram*EntryWH_eq` bridges,
  `Mk_gt_of_symWeight_witness_WH`) threads margins as explicit `ℕ→ℕ` functions. Measured: an img-4
  enumeration `card` at `k=300` went **>280s (timeout) → 41s** by swapping the `histArr` Fin-k scan
  for `partsHist`. ⚠️ **`histArr` (a `let arr := …scan…; fun v => arr.getD v 0`) does NOT materialize
  under `native_decide`** — it rebuilt the array per lookup (k=30: 125s, k=300: timeout, i.e. cost
  ∝ k). So **never rely on per-entry `let`-materialization in `native_decide`; the margin MUST be
  genuinely k-independent (`partsHist` from the parts list).**
- **THE REAL WALL (new): the windowed table COUNT itself.** An img-4 orbit (4 distinct exponent
  values, e.g. `[4,2,1]`) ⇒ 4×4 = 16 cells ⇒ `univ : CTableW` has `4·2^15 = 131072` tables, and this
  is **k-independent** (can't shrink by lowering k). The margin filter is cheap now, but
  `native_decide` still ENUMERATES all 131072 per entry (~41s for the card alone). The 3 essential
  img-4 orbits (`[4,2,1]`,`[3,2,1,1]`,`[3,2,1]`) give 9 img-4×img-4 entries at ~41s+ each
  (+factorials) ⇒ the full 45-orbit witness is ~tens of min–hours and likely OOM/too-slow even on a
  host. img-4 is mathematically REQUIRED (img≤3 bases never clear 4, checked `D=7,9,11`,
  `tools/mk/img3only.py`). **Windowing fixed the 0-cell range but NOT the 2^(#offdiag-cells) blowup.**
- **Factor 3 (bignums) — partially handled, not the gate.** Per accepted table, the column multinomial
  `Nat.multinomial univ (fun v => entryW…)` sums to the 0-column margin (~297 at k=300) ⇒ `297!`.
  `multinomialFast` (Aristotle `f84ef793`, committed in `MultinomialFast.lean`, kernel-clean) routes
  this through `Nat.choose` (Pascal). ⚠️ but `Finset.toList` is **noncomputable**, so
  `multinomialFast f s.toList` can't be used in a `native_decide` def directly — need a COMPUTABLE
  fast multinomial. Aristotle job `3591b35b` (`aristotle-multfold/`) is proving `multFold` (via
  `Finset.fold` of binomials = `Nat.multinomial`). ALSO note `Nat.choose`'s naive Pascal recursion is
  itself slow for *balanced* args — prefer the `descFactorial` form (matchings, below).

### THE path forward: A.2 matchings closed form is now the ONLY box-feasible route
Because the table COUNT (not the per-table work) is the wall, the enumeration must be REPLACED by a
sum that is small AND k-independent. That is the **matchings closed form** (`tools/mk/mk_sym.py`,
function `_entry_sums`/`reduced_closed`, validated vs brute + the Lean `11/3360` spot-check):

    gramDenEntry lam mu = (1/(aut lam · aut mu)) · (∑_M ff(k,T_M) · W(M)) / (k+|lam|+|mu|)!
    gramNumEntry lam mu = (1/(aut lam · aut mu)) · (∑_M ff(k,T_M) · W(M) · (Gocc(M)+(k-T_M)·g(0,0)))
                            / (k+|lam|+|mu|+1)!
  where (lam,mu = the NONZERO parts lists; rl=|lam|, rm=|mu|):
    M       ranges over partial matchings pairing some lam-parts with some mu-parts (t pairs,
            t=0..min(rl,rm); choose t-subsets of each + a bijection) — count is k-INDEPENDENT, ~34
            for rl=rm=3.
    T_M     = rl + rm − |M|   (occupied slots)
    ff(k,T) = k·(k−1)···(k−T+1) = `k.descFactorial T`   (T ≤ 2·deg ≤ 14 — a CHEAP product, no factorial)
    W(M)    = ∏_{paired (a,b)} (lam_a+mu_b)! · ∏_{lam-only a} lam_a! · ∏_{mu-only b} mu_b!
    aut(lam)= ∏_v (mult of value v in lam)!
    g(a,b)  = (a+b+2)!/((a+1)(b+1)(a+b)!);  g(0,0)=2
    Gocc(M) = ∑ over occupied tokens of g(content): paired→g(lam_a,mu_b), solo→g(lam_a,0)/g(0,mu_b)
  ⇒ ~34 cheap terms/entry, ONE factorial/entry, descFactorial only ⇒ full witness `native_decide`
  in milliseconds, AND makes the flagships k=50/54 (degree ~20) feasible too.

**LANDED (committed `ca3d47f`):** the matchings-form DEFS + WITNESS are in
`SymmetricReductionOrbitFree.lean`: `matchData/matchDenSum/autParts/matchDenForm` (denominator),
`gWeight/matchDataN/matchNumSum/matchNumForm` (numerator), `#eval`/`native_decide`-INSTANT even at
k=300 img-4; numerically validated (`11/3360`, `7/2160` = the Lean spot-checks).

**LANDED 2026-06-03 (commits `c9cb696`, `8d46bcd`, `ef2b071`, `8a5a6ba`):** both bridges are now
**THEOREMS**, and the witness is re-keyed on parts-lists. The two A.2 pieces collapsed to:

1. **Bridges PROVEN modulo two atomic combinatorial cores.** `gramDenEntry_eq_matchDenForm` /
   `gramNumEntry_eq_matchNumForm` are no longer axioms — they're theorems. All surrounding plumbing
   is discharged in-kernel: `gramDenEntry = orbit-sum/(k+|α|+|β|)!` (`orbitPair_denominator_
   computable` ∘ `orbitPair_denominator_eq`), the numerator analog (`crossNumerator_orbitSum` ∘
   `orbitPair_numerator_eq` ∘ `numerator_combinatorial_factored`, `markedCellFactor_eq_gWeight`),
   `ofParts_degree` (= `L.sum`), and the `autParts>0` cancellation. The two **atomic** permanent/rook
   identities were `denom_bridge` / `num_bridge`. **STATUS 2026-06-03 (commits `b8fd8f5`, `d18ca93`):
   BOTH ELIMINATED as deep axioms.**
   - **`denom_bridge` — FULLY PROVEN (axiom gone).** Discharged via the **permanent route** (NOT the
     orbit-recursion P2 below). Define `permDenSum La Lb k = ∑_{ρ∈Perm(Fin k)} ∏ᵢ(ofParts La i +
     ofParts Lb(ρ i))!`. Then `lhs_eq_perm` (orbit double-sum·(k-|La|)!(k-|Lb|)! = k!·permDenSum, via
     the proven `ofParts_autParts_orbit_sum`) and `rhs_eq_perm` (matchDenSum·(...) = k!·permDenSum, by
     induction on `La`) share `permDenSum` and cancel. The hard core `permDenSum_laplace` (the inner
     perm-sum after `permDenSum_cons`/decomposeFin collapses to permDenSum on the column-removed list)
     was cracked via: swap↦succAbove perm bridge (`Fin.exists_succAbove_eq`), `permSum_perm_invariant`,
     and the EXACT identity `ofParts Lb ∘ Fin.succAbove j = ofParts (eraseIdx j)` (`ofParts_comp_succAbove`).
     Also `descFactorial_succ_eq'` (UNCONDITIONAL) makes `matchDenSum_cons_eq'` unconditional.
   - **`num_bridge` — FULLY PROVEN (axiom gone), incl. `matchNumSum_cons_eq'` (commit `6d8e23f`).**
     Same permanent route, ℚ-valued, with the extra `∑ᵢ gWeight(pᵢ,qᵢ)` factor. `permNumSum`,
     `permNumSum_cons` (`Fintype.sum_prod_type`), `permSum_gw_invariant`, `inner_num_eq`/`inner_den_eq`,
     `permNumSum_laplace` (j-row gWeight term splits into permDenSum + permNumSum), `lhs_num`,
     `rhs_num` (induction: IH for num + the proven `rhs_eq_perm` for den), `num_bridge`. The
     `matchNumSum_cons_eq'` recursion proved via unmatched/matched branch split + per-entry `weight_elt`
     + `matchDenSum_dataN` (helpers: `list_sum_flatMap`, `sum_range_eq_list`, `zip_range_eq_map`).
   - **`Mk_200_gt_4` is AXIOM-CLEAN: `[propext, Classical.choice, Quot.sound, native_decide]`** — NO
     mathematical axioms remain. The entire symmetric-reduction → Gram-quotient → matchings chain is
     kernel-proven (native_decide only for the concrete k=200 witness computation). NOTHING left to do
     here; the broader `bounded_gap_of_Mk_200` rests on cited analytic NT (§B) owned by another thread.
2. **Re-keying DONE** (`ef2b071`): `Mk_gt_of_symWeight_witness_match_parts (LCs : List (List ℕ × ℚ))`
   — the Gram quotient is the DIRECT list-form double sum `(LCs.map (fun la => (LCs.map (fun lb =>
   la.2·lb.2·matchForm la.1 lb.1 (n+1))).sum)).sum`; no 45-way `MultiIndex` match. Reduces to
   `…_witness_match` via `R = (LCs.map (ofParts∘fst)).toFinset` + noncomputable `partsInv`/`coefInv`
   (`ofParts` inj on `LCs` by `hnodup`; reindex via `List.sum_toFinset`×2). k=3 regression
   (`8a5a6ba`) fires the `native_decide` on the list-form quotient end to end.

(Superseded note — the OLD 2-pieces, for history:)
- ~~Prove the 2 bridge axioms (orbit-sum = matchings-sum, permanent/rook over `S_k`).~~ → now atomic
  `denom_bridge`/`num_bridge`, plumbing done, on Aristotle.
- ~~Re-key the witness on parts-lists / `Fin 45`.~~ → DONE (`…_witness_match_parts`). Measured prior:
   `Mk_gt_of_symWeight_witness_match` sums over `R : Finset (MultiIndex (n+1))` with `c, P` as
   functions on `MultiIndex` — evaluating `c a`/`P a` per summand requires a 45-way match over
   200-entry functions (`#eval` of the full witness CRASHED, code 134 / ~7e9 lookup ops). FIX: a
   variant `…_parts (Ls : List (List ℕ)) (cs : List ℤ) …` whose sum is `∑ i j, cs[i]·cs[j]·matchForm
   Ls[i] Ls[j] (n+1)` (DIRECT indexing, no `MultiIndex` matching), related to `∑ over R = (Ls.map
   ofParts).toFinset` (dedup + `ofParts` injectivity + orbit-disjointness from distinct parts-lists).
   This also subsumes the old "margin materialization" fix (margins `partsHist (n+1) Lᵢ`, Lᵢ in hand).

### The capstone payoff — ✅ DONE ON-BOX 2026-06-03 (commits 72f80c3, fff0e29)
**`BoundedGaps.OrbitFree.Mk_200_gt_4 : (4:ℝ) < Sieve.Mk 200`** is LANDED in
`BoundedGaps/MkWitness200.lean` (built by the default target, full build 8271 jobs). It instantiates
`Mk_gt_of_symWeight_witness_match_parts` with the exact k=200 D=7 witness `witnessLCs200` (45 orbits,
exact-LDL coeffs, rational Rayleigh quotient 4.002898). **First kernel-checked `M_k > 4`.**
`#print axioms Mk_200_gt_4 = [propext, Classical.choice, Quot.sound, native_decide]` (2026-06-03,
commit `6d8e23f`: both `denom_bridge` and `num_bridge` are now FULLY PROVEN theorems — NO
mathematical axioms remain; native_decide only for the concrete k=200 witness).

The companion **`bounded_gap_of_Mk_200`** feeds it into `Targets.H1_le_of_Mk_witness` →
`∃ H, Admissible H ∧ H.length = 200 ∧ liminfGap 1 ≤ diameter H` — the first **unconditional**
bounded-gap result in the repo (vs `Targets.H1_le_246`, which is conditional on the unproven
`Mk 50 > 4`). It rests on `[3 std, denom_bridge, num_bridge, BombieriVinogradov,
exists_separable_F_of_Mk_gt, s1/s2_holds_*, native_decide]` — the bridges + cited analytic NT only.

**❗ The "HOST-only / box OOMs" claim in every prior handoff was WRONG.** The failure was
`deep recursion at 'interpreter'` (interpreter stack used in native_decide/decide setup), NOT OOM.
Fix: `weakLeanArgs = ["--tstack=2000000"]` on `[[lean_lib]]` in `lakefile.toml` (weak ⇒ no full
rebuild). The matchings closed form is genuinely cheap; all three native_decides + two decides run
on-box in ~50s. **Do not re-assume host-only for heavy native_decide — bump tstack first.** When the
two bridge axioms land (Aristotle `0b5bf5be`/`9d05dbaa`), this is a fully kernel-clean (mod
native_decide) `M_200 > 4` → unconditional bounded gaps.

~~The numeric diameter in `bounded_gap_of_Mk_200` is the cheap factorial tuple's (`199·200!`).~~
**✅ GILDED 2026-06-04 (commit `60cd99c`).** `bounded_gap_of_Mk_200` now uses the explicit narrow
admissible 200-tuple `tuple200` (diameter **1304**, greedy residue-sieve, proven admissible via the
Engelsma `checkAdm` bundled-`native_decide` pattern). New: `liminfGap_one_le_1304 : liminfGap 1 ≤
1304` (the concrete H_1 bound) and `narrowness_200_le_1304 : H(200) ≤ 1304`. `Mk_200_gt_4` stays
axiom-clean; `bounded_gap_of_Mk_200` rests only on the 4 analytic-NT axioms (BV, exists_separable_F,
s1/s2) + native_decide.

Witness data IN HAND (`tools/mk/_ldl.py`, exact LDL): k=200 D=7 ratio 4.002898, k=300 ratio 4.006944,
45 orbits each, ~100-digit integer orbit coeffs (regenerate via `PYTHONPATH=. python3` over
`partitions_upto(7)` + `reduced_closed(orbs,K)` + the `ldl_inertia` witness). So `(R,c)` is ready;
only the FEASIBLE entry evaluation (A.2) is missing.

**No small-witness shortcut** (`tools/mk/subset.py`): greedy 31/45 orbits → 3.78; full 45 → 4.011.
Need ~all 45 orbits incl. the 3 essential img-4 orbits. ⇒ **A.2 (matchings closed form) is now the
gating step** — A.1 (filter-card hoist) is DONE but insufficient: the windowed table COUNT
(`~131072` per img-4 entry, k-independent), not the per-table cost, is the wall.

The named flagships (`mk_54_witness_under_EH`, `mk_eps_50_witness`) need `k=50/54` at degree ~20+
(n ~ 600 orbits) — even with the above, much heavier; **host-better** and a separate push.

---

## B. Other open axioms (status / why deferred)

- **`Prerequisites.geh_implies_eh`** (`sorry`): needs a faithful `GEH` body (still opaque `axiom`)
  + Vaughan's identity to rebuild `Λ` from Type I/II convolutions. Multi-session; deferred.
- **`exists_separable_F_of_Mk_gt` — FULLY DISCHARGED 2026-06-04 (commits `153505b`, `d9b4632`).**
  Was a cited deep Polymath8b §6 polynomial-optimisation axiom (one of the 4 gating the UNCONDITIONAL
  `bounded_gap_of_Mk_200`). Now a **fully axiom-clean THEOREM** (`[propext, Classical.choice,
  Quot.sound]`), as is the pure-density `separable_dense_sup` it rested on — discharged in-kernel by
  the **box-tensor construction**: inward centroid expansion `E t = b + r(t−b)` (`b=(1/(k+1))ᵢ`,
  `r=1+modulus mesh`) gives `F₁=F∘E` with support strictly interior (margin `≥(1−r⁻¹)/(k+1)` per
  face) and `|F−F₁|≤δ/2`; box-tensor `G=∑_φ F₁(c_φ)·∏ meshBump h (φ i)` is separable+smooth with
  `|F₁−G|≤δ/2`; margin > mesh keeps support(G)⊆simplex. **`bounded_gap_of_Mk_200` axiom set: 4→3**
  (now `[BombieriVinogradov, s1_holds_from_nonprime_asym, s2_holds_from_prime_asym_under_EH] +
  native_decide`). The ε family (`separable_dense_sup_eps`, `epsilon_trick`) AND the truncated family
  (`separable_dense_sup_truncated`, `exists_separable_F_truncated_of_Mk_truncated_gt`) are ALL now
  axiom-clean too — the entire `separable_dense_*` family is machine-checked. Reusable in-kernel cores
  landed: `abs_sub_weighted_average_le`, `meshBump`/`_nonneg`/`_contDiff`/`_partition`/`_support`,
  `box_tensor_approx`, `exists_uniform_modulus`. **Aristotle sepdense `c46a7778` was a DEAD END**
  (submitted with `ContDiff ℝ ⊤` = C^ω analytic ⟹ vacuous; our axiom is `ContDiff ℝ ∞` = C^∞; see
  memory `sepdense-aristotle-deadend`). ▼ OLD narrowing notes (superseded, kept for history): ▼
- ~~**`exists_separable_F_of_Mk_gt` — NARROWED 2026-06-04 to a single pure-density axiom.**~~ Was a
  cited deep Polymath8b §6 polynomial-optimisation axiom (one of the 4 gating the UNCONDITIONAL
  `bounded_gap_of_Mk_200`). Now a THEOREM resting only on **`separable_dense_sup`** (sup-norm
  density of finite-separable smooth simplex-supported functions — pure approximation theory, NO
  number theory). The chain (all in `Sieve.lean`, axiom-clean except the lone density axiom):
  `exists_separable_F_of_Mk_gt` ⟸ `exists_F_of_Mk_gt` (proven `sSup` extraction) + `sep_approx`
  (now a theorem) ⟸ `mkF_sub_lt_of_sup_le` (the MkF-ratio sup-continuity, **fully kernel-clean**:
  num/den sup-continuity `mkF_{numerator,denominator}_sub_le_const` via `J_i_sub_le_const` /
  `Ji_integrand_integrableOn` + quotient rule) + `separable_dense_sup` (the density nut).
  `#print axioms exists_separable_F_of_Mk_gt = [propext, Classical.choice, Quot.sound,
  separable_dense_sup]`. **Truncated sister also narrowed** (`separable_dense_sup_truncated`, reuses
  the same continuity).
  - **ε sister FULLY DONE (2026-06-04):** (1) ported the continuity machinery to the ε-domains
    (`mkF_eps_sub_lt_of_sup_le` axiom-clean: `Ji_eps_integrand_integrableOn`, `J_i_eps_sub_le_const`,
    `mkF_eps_{num,den}_sub_le_const`; inner length `L=1+ε−∑s≤1+ε`, requires `0≤ε`), making
    `sep_approx_eps` a theorem; (2) then ELIMINATED the eps density axiom: `separable_dense_sup_eps`
    is a THEOREM reducing to base `separable_dense_sup` via the dilation `simplex_eps k ε =
    (1+ε)•simplex k` (`Measure.setIntegral_comp_smul_of_pos` Jacobian, `Module.finrank_fin_fun`).
    `epsilon_trick` now rests on `separable_dense_sup`, not a separate _eps axiom (Sieve axioms 11→10).
  - **REMAINING NUT — `separable_dense_sup`** (+ `_truncated`: per-coord cap `t i ≤ α`, so does NOT
    reduce by dilation — shares the same wall). Intended proof = SEPARABLE box-tensor:
    `G(t) := ∑_{φ:Fin k→I} F(c_φ)·∏_i ρ_{φ(i)}(t_i)`, `{ρ_m}` a 1-D smooth partition of unity (mesh h).
    **FOUR reusable in-kernel CORES landed this lap (all axiom-clean), decomposing the wall:**
    1. `tensor_partition_of_unity` (per-coordinate form): if `∀ i, ∑_m ρ_m(t_i)=1` then
       `∑_φ ∏_i ρ_{φ i}(t_i)=1` (via `Fintype.prod_sum` + `Finset.prod_congr`). The per-coord
       hypothesis composes directly with a finite 1-D PoU valid on a range.
    2. `isFiniteSeparable_tensor_sum`: any finite tensor sum `∑_φ a(φ)∏g(φ i)(t_i)` IS
       `IsFiniteSeparable` (`Fintype.equivFin` reindexing).
    3. `smoothTransition_finite_partition`: the 1-D smooth PoU itself —
       `∑_{m=0}^{N}(σ(x−m)−σ(x−(m+1)))=1` on `[1,N+1]`, `σ=Real.smoothTransition` (telescoping
       `Finset.sum_range_sub'`). Each bump smooth, supp `⊆[m,m+2]`.
    4. `contDiff_tensor_sum`: the tensor sum is `C^∞` when each `g_m` is (`ContDiff.sum`+`contDiff_prod`).
    **So separability ✓, smoothness ✓, PoU-sums-to-1 ✓ are all in-kernel.** RESIDUE = two analytic
    glue steps only: (i) the **modulus-of-continuity sup-bound** `|F t − G t| ≤ δ` (uniform continuity
    of `F` on the compact simplex via `IsCompact.uniformContinuousOn`; relate `∏ρ_{φ}(t)≠0` ⟹ `c_φ`
    within mesh of `t`); (ii) **support(G) ⊆ simplex** via an **inward dilation** `F((1+η)·)` (shrinks
    supp strictly inside the open simplex, gap `≥` mesh ⟹ active bump-boxes stay in simplex;
    `F((1+η)·)→F` uniformly — same dilation trick as the eps reduction). Attack paths for the glue:
    (a) finish the assembly locally (define G with mesh `1/M`, `I=Fin(M+2)`, rescale the 1-D PoU
    `x↦M·x+1`); (b) **Aristotle** — job `c46a7778` (sepdense) grinding the base case (verify
    `#print axioms` on return, port onto the 4 cores).
- **Other Sieve bridges** `s1/s2_holds_from_*` (`Sieve.lean`): the GPY/Maynard asymptotic sieve
  sums. Deep analytic NT (leaf 1 = GPY port, paper-gated for the constant; see §Z).
- **`BombieriVinogradov`, `GEH`, `GeneralizedBombieriVinogradov`, `MPZ_polymath8a`**
  (`Prerequisites.lean`): genuine external analytic-NT inputs; cite-only until mathlib/PNT+ ships.
- **`narrowness_*_ge_*`** (Clark–Jarvis 2001 exhaustive enumeration) and **`narrowness_*_le`** for
  large `k` (Hensley–Richards constructions, `k` up to `3.5e9`): combinatorial, out of scope at
  scale. `narrowness_5511_le` is done (Aristotle-assisted `native_decide`).
- **`Zhang.H1_le_70M`** (`sorry`): Zhang's method-faithful GPY+MPZ sieve; result already free via
  `Polymath8b.H1_le_246`. Deferred.
- **`Polymath8b.twin_primes_or_near_miss_Goldbach`** (`sorry`): §8, weeks of work. Deferred.

---

## C. Aristotle (status 2026-06-04, lap ~05:40Z)

### 🏆🏆 GATE DISCHARGED — `∑μ²/φ = Θ(log N)` is now FULLY UNCONDITIONAL (commit `e8b00d7`).
Proved the prime-power tail bound `∑_{n≤N, IsPrimePow ∧ ¬Prime} Λ(n)/n ≤ 3` **from scratch**
(NOT via Aristotle — beat the `3f137191` job to it), discharging the last gate:
- `tail_eq_kge2`: `Chebyshev.sum_PrimePow_eq_sum_sum` regroups the tail as
  `∑_{k=2}^{⌊logN/log2⌋} ∑_{p≤⌊N^{1/k}⌋}(log p)/p^k` (filter-split off the k=1 primes).
- `tail_kge2_le ≤ 3`: **widen each k-slice's prime range to [2,N]** so the `k,n` ranges become
  independent → `Finset.sum_comm` (NO hard interdependent Fubini!) → `geom_tail_le`
  (`∑_{k≥2}n^{-k} ≤ 1/(n(n-1)) ≤ 2/n²`) → `sum_log_div_sq_le` (`∑(log n)/n² = O(1)`, integral cmp).
- `prime_power_tail_le_three`, then UNCONDITIONAL: `mertens_prime_log_two_sided`
  (`|∑(log p)/p − logN| ≤ log4+7`), **`mertens_theta_log`** (`log N ≤ ∑μ²/φ ≤ exp(1+D)·log N`),
  `mertens2_two_sided` (`∑1/p = loglog N + O(1)`, coeff 1). ALL `#print axioms` clean, no sorry.
- **Aristotle `3f137191` (pptail, proving `≤ 1`) is now SUPERSEDED** — `≤ 3` suffices for O(log N).
  If it returns `≤ 1` it only tightens constants (log4+7 → log4+5); not needed. Free the slot for
  the next rung when it finishes.
- **NEXT RUNG (new top priority):** connect `mertens_theta_log` to the GPY singular-series
  asymptotic that gates `s1_*_holds_from_nonprime_asym` in `Sieve.lean` (the actual consumer).
  Big jump — needs sieve context; read `ANALYTIC_AXIOM_BURNDOWN.md` + Sieve.lean s1 statement.

### EARLIER THIS LAP (~04:30–05:00Z, 11 commits `12e307e`…`f779d0c`, all axiom-clean):
**The ENTIRE sharp chain to the headline `∑μ²/φ = Θ(log N)` is now BUILT, reduced to a SINGLE
remaining gate: `prime_power_tail_le` (in flight `3f137191`).** New in `BoundedGaps/Mertens.lean`:
- `vonMangoldt_split_prime`: `∑Λ(n)/n = ∑_{p≤N}(log p)/p + (proper-prime-power tail)`.
- `mertens_prime_log_two_sided_of` (+`_upper_of_tail`): tail≤1 ⇒ `|∑(log p)/p − log N| ≤ log4+5`.
- **Sharp Mertens 2nd, BOTH halves (coefficient 1):** `mertens2_abel` (2nd Abel identity, weight
  `1/log n`), helpers `log_telescope_eq/_le`, `leading_term_bound/_ge`, `reindex_inv_log`,
  `leading_sum_bound/_ge`, `sum_one_div_n_log_n_ge`; `mertens2_upper_of`/`mertens2_lower_of`
  (`A_n = log n ± C ⇒ ∑1/p = loglog N ± O(1)`); `mertens2_two_sided_of_tail` (bundled textbook
  `∑1/p = loglog N + O(1)` conditional on tail).
- **Headline:** `prime_idx_eq`, `prod_euler_le_exp` (`∏(1+1/(p-1)) ≤ exp(∑1/(p-1))`),
  `euler_exponent_le` (`∑1/(p-1) ≤ ∑1/p+1`), `mertens_upper_of` (`∑μ²/φ ≤ exp(1+D)·log N = O(log N)`),
  `mertens_theta_log_of_tail` (two-sided `Θ(log N)` ⟸ tail). **All ONE `exact` from unconditional.**
- **mathlib unlock for the tail:** `Chebyshev.sum_PrimePow_eq_sum_sum` IS the prime-power regrouping
  `∑_{n≤x, IsPrimePow} f(n) = ∑_{k=1}^{⌊log x/log2⌋} ∑_{p≤x^{1/k}} f(p^k)` — confirms the tail is
  tractable (k=1 slice = primes; tail = k≥2 slices). Aristotle has the right tool.

### THE ONE REMAINING GATE: ✅ DISCHARGED (see above) — `prime_power_tail_le_three` is real.
- `3f137191` (pptail `≤ 1`) superseded; the conditional `*_of_tail` theorems remain as documentation
  of the dependency structure but are no longer needed (unconditional versions exist).
- **🎉 SHARP MERTENS 1st LANDED this lap** (`7412132`): `mertens_vonMangoldt_two_sided`
  `|∑_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4` — the **coefficient-1** estimate. Built from
  `vonMangoldt_hyperbola` (Aristotle `cc0dfbaf`), `sum_log_le`/`le_sum_log` (Stirling via mathlib
  `integral_log`), `cast_div_le_self`/`sub_one_le_cast_div` (floor), and **mathlib's
  `Chebyshev.psi_le_const_mul_self`** (`ψ(N) ≤ (log4+4)N` — the hard ψ≤CN bound is ALREADY in
  mathlib's `Mathlib/NumberTheory/Chebyshev.lean`!). `mertens_vonMangoldt_lower`/`_upper` are the halves.
- **REMAINING sharp chain → headline `∑μ²/φ = Θ(log N)`:**
  1. prime-power tail (in flight `3f137191`) ⇒ **sharp** `∑_{p≤N}(log p)/p = log N + O(1)`.
  2. **sharp Mertens 2nd** `∑_{p≤N} 1/p = log log N + O(1)` (coefficient 1): 2nd Abel step on the
     SHARP `∑(log p)/p` via `abel_summation_identity`. ⚠️ NOTE: `mertens_second_term_bound` is for the
     CRUDE route (bounds `(1+log n)(…)` wholesale → coeff `1+1/log2`). For coeff-1, SPLIT
     `A_n(1/log n − 1/log(n+1)) = log n·(…) + (A_n − log n)·(…)`: leading `log n·(1/log n−1/log(n+1))`
     sums to `log log N + O(1)` (coeff 1, via `sum_one_div_n_log_n_le`), remainder `(A_n−log n)·(…)`
     is `O(1)·∑(1/log n − 1/log(n+1))` which TELESCOPES to `O(1)`. Needs sharp `A_n = log n + O(1)`.
  3. `∑_{p≤N} 1/(p−1) ≤ ∑1/p + 1` (`prime_tail_le`, landed) + `1+x≤eˣ` ⇒ `∏(1+1/(p−1)) = O(log N)`
     (now coeff-1 ⇒ genuine `O(log N)`, NOT the crude `(log N)^3.4`) ⇒ `∑μ²/φ = O(log N)` ⇒
     two-sided `Θ(log N)` with `mertens_lower`.
- **LANDED THIS LAP (17 commits `a2e4c60`…`7412132` on `path-a-selberg-nu`, all axiom-clean,
  full build green 8272 jobs):** the complete 1D-analytic toolkit in `BoundedGaps/Mertens.lean`:
  - sharp Mertens 1st: `vonMangoldt_hyperbola`, `sum_log_le`, `le_sum_log`, `cast_div_le_self`,
    `sub_one_le_cast_div`, `mertens_vonMangoldt_lower/_upper/_two_sided`.
  - `mertens_prod_upper`/`mertensSummand_eq_prod` (`∑μ²/φ ≤ ∏(1+1/(p-1))`), proved locally.
  - `chebyshev_theta_le`/`chebyshev_theta_le'` (`θ(N) ≤ N·log 4`, plain + indicator form).
  - `abel_div_le` (Aristotle `32baa99f`, weight `1/n` summation-by-parts) + `mertens_first_le`
    (`∑_{p≤N}(log p)/p ≤ log4·(1+log N)`) + `mertens_first_le'` (indicator form).
  - `telescope_tail_eq/le`, `prime_tail_le` (`∑_{p≤N}(1/(p-1)−1/p) ≤ 1`).
  - `hasDerivAt_log_log`, `continuousOn/antitoneOn_one_div_x_log_x`, `integral_one_div_x_log_x`
    (FTC: `∫_2^N 1/(x log x)=log log N−log log 2`), `sum_one_div_n_log_n_le` (sum-integral comparison).
  - `abel_summation_identity` (Aristotle `431512dd`, GENERAL-weight summation-by-parts).
  - `mertens_second_term_bound` (`(1+log n)(1/log n−1/log(n+1)) ≤ (1+1/log2)/(n log n)`).
- **⚠️ KEY INSIGHT (sharp vs crude).** The `abel_div_le`-based route gives Mertens 1st with a LOSSY
  `log 4 ≈ 1.386` coefficient (from Chebyshev `θ≤N log4`), so the second Abel step yields only
  `∑1/p ≤ C·log log N` with NON-SHARP `C = log4·(1+1/log2) ≈ 3.4`. Exponentiating gives
  `∑μ²/φ = O((log N)^{3.4})`, **NOT** the sharp `Θ(log N)`. The two-sided `∑μ²/φ ~ log N` (needed
  for sub-step (c)'s main term) requires the SHARP Mertens 1st `∑(log p)/p = log N + O(1)`
  (coefficient exactly 1), via the von Mangoldt / `log(N!)` / Stirling route — hence the `cc0dfbaf` job.
- **NEXT bricks — two tracks:**
  - **(crude, ~80 lines, OPTIONAL milestone)** Assemble qualitative **Mertens 2nd** `∑_{p≤N}1/p = O(log log N)`
    from the landed pieces: `abel_summation_identity` with `a k=[k prime](log k)/k`, `w k=1/log k`
    (⇒ `a k·w k=[k prime]/k`); `A_n` bounded by `mertens_first_le'`; split off n=1 (A₁=0, junk weight);
    bound the difference-sum termwise via `mertens_second_term_bound` then `sum_one_div_n_log_n_le`
    (mind the `Icc 2 (N-1)` vs `Ico 2 N`/`n=3..N` index shift, +`1/(2log2)` for the n=2 term).
    Famous theorem, but non-sharp constant — does NOT give the headline `∑μ²/φ=Θ(log N)`.
  - **(SHARP, the real headline path)** von Mangoldt route: `vonMangoldt_hyperbola` (in flight) →
    Stirling `N log N−N+1 ≤ ∑_{m≤N}log m ≤ N log N` (use mathlib `integral_log` +
    `MonotoneOn.integral_le_sum`; ALL tooling present) → `⌊N/n⌋=N/n−frac`, ψ(N)=∑Λ(n)≤C·N
    (Chebyshev) → `∑Λ(n)/n = log N + O(1)` → drop prime-power tail (`∑_{k≥2}(log p)/p^k` converges)
    → SHARP `∑(log p)/p = log N+O(1)` → sharp Abel (reuse `abel_summation_identity`) → `∑1/p=log log N+O(1)`
    → `∑μ²/φ = Θ(log N)`. mathlib has `ArithmeticFunction.vonMangoldt_sum`, `vonMangoldt_apply_prime`,
    `vonMangoldt_le_log`, `Stirling.le_log_factorial_stirling`.
- **DONE+ported 2026-06-04 — `6c45fd6b` `mertens_crux`** (the analytic on-ramp's nut): returned
  sorry-free, verified + ported into `BoundedGaps/Mertens.lean` as part of `mertens_lower`
  (`log N ≤ ∑ μ²/φ`), `#print axioms = [propext, Classical.choice, Quot.sound]`. One `grind`
  regression (radical(p^k)=p) hand-fixed; mathlib v4.29.1 DOES have `radical`.
- **DONE+ported (earlier): the two bridge cores.** `0b5bf5be` denom_bridge, `9d05dbaa` num_bridge —
  both eliminated (handoff `d977260`); `Mk_200_gt_4` axiom-clean.
- DONE+ported (earlier): `f84ef793` multinomialFast (→ `MultinomialFast.lean`); `656d6b54`
  card_filter_ofParts (→ re-proved). `3591b35b` multfold = dead path (enumeration abandoned).
- After both bridges land: the ONLY remaining gap to a kernel-checked `Mk 200 > 4` is the heavy
  capstone `native_decide` on `Mk_gt_of_symWeight_witness_match_parts witLCs … ` — likely HOST-only
  (2025 matchForm terms, 214! factorials; box OOMs). The witness `LCs` literal still needs to be
  generated from `tools/mk/_ldl.py` (k=200 D=7, 45 orbits) and `#eval`-checked > 4 (fast, computable).
- **NEW — analytic-NT burn-down track (2026-06-03), for the fleet to pick up in due course:**
  `6c45fd6b-3757-4a2c-87ba-059478d10cff` (`mertensSummand`/`mertens_crux`) — the entry lemma for the
  s1/s2 sieve-asymptotic burn-down: `∑_{n≤N} 1/n ≤ ∑_{n≤N} μ²(n)/φ(n)` (radical-fiber/Euler-product
  rearrangement; mathlib has no `radical:ℕ→ℕ` nor `∑∏=∏∑` over `primeFactors`). On return: verify
  in-kernel + `#print axioms` (Aristotle pins v4.28; we're v4.29.1), then it discharges the lone
  real `sorry` in the skeleton `scratch_mertens.lean` (repo root, untracked, typechecks — the endpoint
  `log N ≤ harmonic N` already compiles via `log_le_harmonic_floor`). **Full map of why this matters and
  the whole analytic-axiom ladder (BV / Large Sieve / s1/s2 / PNT) is in `ANALYTIC_AXIOM_BURNDOWN.md`.**
  A NEW, EH-free, weeks-scale on-ramp — independent of the `Mk` main thread above.

---

## Z. Analytic-NT burn-down thread (s1/s2 via weighted Mertens) — added 2026-06-04 PM

Separate from the numerical `Mk` endgame above. State after this lap: front #4 (1-D weighted
Mertens) **reduced to ONE analytic axiom**; 8 axiom-clean lemmas + full Abel reduction in
`BoundedGaps/WeightedMertens.lean`. Build green (8276 jobs).

### Open items (this sub-thread)
- **`WeightedMertens.riemann_sum_log_weight`** — the ONLY axiom under `weighted_mertens`. Pure
  real-analysis Riemann-sum limit `(∑_{2≤n≤N}F(log n/log N)/n)/log N → ∫₀¹F`.
- **`Sieve.s1_holds_from_nonprime_asym`**, **`s2_*`** — multidimensional generalization of weighted
  Mertens (the genuine multi-month nut: singular series + simplex integral).
- **`Sieve.exists_separable_F_*`** — near-optimal separable `F` (Polymath8b §5-6).
- **`Prerequisites.geh_implies_eh`** (`sorry`) — needs GEH body + Vaughan's identity; deep-deferred.

### Three attack paths each

**`riemann_sum_log_weight` (ONE lap from front #4 being axiom-free):**
1. PORT Aristotle `930e468a` (`aristotle-wmertens/`); statement is byte-identical → paste body
   under our axiom name; `#print axioms` to catch v4.28→v4.29 `sorryAx`.
2. Local monotone special case via `Analysis/SumIntegralComparisons`
   (`sum_mul_Ico_le_integral_of_monotone_antitone`, weight `1/n` antitone), squeeze; extend to C¹
   `F` via `F=∫F'` BV decomposition.
3. Substitution `∫_2^N F(log t/logN)/t dt = log N·∫_{log2/logN}^1 F` (CoV moved in v4.29.1 →
   `integral_image_eq_integral_abs_deriv_smul`) + sum-vs-integral error killed by
   `weighted_avg_majorant_tendsto_zero`.

**`s1_holds_from_nonprime_asym` (multidimensional lift):**
1. STATE the k-dim weighted Mertens (Polymath8b §3 sfg-1/lflg): `sieveSum(selberg_nu)` → k-fold
   product of 1-D weighted sums × singular series `𝔖`; `weighted_mertens` is the 1-D factor.
2. Build `𝔖(H)` as a convergent Euler product (reuse `SharpMertens` `eulerProduct_tprod` machinery);
   finiteness + positivity = the `alphaMainTerm` normalization.
3. Separable rank-1 (`J=1`, `F=∏F_i`) case first → `sieveSum` factors, each factor is exactly
   `weighted_mertens`; then `IsLittleO` glue (sub-step (d)); generalize by linearity over `∑_j c_j∏_i`.

**`s2_*`:** mirror s1 with `θ(n+h_i)` on one coordinate (EH/MPZ supplies level of distribution);
only structural diff is the `ϑ/2` (resp `1/4+ϖ`) normalization (Polymath8b §3 theta-oo). Do s1 first.

**`exists_separable_F_*`:** (a) explicit Bernstein/polynomial witness + numeric Rayleigh
(`SievePolynomial`); (b) Stone–Weierstrass density of tensor polynomials on the simplex; (c) extract
near-optimal separable witness from the `MkSet_bddAbove` sup definition.

### Next-lap pointer
item 1/P1 DONE (`riemann_sum_log_weight` ported, front #4 axiom-free). Sub-step (c) **algebra**
now also DONE — `SieveExpansion.lean` has the GPY diagonalization ladder (all axiom-clean,
2026-06-04 continuation): `gpy_diagonalize` (`∑_{d,e}w(d)w(e)/[d,e]=∑_r φ(r)(∑_{r∣d}w(d)/d)²`),
`gpy_diagonalize_moebius` (the `w=μ·g` sieve form = per-coordinate quadratic form in the expansion),
`gpy_yvar_substitution` (`y_r=(μ(r)/r)·∑_{(r,s)=1}μ(s)g(rs)/s`), `gpy_quadform_nonneg` (PSD).
Sub-step (c) ALGEBRA LADDER now COMPLETE (8 axiom-clean commits this lap): also added
`gpy_diagonalize_moebius_squarefree`, `gpy_yvar_eq_zero_of_not_squarefree`,
`gpy_diagonal_asymptotic_form` (canonical capstone `∑μμgg/[d,e]=∑_{r sf}(φ(r)/r²)z_r²`),
`piFinset_lattice_main_factor` + `heuristic_main_term_diagonalized` (heuristic main = `M·∏ᵢ`
diagonalized form), and the (s1) REDUCTION `sieveSum_separable_eq_heuristic_add_correction`
(`sieveSum = heuristic_main + correction`). The whole algebra of sub-step (a)→(c) is machine-checked.
**Three purely-analytic obligations remain** (see ANALYTIC_AXIOM_BURNDOWN.md tail): (1) the
diagonal-sum asymptotic `∑_{r sf}(φ(r)/r²)z_r²→const` (smooth core = Aristotle `3e2b6a8d`); (2) the
correction bound `∑_P coeffₚ(countₚ−M/∏[Pᵢ])=o(main)` via the W-trick discharge
(`lattice_count_offdiag_vanish_Wtrick`) + diagonal `O(1)` error (`lattice_count_main_term`) with
`M=(B−A)/W`; (3) sub-step (d) `IsLittleO` glue into `alphaBound`. Reusable analytic bricks in
`WeightedMertens.lean`: `weighted_cesaro_tendsto_zero`, `weighted_avg_majorant_tendsto_zero`,
`harmonic_div_log_tendsto_one`, `sum_log_mul_log_diff_le_sq`, `Bdisc`/`discrepancy_*`, `abel_tail_*`,
`weighted_mertens_of_riemann`, `weighted_mertens_of_contDiff`.

**UPDATE 2026-06-04 lap N+1 (commits `af0a3e6`…`e8dd497`, 8 axiom-clean, build green 8277):**
The CROSS-TERM (`j≠j'`) algebra is now also done (prior lap was single-`F` diagonal only), and a
**Cauchy–Schwarz collapse** reduced the main-term obligation to the DIAGONAL block alone. New in
`SieveExpansion.lean`: `gpy_diagonalize_bilinear`/`_moebius_bilinear[_squarefree]`/
`gpy_diagonal_asymptotic_form_bilinear` (cross diagonalization ladder); `sieveDivisors_pos`/
`_dvd_closed`; `heuristic_main_selberg_nu_canonical` (FULL `selberg_nu` main term in canonical
`∑_{j,j'}cⱼcⱼ'M∏ᵢ∑_{r sf}(φ/r²)z₁z₂` form); `correction_weight_factor[_split]` (correction weight →
∏ of 1-D Möbius sums — but LOOSE, see burndown); **`gpy_bilinear_cauchy_schwarz`**
(`B(g₁,g₂)²≤B(g₁,g₁)B(g₂,g₂)` ⟹ cross blocks auto-bounded by the diagonal). **Net: `s1` now needs
only the SINGLE diagonal limit `∑_{r sf}(φ/r²)z_r²→I(F)` (Aristotle `weighted_riemann_2d`, in
flight) + off-diag-main `o(main)` + `∑_{diag}|coeff|` size bound + `IsLittleO` glue.** Diagonal
`O(1)` error already wired via `lattice_count_main_term` → `diag_error_bound`. Full map in
`ANALYTIC_AXIOM_BURNDOWN.md` tail.

### UPDATE 2026-06-04 lap N+2 (commits `691a239`,`3a3dbef`,`e7dc3ae`,`8f55d07`; build green 8277)
**Leaves (2) and (4) of `s1_holds_from_nonprime_asym` are now DONE in-kernel.** Cauchy–Schwarz
(prior lap) had collapsed the main term to the diagonal, leaving 4 analytic leaves. This lap closed
two of them:
- **Leaf (2) `∑_{diag}|coeff|=o(main)` — DONE.** `SieveExpansion.hyperbola_count_le` proves the
  k-dim Dirichlet count `#{d∈[1,N]^k:∏dᵢ≤N} ≤ N(1+log N)^{k-1}` fully in-kernel (was queued for
  Aristotle; no longer needed there). Induction on k + `Fin.cons`/`Fin.tail` `card_bij'` fiber
  bijection + `harmonic_le_one_add_log`. Bridge `lattice_count_le_hyperbola` + capstone
  `diagonal_weight_le_hyperbola` give `∑_{diag}|coeff| ≤ C²⌊R⌋₊(1+log⌊R⌋₊)^{k-1}`. Residual: the
  parameter tail `R=o(M log R)` (GPY plumbing, not analysis).
- **Leaf (4) `IsLittleO` glue — DONE (modular chain).** `Sieve.alphaBound_of_sub_littleO`/
  `betaBound_of_sub_littleO` (positive-part `max(f,0)=O f` ⟹ two-sided diff o(main) suffices) +
  `alphaBound_of_heuristic_correction`/`betaBound_of_heuristic_correction` (split `sieveSum=Aheur+Bcorr`;
  heuristic limit + correction bound ⟹ alphaBound). Machine-checks `leaf 1 ∧ leaf 3 ⟹ s1`.

**s1 remaining nuts:**
1. **Leaf (1) diagonal asymptotic** `∑_{r sf}(φ(r)/r²)z_r² → I(F)·const`. **SMOOTH CORE CLOSED
   (lap N+3, commit `68e9eb0`, axiom-clean):** the 2-D simplex limit
   `InnerUniformReduction.weighted_riemann_2d` is PROVEN UNCONDITIONALLY in-kernel (all of `psi_tendsto`
   + the Pólya reduction chain machine-checked; the 3 Aristotle leaf-1 jobs cancelled as redundant).
   **REMAINING for leaf 1 = the GPY port (multi-lap, the new frontier):** connect
   `gpy_diagonal_asymptotic_form`'s output `∑_{r sf}(φ(r)/r²) z_r²` (with `z_r=∑_{(s,r)=1}μ(s)g(rs)/s`,
   `g(d)=F(log d/log R)`) to the `weighted_riemann_2d` double-sum shape. Three attack paths:
   (a) expand `z_r² = ∑_{s,s'}μ(s)μ(s')g(rs)g(rs')/(ss')`, swap to `∑_{s,s'}(…)∑_{r}(φ(r)/r²)[r∣…]`,
   recognise the inner `r`-sum as the singular series `𝔖`; (b) rank-1/separable case first (single
   coordinate, `F=∏Fᵢ`) to validate the shape before the general `J`-basis; (c) reuse `SharpMertens`
   `eulerProduct_tprod` for the `𝔖(H)=∏_p(1-ν_p/p)(1-1/p)^{-k}` Euler product. NB this port consumes
   the now-proven `weighted_riemann_2d` as a black box — design carefully (needs the GPY paper).
2. **Leaf (3) off-diagonal heuristic main = o(main)** = `M·∑_{¬diag}w_P/∏[Pᵢ] = o(M(log R)^k)` (the
   phantom main over W-trick-incompatible tuples whose actual count is 0). Infra:
   `correction_abs_bound` already routes the correction to exactly (leaf 2 diag weight) + (this
   off-diag main). Attack: singular-series discrepancy + W-trick prime gain; needs `W=∏_{p≤D₀}p`,
   `M=(B−A)/W`, `R=x^{θ/2}` parameter plumbing. NOT a clean isolated lemma — coupled to 𝔖(H).

### Witness-axiom thread — feasibility probe result (2026-06-04 lap N+2)
Probed discharging `mk_54_witness_under_EH` (needs `Mk 54 > 4`) via the `Mk_gt_of_symWeight_witness_match_parts`
+ explicit symmetric witness route (as `Mk_200_gt_4` does). **Riskiest assumption FAILS:**
`tools/mk/gen_witness7.py` (degree D=7) sweeps K≥160 and prints "no positive pivot (M_K≤4)" for
small K — i.e. a degree-7 symmetric witness does NOT reach 4 at k=54 (the achievable Rayleigh bound
grows with k; k=200 is near the deg-7 threshold). To get `Mk 54 > 4` (true value 4.00238, Polymath8b)
needs a HIGHER-degree witness (D≥8 ⟹ much larger Gram `native_decide`) AND still rests on the
`denom_bridge`/`num_bridge` realizability axioms (the central gap, on Aristotle). So this thread is a
heavy multi-lap lift, not a clean lap win. Same applies a fortiori to `mk_5511`(>6)/`mk_41588`(>8)/etc.
(higher thresholds). Conclusion: the `mk_*_witness` axioms are gated on the bridge axioms + a
higher-degree witness pipeline; defer until the bridge axioms land. Monotonicity of `Mk` does NOT help
(k<200 witnesses need k-specific constructions; k>200 ones need thresholds >4).

### Leaf (1) DECOMPOSED — 2-D simplex limit reduced to inner uniform convergence (lap N+2, commit `9206855`)
`BoundedGaps/WeightedRiemann2D.lean` (axiom-clean, build green 8278): the deep leaf-1 nut (the 2-D
weighted Riemann limit `weighted_riemann_2d`) is PROVEN modulo a single clean ingredient. Proved
in-kernel: `phi_continuousOn` (Φ_G continuous), `perturbed_riemann` (the MAIN+ERROR perturbed
Riemann core — if `a R m → Φ` uniformly in m, the a-weighted log-sum → ∫₀¹F·Φ), `two_d_factor` (the
double sum factors), `weighted_riemann_2d_of_inner` (capstone). **Remaining = `inner_uniform`**:
`(∑_{n≤R/m}G(log n/log R)/n)/log R → ∫₀^{1-log m/log R}G` uniformly in m∈[2,R]. Three attack paths:
1. **Aristotle** — `aristotle-inner-uniform/Problem.lean` is WRITTEN & typechecks (statement +
   `riemann_sum_log_weight` axiom + split-at-`R^{1-δ}` proof sketch). Submit when the current 2-D
   slot frees, OR immediately if the monolithic `weighted_riemann_2d` (`3e2b6a8d`) fails.
2. **Local split proof** — `m∈[2,R^{1-δ}]`: `R'=⌊R/m⌋≥R^δ→∞`, uniform Riemann via equicontinuity of
   `u↦G((1-s)u)` (G unif. cont. on compact [0,1]); `m∈(R^{1-δ},R]`: `1-s<δ` so sum and integral both
   `O(δ)`. Take δ from ε then R large. The scale-change `inner/logR=(1-s)·(∑G((1-s)·)/n)/logR'` +
   `riemann_sum_log_weight` on `G_s(u)=G((1-s)u)` gives the pointwise piece.
3. **Harvest the monolithic 2-D** — if `weighted_riemann_2d` (`3e2b6a8d`) returns, port directly
   (don't even need the decomposition for the port; the decomposition stays as a cleaner proof/hedge).
Then: connect `weighted_riemann_2d` to the repo's `gpy_diagonal_asymptotic_form` (the Selberg-diagonal
↔ double-Riemann GPY manipulation) — the remaining port step for leaf (1).

### Leaf (1) k-D LIFT — 3-D level FULLY PROVEN, unconditional (lap 2026-06-04 PM, 5 commits)
`BoundedGaps/WeightedRiemann3D.lean` (axiom-clean, build green 8281). The `k`-D weighted-Mertens lift
is the remaining analytic core of s1/s2 (`mkF_denominator = ∫_{simplex}F²` is the `k`-D simplex
integral). The 1-D (`psi_tendsto`), 2-D (`weighted_riemann_2d`), and now **3-D** levels are PROVEN
UNCONDITIONALLY. The 3-D file mirrors the 2-D construction one dimension up, reusing the same
`perturbed_riemann` + `PolyaUniform.polya_uniform` engines:
- `Phi2 G H s = ∫₀^{1-s} G(y)·Phi_H(s+y) dy` (the 2-D simplex cross-section), `phi2_continuous`,
  `phi2_scale` (the t-rescaling change-of-variables), `integral_F_phi2_eq_simplex`.
- `three_d_factor` — the `l·m·n ≤ R` triple sum factors over the outer variable `l` (pure algebra).
- `weighted_riemann_3d_of_inner` — 3-D simplex limit GIVEN the inner-uniform 2-D convergence.
- `Psi3`, `psi3_monotoneOn`, `psi3_reparam`, `inner_uniform_3d_of_pointwise_nonneg` — the Pólya
  monotone-to-continuous upgrade reducing the inner-uniform (for `G,H ≥ 0`) to a POINTWISE limit.
- `psi3_pointwise` — **PROVEN** (the former nut): the `t`-scaled 2-D Riemann sum → `Φ₂(1-t)`, via
  rescale `Ft=G(t·)`,`Gt=H(t·)`, level `N=⌊R^t⌋`, `c_R=logN/logR→t`; feed `Ft,Gt` into
  `weighted_riemann_2d` at `N`; absorb the `c_R→t` drift (product split + 2-D harmonic from
  `weighted_riemann_2d 1 1`); reassemble `Psi3 = c_R²·(realSum/logN²)`. (`set_option maxHeartbeats
  1000000`; opaque `C` via `obtain` to stop `set`-zeta unfolding the integral.)
- `weighted_riemann_3d` — **the UNCONDITIONAL capstone** (for `G,H ≥ 0`, `F` continuous):
  `∑_{lmn≤R} F·G·H/(lmn)/(logR)³ → ∫₀¹ F·Φ₂ = ∫_{x+y+z≤1} F·G·H`.

Aristotle psi3-pointwise (`680977a8`) is now SUPERSEDED (proven in-kernel); harvest unnecessary.

### Generic k-D FRAMEWORK — DONE except ONE lemma (`psi_k_pointwise`) (lap 2026-06-04 PM)
`BoundedGaps/WeightedRiemannKD.lean` (axiom-clean, build green 8282) proves the FULL generic k-D
simplex limit for ALL lists **modulo a single isolated hypothesis**. Built & proven:
- `nestedLogSum`/`nestedPhi` defs (+ `_singleton`/`_pair` = `Phi`/`Phi2`, `nestedLogSum_singleton`
  /`_pair`), `nestedPhi_continuous`, `nestedLogSum_nonneg`/`_mono`, `nestedLogSum_factor`.
- `weighted_riemann_cons_of_inner` (reduction engine), `weighted_riemann_kd_nil` (base).
- `PsiK`/`psiK_monotoneOn` (Pólya monotonicity), `psiK_reparam`, `inner_uniform_kd_of_pointwise`
  (Pólya assembly: pointwise → inner-uniform `huni`).
- **`weighted_riemann_kd_of_pointwise`** — THE CAPSTONE: given the generic pointwise `hpw`, the full
  `nestedLogSum R Gs R/(logR)^|Gs| → nestedPhi Gs 0 = ∫_{simplex}∏Gs` for every nonneg continuous
  `Gs`. Each length = one `cons_of_inner ∘ inner_uniform_kd ∘ hpw`.

**THE ONE REMAINING LEMMA: `psi_k_pointwise`** (= `hpw`): for every nonneg continuous list `gs` and
`t∈[0,1]`, `PsiK R gs t → nestedPhi gs (1-t)`. This is the generic `psi3_pointwise`. Prove by STRONG
INDUCTION on `gs.length`:
- Unfold `PsiK R gs t = nestedLogSum R gs ⌊R^t⌋/(logR)^|gs|`. Rescale via level `N=⌊R^t⌋`,
  `c_R=logN/logR→t`: `nestedLogSum R gs ⌊R^t⌋ = ` (level-`|gs|` nested sum at budget `N`, but
  args `log·/logR` not `log·/logN`). The IH `weighted_riemann_kd_of_pointwise gs` gives the level-`gs`
  limit `nestedLogSum N gs N/(logN)^|gs| → nestedPhi gs 0`; a drift bound (uniform-cont absorbs the
  `c_R→t` arg drift) + the `t`-scaling (`nestedPhi`-rescale, generic `phi2_scale`) convert it to
  `PsiK R gs t → nestedPhi gs (1-t)`.
Then `hpw := psi_k_pointwise` discharges `weighted_riemann_kd_of_pointwise`'s hypothesis ⟹ the
UNCONDITIONAL generic `weighted_riemann_kd` for all k. The 3-D `psi3_pointwise` is the exact
template (generic version adds the strong induction + a generic drift over the nested sum). ~1 lap.

**Concrete 4-D** (`weighted_riemann_4d`) is the low-risk fallback if the generic induction stalls:
copy the 3-D file one dimension up (`Φ₃ G H K s = ∫₀^{1-s} G·Φ₂ H K (s+y)`, `psi4_pointwise`
rescales to the now-available `weighted_riemann_3d`).

**Signed `G,H`** (still open, low priority): `inner_uniform_3d_of_pointwise_nonneg` needs `G,H ≥ 0`
(Pólya monotonicity). For signed, ±-split each (4-way for the product) mirroring
`inner_uniform_of_pointwise`. Defer — nonneg suffices for the GPY box-tensor `F` factors.
