# Aristotle target queue — bounded_gaps

How to be in the best position to fire useful questions at Harmonic's Aristotle.
A target is fireable when it is **bounded + self-contained + architected** (a precise
Lean statement whose proof needs no machinery mathlib lacks). Most remaining work is
*whole theorems*; the supply of fireable lemmas is manufactured by **decomposing** them.

## Recipe (validated 2026-05-31 on `tuple_5511_admissible`)
1. Write the target as a **standalone `.lean`** (statement + `sorry`), self-contained: pull in
   only the data/defs it needs, state the goal in valid Lean, add an architected-strategy docstring.
2. **Pre-check locally** against our v4.29.1 mathlib (`lake env lean scratch.lean`) — confirms it
   elaborates with the `sorry`. Never burn an Aristotle run on a malformed goal (I nearly sent
   pseudo-syntax on the first try).
3. `aristotle submit "<instructions>" --project-dir <dir>`; poll `aristotle list` (one-shot; NOT
   `aristotle show` = blocking TUI). Background poller exits on non-RUNNING → re-invokes the session.
4. `aristotle download <id> --destination x.tar.gz` → untar → port the proof into the repo →
   `lake build <Module>` + `#print axioms` to reverify under v4.29.1.

**Toolchain note:** Aristotle pins **v4.28.0**, repo is **v4.29.1**. Standalone-statement mode makes
the drift a non-issue for stable lemmas (the 5511 proof ported with ZERO edits). Open experiment:
hand it our `lean-toolchain` in `--project-dir` to see if it'll prove against v4.29.1 directly.

## Status
- ✅ **`tuple_5511_admissible`** — DONE (commit `b682f25`). axiom→theorem, bundled `native_decide`
  + ZMod bridge. No sorryAx, no new axiom kinds. Aristotle one-shot it; ported clean.

## The real vein: `mk_*_witness` are dischargeable, not "Maple" citations
The M_k variational lower bounds were axiomatized as external numerical evidence. **They are not
irreducible.** The repo already has (axiom-clean): `polynomialMkF P : ℚ` (exact Rayleigh ratio of a
polynomial test fn via Dirichlet integrals), `polynomialMkF_eq_MkF`, and `Mk_ge_polynomialMkF` (the
honest smooth-cutoff + DCT lower bound). So each `mk_*_witness` reduces to ONE concrete obligation:

> exhibit an explicit `PolynomialSieveWeight k` P and prove the **rational** inequality
> `polynomialMkF P > threshold`.

That is bounded, computable mathematics — and a strong Aristotle target (or do-it-here).

### M_5 > 2 (`mk_5_witness_under_EH`) — ✅ DONE (commit `f405f27`)
Discharged axiom→theorem in `BoundedGaps/Mk5Witness.lean`. **Reusable pattern for the whole `mk_*`
family** (no Aristotle needed): (1) explicit witness `P5` (56 monomials); (2) computable `List`
evaluators `numC`/`denC` mirroring the `noncomputable` Finset `polynomialMaynardNumerator/Denominator`;
(3) bridge `∑ x ∈ l.toFinset = (l.map ·).sum` via `List.sum_toFinset` + `Nodup` (the `dsum` helper),
with `monomialIntegral`/`dirichletIntegralWithSlack` defeq to the computable mirrors; (4) exact value
by `native_decide`; (5) chain `Mk_ge_polynomialMkF` + `polynomialMkF_eq_MkF`. Axiom-clean modulo
`native_decide`. Larger `mk_*` (k=50, 35410, …) reuse this verbatim once the witness search
(`tools/mk/`) is rerun per k — only the `native_decide` weight grows.

<details><summary>Original derivation notes</summary>
Computed exactly (`tools/mk/mk5_sym.py`, stdlib rationals, mirrors the Lean `polynomialMkF` formula):
- deg ≤1 basis caps at ≈1.9508; deg ≤2 at **1.9905** (exact `2274413/1142625` < 2, so genuinely
  insufficient); only **deg 3** clears it at ≈**2.00289** — independently reproduces Maynard's
  "M_5 needs cubics" finding.
- Exact rational witness (symmetric, 7 monomial-orbit coeffs, scaled ×62832):
  `() 14960 · (1) -40392 · (1,1) 62832 · (1,1,1) -39984 · (2) 59136 · (2,1) -43197 · (3) -31416`
  → `polynomialMkF P = 12048682945/6016885374 ≈ 2.002478 > 2`. ✓
- **Next:** encode as `PolynomialSieveWeight 5`, prove `polynomialMkF P = <rational>` (native_decide /
  norm_num on the finite sum), chain `Mk_ge_polynomialMkF` → `Mk 5 > 2`, pick ϑ→1 with `2/ϑ < ratio`.
</details>

### Larger M_k (`mk_50`, `mk_35410`, …) — same shape, harder
Same reduction; the §6 "Maple computation" IS this Rayleigh optimization at larger basis/dimension.
Tractability drops with k and required degree. The witness search is mechanical (extend `mk5_sym.py`);
the Lean `polynomialMkF = rational` proof gets heavier (bigger `native_decide`). Candidate batch once
M_5 validates the path. Fire-ready only after we run the witness search per k.

## NOT fireable (don't waste runs)
- `geh_implies_eh` — Vaughan's identity port; open theory-build, mathlib lacks it. **Integrity flag**
  on the "route (a)" shortcut (see HANDOFF) — do NOT point Aristotle at it.
- `BombieriVinogradov`, `GeneralizedBV`, `MPZ_polymath8a`, sieve `s1_*`/`s2_*`, `exists_separable_F_*`
  — the cited deep analytic-NT inputs. Not bounded.
- `narrowness_*_ge` (lower bounds) — exhaustive non-existence search, explosive.
- `narrowness_35410_le …_3473955908_le` (upper bounds) — same shape as 5511 BUT **data-blocked**
  (no tuple files for these; 75M/3.4B-element tuples can't be Lean literals anyway). Host-only data fetch.
