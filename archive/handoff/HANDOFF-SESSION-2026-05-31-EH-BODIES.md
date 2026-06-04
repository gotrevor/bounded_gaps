# Handoff: bounded_gaps — EH/MPZ given precise bodies, `eh_implies_mpz` proven

**Date**: 2026-05-31 ~13:00 UTC · **Branch**: `path-a-selberg-nu` · **HEAD** `3180948` (host must push — no egress in box).

## 🎯 What this session did
Trevor asked whether the two "unprovable until mathlib ships machinery" Prerequisites sorries
(`geh_implies_eh`, `eh_implies_mpz`) could be planned/built. Answer, with code:

- **`eh_implies_mpz` — DONE, axiom-clean.** The blocker was *modeling*, not deep math: `EH`/`GEH`/`MPZ`
  were contentless `axiom _ : Prop`, so the implication had no proof term. Gave `EH` and `MPZ` **precise
  von-Mangoldt discrepancy bodies** (Trevor's call: "Precise"), after which `EH[1/2+2ϖ] → MPZ[ϖ,δ]` is a
  genuine **sub-sum** (same `Λ`, modulus set filtered to δ-smooth). `#print axioms eh_implies_mpz =
  [propext, Classical.choice, Quot.sound]` — no `sorryAx`. Full library green (8254 jobs). **Sorries 4 → 3.**
  Commit `0c17265`.
- **`geh_implies_eh` — stays a sorry; the wall is now sharp and named (Vaughan's identity).** Commit
  `3180948` updates its triage comment (lone sorry now at `Prerequisites:154`). See below.

## 🧠 Context to carry forward
- **The discrepancy foundation** (`Prerequisites.lean`, new `## The discrepancy foundation` section):
  `window x` = `[x,2x]∩ℕ`; `coprimeRes q`; `discrepancy f x q a` = (residue-class sum) −
  (1/φ(q))(coprime-class sum); `maxDisc f x q : ℝ≥0` = `sup_a |Δ|` (in ℝ≥0 so it's total + non-negative
  for free — that non-negativity is what makes the sub-sum monotone). `IsSmooth δ x q` = Squarefree ∧
  primeFactors ≤ x^δ. `EH ϑ` / `MPZ ϖ δ` = `∀A≥0, ∃C>0, ∀x≥2, ↑(∑_{q≤Q} maxDisc Λ x q) ≤ C·x/(log x)^A`,
  EH over `q ≤ x^ϑ`, MPZ over the δ-smooth `q ≤ x^{1/2+2ϖ}`.
- **Why nothing downstream broke:** every consumer of EH/GEH/MPZ (Sieve `maynard_thm`, the `s2_*` axioms,
  Maynard/Polymath8b `*_under_EH/GEH`, Targets) threads the hypothesis **opaquely** to a cited axiom —
  none unfolds its content. So giving real bodies is free for them, and it's an **honesty upgrade**:
  `BombieriVinogradov : EH ϑ` / `MPZ_polymath8a : MPZ ϖ δ` now assert the *actual* theorems instead of a
  contentless `Prop` (which `True` would have satisfied).
- **`geh_implies_eh` is categorically harder than `eh_implies_mpz`, and I made it slightly harder by
  giving EH a body while leaving GEH opaque** (real target, opaque source). To do it honestly needs:
  (1) a faithful **GEH body** — discrepancy over Dirichlet convolutions `α⋆β` with a **Siegel-Walfisz**
  hypothesis on `β` (a real definitional chunk: SW + convolution-discrepancy), and (2) **Vaughan's
  identity** to decompose `Λ` into Type I/II pieces landing in GEH's class. mathlib has `Λ = μ⋆log`
  (`sum_moebius_mul_log_eq`) but **no Vaughan identity** (the `log` factor is too large and must be split —
  that *is* Vaughan). Genuine multi-session port. The `eh_implies_mpz` trick (sub-sum, same function) does
  **not** transfer — here `Λ` must be rebuilt from convolutions.

## ⚠️ Lean gotchas (new this session)
- `vonMangoldt`/`Λ` moved: `Mathlib/NumberTheory/VonMangoldt.lean` is now a **deprecation stub**; real home
  is `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`. `open ArithmeticFunction` + `Λ` notation,
  or `vonMangoldt n`. Möbius inversion `Λ = μ⋆log` is `sum_moebius_mul_log_eq` / `vonMangoldt_sum`.
- A `def` whose body has a real comparison (`x ≤ (n:ℝ)`, `p ≤ x^δ`) is **noncomputable** and its `filter`
  predicate is **not Decidable** — use `open Classical in` *immediately before the def* (it must precede the
  doc comment `/-- … -/`, not sit between the comment and the `def` — that's a parse error
  "unexpected token 'open'; expected 'lemma'"). In the matching proof, `classical` at the top + plain
  `apply Finset.sum_le_sum_of_subset` lets the goal's own DecidablePred drive inference.
- `Finset.sum_le_sum_of_subset` needs a canonically-ordered monoid — `ℝ≥0` qualifies, `ℝ` does **not** for
  free (subtraction). Summing `maxDisc` in `ℝ≥0` then casting via `NNReal.coe_le_coe.mpr` is what makes the
  sub-sum go through.
- Box OOM hit mid-session ("Cannot allocate memory" opening oleans) — `pkill -9 lean lake`, re-run, cache
  makes it fast. The relay batches output on a delay; failed-then-recovered builds can look alarming. The
  authoritative check is the final `Build completed successfully (N jobs)` line + `#print axioms`.

## 🎬 Next actions
1. **Bank it (host):** push `path-a-selberg-nu` (HEAD `3180948` — the bridge work from earlier sessions +
   these two commits). No PR machinery in the box.
2. **If continuing the EH thread:** the honest `geh_implies_eh` = build a Siegel-Walfisz def + a faithful
   GEH convolution-discrepancy body + port Vaughan's identity. Multi-session; only worth it if a Vaughan
   identity is on the horizon. **Otherwise leave it** — it's a real wall, honestly documented.
3. **Or pivot** (still the standing recommendation): erdos-403's lone `tied_sharp_ceiling` kernel
   (`~/src/erdos-403`, `Basic.lean:272`) is the warmer offline-tractable target.

## 📁 Key files
- `BoundedGaps/Prerequisites.lean` — the discrepancy foundation + real `EH`/`MPZ` + proven
  `eh_implies_mpz` + `geh_implies_eh` (documented Vaughan-wall sorry, line ~154).

---
**Remaining real sorries (3):** `Prerequisites:geh_implies_eh` (Vaughan wall), `Polymath8b:796`
(twin/Goldbach §8), `Zhang:36` (70M). All off the H_m/polynomial-witness path, which is sorry-free
modulo the open-math `Mk 49 > 4` numerics.
