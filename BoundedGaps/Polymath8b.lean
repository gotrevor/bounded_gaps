/-
# Polymath8b — Variants of the Selberg sieve, bounded intervals containing many primes.

Tao, Maynard, et al. (2014). The 246 paper.

Captures: the main theorem (all 13 numerical bounds), the DHL reformulation
(Theorem main-dhl), the H(k) bounds (Theorem hk-bound), the parity-barrier
optimality of $H_1 \le 6$, and the twin-primes-or-Goldbach disjunction.

Local copy: [../papers/pdf/polymath8b-2014-variants.pdf](../papers/pdf/polymath8b-2014-variants.pdf)
LaTeX source: [../papers/src/polymath8b-1407.4897/newergap-submitted.tex](../papers/src/polymath8b-1407.4897/newergap-submitted.tex)

Statements lifted from §1 (Theorem main, Theorem disj), §3 (Theorem main-dhl,
Theorem hk-bound), §7 (parity).

## File organization (blueprint order)

The §1 numerical bounds in Polymath8b are stated first in the paper, but each one
*depends on* a §3 DHL[k, j] claim plus a §3 narrowness bound. To make the
dependency tree compile (and to make the proof structure readable), this file
presents the helpers first:

1. §3 DHL reformulations (the dhl_*_* claims that §1 chains through)
2. §3 Narrowness bounds (Theorem hk-bound — the H(k) values §1 chains through)
3. §1 Main Theorem with blueprint-split chained proofs
4. §7 Parity barrier
5. §8 Twin-primes-or-Goldbach disjunction
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Prerequisites
import BoundedGaps.Sieve
import BoundedGaps.Engelsma

namespace BoundedGaps.Polymath8b

open BoundedGaps
open scoped ContDiff

/-! ## §3 — The DHL reformulation (Theorem main-dhl)

The numerical bounds in §1 (Theorem main) all factor through DHL[k, j] claims.

Each DHL claim below is blueprint-split into an application of one of
`Sieve.{maynard_thm, maynard_trunc, epsilon_trick, epsilon_beyond}` together
with the matching $M_k$ (or $M_{k, \varepsilon}$) numerical witness — a
focused sorry stating the specific variational inequality Polymath8b §6
establishes by direct numerical (Maple) computation. -/

/-! ### Mk-witness leaves (Polymath8b §6 numerical claims, axiomatized)

These are the leaf claims the §3 DHL chains route through. Each captures a
specific variational inequality that Polymath8b §6 establishes via direct
numerical computation on the Maynard quadratic form on the simplex — often
via Maple-style integration over piecewise polynomials. Axiomatized as
cited external evidence per the project's "axioms at leaves" principle. -/

/-- Polymath8b §6 + Bombieri-Vinogradov: $\exists \varepsilon, \vartheta$ with
$0 < \vartheta < 1/2$ (so $\EH[\vartheta]$ holds via BV), $1 + \varepsilon
< 1/\vartheta$, and $M_{50, \varepsilon} > 2/\vartheta$ (threshold for
`epsilon_trick` at $m=1$).

Polymath8b Theorem `mke-lower`(i) gives $M_{50, 1/25} > 4.0043$. Choosing
$\varepsilon = 1/25$ and $\vartheta$ slightly below $1/2$ (say
$\vartheta = 1/2 - \eta$ for small $\eta$) satisfies all conditions:
$1 + 1/25 = 1.04 < 1/\vartheta \approx 2$ and $2/\vartheta \approx 4 < 4.0043$.
Drives DHL[50, 2] → $H_1 \le 246$. -/
axiom mk_eps_50_witness :
    ∃ ε ϑ : ℝ, 0 < ε ∧ (0 < ϑ ∧ ϑ < 1 / 2) ∧
      1 + ε < 1 / ϑ ∧ Sieve.Mk_eps 50 ε > 2 / ϑ

/-- Polymath8b §6: $\exists$ MPZ parameters $\varpi, \delta$ with
$M_{35410}^{[\delta/(1/4+\varpi)]} > 2/(1/4+\varpi)$. Combines Polymath8a §2
(MPZ existence at specific parameters) with Polymath8b §6 (variational bound
on the truncated simplex). Drives DHL[35410, 3] via `Sieve.maynard_trunc`
($m = 2$). Paper Theorem `mlower-var`(ii) at line 973: there exist $\delta,
\varpi$ with $600\varpi + 180\delta < 7$ and the inequality. -/
axiom mk_35410_witness :
    ∃ ϖ δ : ℝ, 0 < 1/4 + ϖ ∧ 0 < δ ∧ Prerequisites.MPZ ϖ δ ∧
      Sieve.Mk_truncated 35410 (δ / (1/4 + ϖ)) > 2 / (1/4 + ϖ)

/-- Polymath8b §6: $M_{1649821}^{[\delta/(1/4+\varpi)]} > 3/(1/4+\varpi)$
at suitable MPZ parameters. Drives DHL[1649821, 4] ($m = 3$). Paper Theorem
`mlower-var`(iii) at line 974. -/
axiom mk_1649821_witness :
    ∃ ϖ δ : ℝ, 0 < 1/4 + ϖ ∧ 0 < δ ∧ Prerequisites.MPZ ϖ δ ∧
      Sieve.Mk_truncated 1649821 (δ / (1/4 + ϖ)) > 3 / (1/4 + ϖ)

/-- Polymath8b §6: $M_{75845707}^{[\delta/(1/4+\varpi)]} > 4/(1/4+\varpi)$
at suitable MPZ parameters. Drives DHL[75845707, 5] ($m = 4$). Paper
Theorem `mlower-var`(iv) at line 975. -/
axiom mk_75845707_witness :
    ∃ ϖ δ : ℝ, 0 < 1/4 + ϖ ∧ 0 < δ ∧ Prerequisites.MPZ ϖ δ ∧
      Sieve.Mk_truncated 75845707 (δ / (1/4 + ϖ)) > 4 / (1/4 + ϖ)

/-- Polymath8b §6: $M_{3473955908}^{[\delta/(1/4+\varpi)]} > 5/(1/4+\varpi)$
at suitable MPZ parameters. Drives DHL[3473955908, 6] ($m = 5$, largest
tabulated case). Paper Theorem `mlower-var`(v) at line 976. -/
axiom mk_3473955908_witness :
    ∃ ϖ δ : ℝ, 0 < 1/4 + ϖ ∧ 0 < δ ∧ Prerequisites.MPZ ϖ δ ∧
      Sieve.Mk_truncated 3473955908 (δ / (1/4 + ϖ)) > 5 / (1/4 + ϖ)

/-- Polymath8b §6: $\vartheta \in (0, 1)$ with $M_{54} > 4/\vartheta$, under
EH. Drives DHL[54, 3] via `Sieve.maynard_thm` (threshold `2m/ϑ` with $m=2$).
Polymath8b Theorem `mlower`(vii) reports $M_{54} > 4.00238$, so for ϑ
sufficiently close to 1, $4/\vartheta < 4.00238$. -/
axiom mk_54_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 54 > 2 * 2 / ϑ

/-- Polymath8b §6: $M_{5511} > 6/\vartheta$ under EH. Drives DHL[5511, 4]
via `Sieve.maynard_thm` (threshold `2m/ϑ` with $m=3$). Polymath8b Theorem
`mlower`(viii) reports $M_{5511} > 6$, achievable for ϑ → 1. -/
axiom mk_5511_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 5511 > 2 * 3 / ϑ

/-- Polymath8b §6: $M_{41588} > 8/\vartheta$ under EH. Drives DHL[41588, 5]
via `Sieve.maynard_thm` (threshold `2m/ϑ` with $m=4$). Polymath8b Theorem
`mlower`(ix) reports $M_{41588} > 8$, achievable for ϑ → 1. -/
axiom mk_41588_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 41588 > 2 * 4 / ϑ

/-- Polymath8b §6: $M_{309661} > 10/\vartheta$ under EH. Drives DHL[309661, 6]
via `Sieve.maynard_thm` (threshold `2m/ϑ` with $m=5$). Polymath8b Theorem
`mlower`(x) reports $M_{309661} > 10$, achievable for ϑ → 1. -/
axiom mk_309661_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 309661 > 2 * 5 / ϑ

/-- Polymath8b §6 + Theorem `piece`: an explicit $F$ witness for
`epsilon_beyond` at $k = 3, m = 1$ — the parity-tight flagship yielding
$H_1 \le 6$ under GEH.

Packages the full hypothesis bundle that `Sieve.epsilon_beyond` requires
(F on $\frac{3}{2} \mathcal{R}_3$, vanishing marginal, $\sum J_{i,1-\varepsilon}
/ I(F) > 2/\vartheta$).

Citation: Polymath8b Theorem `piece` (§6) produces a piecewise polynomial
$F$ symmetric in $(t_1, t_2, t_3)$, supported on the $\frac{3}{2}$-scaled
simplex, with the vanishing marginal property and the threshold
inequality. Regularization to $C^\infty$ is part of the proof of
`epsilon-beyond` (§5 line 1581) and is absorbed into this axiom for the
purposes of the present statement.

**PR-A1b-ii restate**: superseded the previous `Sieve.Mk_eps 3 ε > 2/ϑ`
shape — `epsilon-beyond` has no $M_{k, \varepsilon}$ Rayleigh sup, only
an explicit $F$. -/
axiom mk_eps_3_witness_under_GEH :
    ∃ (ε ϑ : ℝ) (F : (Fin 3 → ℝ) → ℝ),
      0 < ε ∧ ε < 1 / ((3 : ℝ) - 1) ∧
      (0 < ϑ ∧ ϑ < 1) ∧
      Sieve.IsFiniteSeparable F ∧
      ContDiff ℝ ∞ F ∧
      Function.support F ⊆ Sieve.simplex_scaled 3 ((3 : ℝ) / ((3 : ℝ) - 1)) ∧
      Sieve.HasVanishingMarginal 3 ε F ∧
      Sieve.mkF_beyond_denominator 3 F > 0 ∧
      (∑ i, Sieve.J_i_beyond 3 ε F i) / Sieve.mkF_beyond_denominator 3 F >
        2 * 1 / ϑ

/-- Polymath8b §6 / `mke-lower`(xiii): an explicit $F$ witness for
`epsilon_beyond` at $k = 51, m = 2$ — drives $\DHL[51, 3]$ under GEH.

Citation: Polymath8b Theorem `mke-lower`(xiii) reports $M_{51, 1/50} >
4.00156$, but `epsilon-beyond` consumes the upstream $F$ witness (with
vanishing marginal) rather than the bare $M_{k,\varepsilon}$ Rayleigh sup.
Both come from the same Krylov-subspace construction; this axiom packages
the $F$ + vanishing marginal directly.

**PR-A1b-ii restate**: superseded the previous `Sieve.Mk_eps 51 ε > 4/ϑ`
shape. -/
axiom mk_eps_51_witness_under_GEH :
    ∃ (ε ϑ : ℝ) (F : (Fin 51 → ℝ) → ℝ),
      0 < ε ∧ ε < 1 / ((51 : ℝ) - 1) ∧
      (0 < ϑ ∧ ϑ < 1) ∧
      Sieve.IsFiniteSeparable F ∧
      ContDiff ℝ ∞ F ∧
      Function.support F ⊆ Sieve.simplex_scaled 51 ((51 : ℝ) / ((51 : ℝ) - 1)) ∧
      Sieve.HasVanishingMarginal 51 ε F ∧
      Sieve.mkF_beyond_denominator 51 F > 0 ∧
      (∑ i, Sieve.J_i_beyond 51 ε F i) / Sieve.mkF_beyond_denominator 51 F >
        2 * 2 / ϑ

/-! ### DHL[k, m+1] claims (chained through Sieve.maynard_* + Mk witnesses) -/

/-- **DHL[50, 2]** unconditional → $H_1 \le H(50) = 246$.

Blueprint: ε-trick at $k=50, m=1$ with the §6 numerical witness
`mk_eps_50_witness`. The witness provides $(ε, ϑ)$ with $ϑ < 1/2$, so
EH[ϑ] is unconditional (Bombieri-Vinogradov). -/
theorem dhl_50_2 : DHL 50 2 := by
  obtain ⟨ε, ϑ, hε, hϑBV, hSupp, hMk⟩ := mk_eps_50_witness
  have hEH : Prerequisites.EH ϑ := Prerequisites.BombieriVinogradov hϑBV
  have hϑ : 0 < ϑ ∧ ϑ < 1 :=
    ⟨hϑBV.1, hϑBV.2.trans (by norm_num : (1 / 2 : ℝ) < 1)⟩
  have hMk' : Sieve.Mk_eps 50 ε > 2 * (1 : ℕ) / ϑ := by
    have : (2 * (1 : ℕ) : ℝ) / ϑ = 2 / ϑ := by push_cast; ring
    rw [this]; exact hMk
  exact Sieve.epsilon_trick 50 1 (by norm_num) (by norm_num)
    ε ϑ hε hϑ hEH hSupp hMk'

/-- **DHL[35410, 3]** unconditional.

Blueprint: maynard_trunc at $k=35410, m=2$ with MPZ parameters from `mk_35410_witness`. -/
theorem dhl_35410_3 : DHL 35410 3 := by
  obtain ⟨ϖ, δ, hϖ, hδ, hMPZ, hMk⟩ := mk_35410_witness
  exact Sieve.maynard_trunc 35410 2 (by norm_num) (by norm_num) ϖ δ hϖ hδ hMPZ hMk

/-- **DHL[1649821, 4]** unconditional. -/
theorem dhl_1649821_4 : DHL 1649821 4 := by
  obtain ⟨ϖ, δ, hϖ, hδ, hMPZ, hMk⟩ := mk_1649821_witness
  exact Sieve.maynard_trunc 1649821 3 (by norm_num) (by norm_num) ϖ δ hϖ hδ hMPZ hMk

/-- **DHL[75845707, 5]** unconditional. -/
theorem dhl_75845707_5 : DHL 75845707 5 := by
  obtain ⟨ϖ, δ, hϖ, hδ, hMPZ, hMk⟩ := mk_75845707_witness
  exact Sieve.maynard_trunc 75845707 4 (by norm_num) (by norm_num) ϖ δ hϖ hδ hMPZ hMk

/-- **DHL[3473955908, 6]** unconditional. -/
theorem dhl_3473955908_6 : DHL 3473955908 6 := by
  obtain ⟨ϖ, δ, hϖ, hδ, hMPZ, hMk⟩ := mk_3473955908_witness
  exact Sieve.maynard_trunc 3473955908 5 (by norm_num) (by norm_num) ϖ δ hϖ hδ hMPZ hMk

/-- **DHL[k, m+1]** unconditional asymptotic: holds whenever
$k \ge C \exp((4 - 28/157) m)$. -/
-- TRIAGE: NEEDS_SIEVE — asymptotic Mk lower bound + maynard_trunc applied
-- uniformly in m. Requires asymptotic admissibility (k-tuple construction
-- at scale). Not yet blueprint-split — single leaf.
theorem dhl_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ, m ≥ 1 →
      (k : ℝ) ≥ C * Real.exp ((4 - 28/157) * m) → DHL k (m + 1) := sorry

/-- Under EH: **DHL[54, 3]**.

Blueprint: maynard_thm at $k=54, m=2$ with `mk_54_witness_under_EH` and EH
at the chosen $\vartheta$. -/
theorem dhl_54_3_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 54 3 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_54_witness_under_EH
  exact Sieve.maynard_thm 54 2 (by norm_num) (by norm_num) ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[5511, 4]**. -/
theorem dhl_5511_4_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 5511 4 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_5511_witness_under_EH
  exact Sieve.maynard_thm 5511 3 (by norm_num) (by norm_num) ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[41588, 5]**. -/
theorem dhl_41588_5_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 41588 5 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_41588_witness_under_EH
  exact Sieve.maynard_thm 41588 4 (by norm_num) (by norm_num) ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[309661, 6]**. -/
theorem dhl_309661_6_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 309661 6 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_309661_witness_under_EH
  exact Sieve.maynard_thm 309661 5 (by norm_num) (by norm_num) ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH, asymptotic DHL: exponent $2m$ instead of $(4 - 28/157)m$. -/
-- TRIAGE: NEEDS_SIEVE — asymptotic version of maynard_thm under EH. Single leaf.
theorem dhl_asymptotic_under_EH
    (_hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k m : ℕ, m ≥ 1 →
      (k : ℝ) ≥ C * Real.exp (2 * m) → DHL k (m + 1) := sorry

/-- Under GEH: **DHL[3, 2]**. The flagship parity-tight result.

Blueprint: epsilon_beyond at $k=3, m=1$ with `mk_eps_3_witness_under_GEH` and
GEH at the chosen $\vartheta$. -/
theorem dhl_3_2_under_GEH (hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    DHL 3 2 := by
  obtain ⟨ε, ϑ, F, hε_pos, hε_lt, hϑ, hSep, hSmooth, hSupp, hVanish, hDen, hThresh⟩ :=
    mk_eps_3_witness_under_GEH
  exact Sieve.epsilon_beyond 3 1 (by norm_num) (by norm_num) ε ϑ hε_pos hε_lt
    hϑ (hGEH ϑ hϑ) F hSep hSmooth hSupp hVanish hDen (by exact_mod_cast hThresh)

/-- Under GEH: **DHL[51, 3]**. -/
theorem dhl_51_3_under_GEH (hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    DHL 51 3 := by
  obtain ⟨ε, ϑ, F, hε_pos, hε_lt, hϑ, hSep, hSmooth, hSupp, hVanish, hDen, hThresh⟩ :=
    mk_eps_51_witness_under_GEH
  exact Sieve.epsilon_beyond 51 2 (by norm_num) (by norm_num) ε ϑ hε_pos hε_lt
    hϑ (hGEH ϑ hϑ) F hSep hSmooth hSupp hVanish hDen (by exact_mod_cast hThresh)

/-! ## §3 — Narrowness bounds (Theorem hk-bound) -/

/-- $H(2) = 2$ (the tuple $(0, 2)$ realizes it). Fully proven:
the upper bound is `Basic.narrowness_2_le_two` (the tuple $(0, 2)$ witnesses);
the lower bound is `Basic.narrowness_2_ge_two` (mod-2 parity forces any
admissible 2-tuple's diameter to be even and positive, hence $\ge 2$). -/
theorem narrowness_2 : narrowness 2 = 2 :=
  le_antisymm narrowness_2_le_two narrowness_2_ge_two

/-- $H(3) = 6$ (the tuple $(0, 2, 6)$ realizes it). Fully proven:
the upper bound is `Basic.narrowness_3_le_six` (the tuple $(0,2,6)$ witnesses);
the lower bound is `Basic.narrowness_3_ge_six` (no admissible 3-tuple of
diameter $< 6$, by simultaneous case analysis on residues mod 2 and mod 3). -/
theorem narrowness_3 : narrowness 3 = 6 :=
  le_antisymm narrowness_3_le_six narrowness_3_ge_six

/-- $H(50) \ge 246$: no admissible 50-tuple has diameter less than 246.
Cited as an external result from Clark-Jarvis 2001 (*Dense admissible
sequences*, Math. Comp. 70(236):1713-1718), where exact values of $H(k)$
were computed by exhaustive enumeration for all $k \le 342$. The
enumeration itself is out of scope for this project; a mechanized search
would require a verified admissibility check over candidate 50-tuples of
diameter $< 246$. -/
axiom narrowness_50_ge_246 : 246 ≤ narrowness 50

/-- **$H(50) = 246$**: an admissible 50-tuple of diameter 246 exists, and no
narrower one. The $\le 246$ direction is `Engelsma.narrowness_50_le_246`
(the Engelsma 50-tuple witnesses it); the $\ge 246$ direction is axiomatized
as `narrowness_50_ge_246` (Clark-Jarvis 2001). -/
theorem narrowness_50 : narrowness 50 = 246 :=
  le_antisymm Engelsma.narrowness_50_le_246 narrowness_50_ge_246

/-- $H(51) \ge 252$. Cited from Clark-Jarvis 2001; see `narrowness_50_ge_246`
for the source and rationale. -/
axiom narrowness_51_ge_252 : 252 ≤ narrowness 51

/-- $H(51) = 252$. The $\le 252$ direction is `Engelsma.narrowness_51_le_252`;
the $\ge 252$ direction is axiomatized as `narrowness_51_ge_252`
(Clark-Jarvis 2001). -/
theorem narrowness_51 : narrowness 51 = 252 :=
  le_antisymm Engelsma.narrowness_51_le_252 narrowness_51_ge_252

/-- $H(54) \ge 270$. Cited from Clark-Jarvis 2001; see `narrowness_50_ge_246`
for the source and rationale. -/
axiom narrowness_54_ge_270 : 270 ≤ narrowness 54

/-- $H(54) = 270$. The $\le 270$ direction is `Engelsma.narrowness_54_le_270`;
the $\ge 270$ direction is axiomatized as `narrowness_54_ge_270`
(Clark-Jarvis 2001). -/
theorem narrowness_54 : narrowness 54 = 270 :=
  le_antisymm Engelsma.narrowness_54_le_270 narrowness_54_ge_270

-- LARGE-k NARROWNESS BOUNDS — all 7 below: each would land if we ran the
-- tuple harvest at that k (analogous to today's k=51, k=54 harvest from MIT
-- primegaps). At k > ~1000 the harvest is non-trivial — Engelsma's database
-- caps at moderate k, and `native_decide` admissibility may stop scaling.
-- For very large k (35410+) admissibility must use an asymptotic construction
-- (e.g. greedy/Erdős-style), not direct enumeration.

/-- $H(5511) \le 52116$. Chains through the MIT primegaps tuple harvested
into `Engelsma.tuple_5511`; admissibility itself is a SCALING_FAILURE sorry
(`interval_cases` over 5510 primes overflows Lean's elaborator). -/
theorem narrowness_5511_le : narrowness 5511 ≤ 52116 :=
  Engelsma.narrowness_5511_le_52116

-- The following six $H(k)$ upper bounds are axiomatized as external
-- numerical results. Each comes from an admissible-tuple construction
-- (Hensley-Richards 1973 / Engelsma-style greedy) reported in Polymath8b
-- §6 and used in §1's $H_m$ bounds. Lean mechanization of the underlying
-- constructions at these scales (up to $k \approx 3.5 \times 10^9$) is a
-- separate large lift and out of current scope; we cite the constructions
-- as leaves rather than redoing them in Lean.

/-- $H(35410) \le 398130$. External: Polymath8b §6 (Hensley-Richards-type
admissible-tuple construction). -/
axiom narrowness_35410_le : narrowness 35410 ≤ 398130

/-- $H(41588) \le 474266$. External: Polymath8b §6. -/
axiom narrowness_41588_le : narrowness 41588 ≤ 474266

/-- $H(309661) \le 4137854$. External: Polymath8b §6. -/
axiom narrowness_309661_le : narrowness 309661 ≤ 4137854

/-- $H(1649821) \le 24797814$. External: Polymath8b §6. -/
axiom narrowness_1649821_le : narrowness 1649821 ≤ 24797814

/-- $H(75845707) \le 1431556072$. External: Polymath8b §6. -/
axiom narrowness_75845707_le : narrowness 75845707 ≤ 1431556072

/-- $H(3473955908) \le 80550202480$. External: Polymath8b §6 (largest tabulated
$H_m$ entry; $k \approx 3.5 \times 10^9$). -/
axiom narrowness_3473955908_le : narrowness 3473955908 ≤ 80550202480

/-- Asymptotic upper bound: $H(k) = O(k \log k)$. External: Hensley-Richards
1973 (*"Primes in intervals"*, Acta Arith. 25(4):375-391), which constructs
admissible $k$-tuples from primes in a window of length $\sim k \log k$ and
in fact establishes the sharper $H(k) \le k \log k + k \log \log k - k + o(k)$.
We cite the $O(k \log k)$ form as the leaf consumed by the §1 asymptotic
combinator; the sharper form is available from the same source if needed. -/
axiom narrowness_asymptotic_upper :
    (fun k : ℕ => (narrowness k : ℝ))
      =O[Filter.atTop]
      (fun k : ℕ => (k : ℝ) * Real.log k)


/-! ## §1 — Main Theorem (Theorem 1.3 in the paper, labeled `main`)

All bounds are stated as `liminfGap m ≤ (constant : ℕ∞)`.

Each bound below is blueprint-split: the proof body chains through a §3 DHL
claim, a §3 narrowness bound, and one of the `Basic.dhl_*_implies_*` bridges.
The chain is type-checked even though individual leaves remain `sorry`. -/

/-! ### Asymptotic combinator (helper for the asymptotic §1 bounds) -/

/-- Bookkeeping combinator: an asymptotic DHL claim together with the
narrowness $=O(k \log k)$ bound produces an asymptotic $H_m$ bound at the
matching exponent.

**Discharged 2026-05-28**: real proof. For each $m$, take
$k_m = \max(\lceil C_{\mathrm{dhl}} e^{\alpha m}\rceil, m + 1 + k_0)$ where
$k_0$ is the `IsBigO` window threshold. The three `max` clauses give
respectively: (a) $k_m \ge C_{\mathrm{dhl}} e^{\alpha m}$ so DHL fires;
(b) $k_m \ge m + 1$ so `dhl_implies_liminfGap` applies; (c) $k_m \ge k_0$
so the narrowness $O(k\log k)$ bound applies. Then
$k_m \le C_3 e^{\alpha m}$ and $\log k_m \le \log C_3 + \alpha m$ give
$k_m \log k_m \le C_5\, m\, e^{\alpha m}$, and the chain
$\mathrm{liminfGap}\,m \le \mathrm{narrowness}\,k_m \le C_0 k_m \log k_m$
closes after the $\mathbb{N}_\infty \to \mathbb{R}_{\ge 0}^\infty$
coercion.

The `0 < α` hypothesis is essential: with $\alpha \le 0$ the $m+1$ lower
bound on a usable $k$ would outgrow the $m\,e^{\alpha m}$ target. Both call
sites (`Hm_asymptotic_unconditional` at $\alpha = 4 - 28/157$,
`Hm_asymptotic_under_EH` at $\alpha = 2$) satisfy it. -/
theorem hm_asymp_from_dhl_and_narrowness (α : ℝ) (hα : 0 < α)
    (Cdhl : ℝ) (hCdhl_pos : 0 < Cdhl)
    (hDHL_asymp : ∀ k m : ℕ, m ≥ 1 →
      (k : ℝ) ≥ Cdhl * Real.exp (α * m) → DHL k (m + 1))
    (hNarrow_asymp : (fun k : ℕ => (narrowness k : ℝ))
        =O[Filter.atTop] (fun k : ℕ => (k : ℝ) * Real.log k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp (α * m)) := by
  -- IsBigO witness, normalized to a nonneg constant.
  obtain ⟨C₀, hC₀⟩ := hNarrow_asymp.bound
  rw [Filter.eventually_atTop] at hC₀
  obtain ⟨k₀, hk₀⟩ := hC₀
  set C₀' := max C₀ 0 with hC₀'def
  have hC₀'_nonneg : 0 ≤ C₀' := le_max_right _ _
  -- uniform bound coefficients
  set C₃ : ℝ := Cdhl + 1/α + (k₀ : ℝ) + 3 with hC₃def
  have hC₃_ge1 : 1 ≤ C₃ := by
    have h1 : 0 < 1/α := by positivity
    have h2 : (0:ℝ) ≤ (k₀:ℝ) := by positivity
    rw [hC₃def]; nlinarith
  have hC₃_pos : 0 < C₃ := by linarith
  have hlogC₃_nonneg : 0 ≤ Real.log C₃ := Real.log_nonneg hC₃_ge1
  set C₅ : ℝ := C₃ * (Real.log C₃ + α) with hC₅def
  have hC₅_pos : 0 < C₅ := by rw [hC₅def]; positivity
  refine ⟨C₀' * C₅ + 1, by positivity, fun m hm => ?_⟩
  -- choose k large enough for DHL, the bridge, and the IsBigO window
  set km : ℕ := max (Nat.ceil (Cdhl * Real.exp (α * m))) (m + 1 + k₀) with hkmdef
  have hkm_ge_m1 : m + 1 ≤ km := le_trans (by omega) (le_max_right _ _)
  have hkm_ge_k0 : k₀ ≤ km := le_trans (by omega) (le_max_right _ _)
  have hkm_ge1 : 1 ≤ km := by omega
  have hkmR_pos : (0:ℝ) < (km:ℝ) := by exact_mod_cast hkm_ge1
  have hexp_pos : (0:ℝ) < Real.exp (α * m) := Real.exp_pos _
  have hexp_ge1 : (1:ℝ) ≤ Real.exp (α * m) := by
    apply Real.one_le_exp; positivity
  -- A) k ≥ Cdhl exp(αm)
  have hA : Cdhl * Real.exp (α * m) ≤ (km : ℝ) := by
    calc Cdhl * Real.exp (α*m) ≤ (Nat.ceil (Cdhl * Real.exp (α*m)) : ℝ) := Nat.le_ceil _
      _ ≤ (km : ℝ) := by exact_mod_cast le_max_left _ _
  -- DHL + the §3 bridge
  have hDHL : DHL km (m+1) := hDHL_asymp km m hm hA
  have hLim : liminfGap m ≤ (narrowness km : ℕ∞) :=
    dhl_implies_liminfGap km m hkm_ge_m1 hDHL
  -- narrowness bound from IsBigO
  have hNarrowReal : (narrowness km : ℝ) ≤ C₀' * ((km:ℝ) * Real.log km) := by
    have h := hk₀ km hkm_ge_k0
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg
      (by positivity : (0:ℝ) ≤ (km:ℝ) * Real.log km)] at h
    calc (narrowness km : ℝ) ≤ C₀ * ((km:ℝ) * Real.log km) := h
      _ ≤ C₀' * ((km:ℝ) * Real.log km) := by
          gcongr ?_ * _
          exact le_max_left _ _
  -- B) k ≤ C₃ exp(αm)
  have hceil_bd : (Nat.ceil (Cdhl * Real.exp (α*m)) : ℝ) ≤ (Cdhl + 1) * Real.exp (α*m) := by
    have h1 : (Nat.ceil (Cdhl * Real.exp (α*m)) : ℝ) ≤ Cdhl * Real.exp (α*m) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    nlinarith [hexp_ge1, hCdhl_pos]
  have hm1k0_bd : ((m + 1 + k₀ : ℕ) : ℝ) ≤ (1/α + 1 + (k₀:ℝ)) * Real.exp (α*m) := by
    have hmbd : (m : ℝ) + 1 ≤ (1/α + 1) * Real.exp (α * m) := by
      have hαm : (0:ℝ) ≤ α * m := by positivity
      have hexp_ge : 1 + α * m ≤ Real.exp (α * m) := by
        have := Real.add_one_le_exp (α * m); linarith
      have hm_bd : (m : ℝ) ≤ Real.exp (α * m) / α := by
        rw [le_div_iff₀ hα]; nlinarith [hexp_ge]
      calc (m : ℝ) + 1 ≤ Real.exp (α * m) / α + Real.exp (α * m) := by gcongr
        _ = (1/α + 1) * Real.exp (α * m) := by ring
    have hk0bd : (k₀:ℝ) ≤ (k₀:ℝ) * Real.exp (α*m) := by nlinarith [hexp_ge1]
    push_cast
    nlinarith [hmbd, hk0bd]
  have hkm_bd : (km : ℝ) ≤ C₃ * Real.exp (α * m) := by
    rw [hkmdef]
    push_cast [Nat.cast_max]
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · calc (Nat.ceil (Cdhl * Real.exp (α*m)) : ℝ) ≤ (Cdhl + 1) * Real.exp (α*m) := hceil_bd
        _ ≤ C₃ * Real.exp (α*m) := by
            rw [hC₃def]
            nlinarith [hexp_pos, (by positivity : (0:ℝ) ≤ 1/α), (by positivity : (0:ℝ) ≤ (k₀:ℝ))]
    · calc ((m:ℝ) + 1 + (k₀:ℝ)) ≤ (1/α + 1 + (k₀:ℝ)) * Real.exp (α*m) := by
            have := hm1k0_bd; push_cast at this; linarith
        _ ≤ C₃ * Real.exp (α*m) := by rw [hC₃def]; nlinarith [hexp_pos, hCdhl_pos]
  -- C) log k ≤ log C₃ + αm
  have hlogkm : Real.log km ≤ Real.log C₃ + α * m := by
    have h1 : Real.log km ≤ Real.log (C₃ * Real.exp (α*m)) :=
      Real.log_le_log hkmR_pos hkm_bd
    rwa [Real.log_mul (ne_of_gt hC₃_pos) (ne_of_gt hexp_pos), Real.log_exp] at h1
  have hlogkm_nonneg : 0 ≤ Real.log km := Real.log_nonneg (by exact_mod_cast hkm_ge1)
  -- D) k log k ≤ C₅ m exp(αm)
  have hprod : (km:ℝ) * Real.log km ≤ C₅ * m * Real.exp (α*m) := by
    have hmul : (km:ℝ) * Real.log km ≤ (C₃ * Real.exp (α*m)) * (Real.log C₃ + α * m) :=
      mul_le_mul hkm_bd hlogkm hlogkm_nonneg (by positivity)
    have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [hC₅def]
    nlinarith [hmul, hlogC₃_nonneg, hexp_pos, hmR1, hC₃_pos,
      mul_nonneg (mul_nonneg hlogC₃_nonneg (le_of_lt hC₃_pos)) (le_of_lt hexp_pos)]
  -- combine real bounds
  have hfinal_real : (narrowness km : ℝ) ≤ (C₀'*C₅ + 1) * m * Real.exp (α*m) := by
    have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    calc (narrowness km : ℝ) ≤ C₀' * ((km:ℝ) * Real.log km) := hNarrowReal
      _ ≤ C₀' * (C₅ * m * Real.exp (α*m)) := by gcongr
      _ ≤ (C₀'*C₅ + 1) * m * Real.exp (α*m) := by
          nlinarith [hexp_pos, hmR1, mul_nonneg hC₀'_nonneg (le_of_lt hC₅_pos)]
  -- coerce ℕ∞ → ENNReal
  have step1 : (liminfGap m : ENNReal) ≤ ((narrowness km : ℕ∞) : ENNReal) :=
    ENat.toENNReal_le.mpr hLim
  have step2 : ((narrowness km : ℕ∞) : ENNReal) = (narrowness km : ENNReal) := by simp
  have step3 : (narrowness km : ENNReal) ≤
      ENNReal.ofReal ((C₀'*C₅ + 1) * m * Real.exp (α*m)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hfinal_real
  rw [step2] at step1
  exact step1.trans step3

/-! ### Unconditional bounds (Theorem main, (i)-(vi)) -/

/-- **(i)** $H_1 \le 246$. Uses Bombieri-Vinogradov only.

Blueprint: DHL[50, 2] (via BV + Maynard ε-trick) combined with the Engelsma
50-tuple of diameter 246 (admissible, length 50, diameter 246) gives
`BoundedGap 246`, which is equivalent to `liminfGap 1 ≤ 246` by
`liminfGap_one_le_iff`. -/
theorem H1_le_246 : liminfGap 1 ≤ (246 : ℕ∞) := by
  have hDHL : DHL 50 2 := dhl_50_2
  have hBounded : BoundedGap (diameter Engelsma.tuple_50) :=
    dhl_two_implies_boundedGap 50 hDHL
      Engelsma.tuple_50 Engelsma.tuple_50_admissible Engelsma.tuple_50_length
  rw [Engelsma.tuple_50_diameter] at hBounded
  exact (liminfGap_one_le_iff 246).mpr hBounded

/-- **(ii)** $H_2 \le 398{,}130$. Uses Polymath8a MPZ result.

Blueprint: DHL[35410, 3] (via MPZ + maynard_trunc) → $H_2 \le H(35410)$ via
`dhl_implies_liminfGap`, then $H(35410) \le 398{,}130$ via the narrowness
upper bound `narrowness_35410_le`. -/
theorem H2_le_398130 : liminfGap 2 ≤ (398130 : ℕ∞) := by
  have hDHL : DHL 35410 3 := dhl_35410_3
  have h1 : liminfGap 2 ≤ (narrowness 35410 : ℕ∞) :=
    dhl_implies_liminfGap 35410 2 (by norm_num) hDHL
  calc liminfGap 2
      ≤ (narrowness 35410 : ℕ∞) := h1
    _ ≤ (398130 : ℕ∞) := by exact_mod_cast narrowness_35410_le

/-- **(iii)** $H_3 \le 24{,}797{,}814$. Uses Polymath8a MPZ result.

Blueprint: DHL[1649821, 4] → $H_3 \le H(1649821) \le 24{,}797{,}814$. -/
theorem H3_le_24797814 : liminfGap 3 ≤ (24797814 : ℕ∞) := by
  have hDHL : DHL 1649821 4 := dhl_1649821_4
  have h1 : liminfGap 3 ≤ (narrowness 1649821 : ℕ∞) :=
    dhl_implies_liminfGap 1649821 3 (by norm_num) hDHL
  calc liminfGap 3
      ≤ (narrowness 1649821 : ℕ∞) := h1
    _ ≤ (24797814 : ℕ∞) := by exact_mod_cast narrowness_1649821_le

/-- **(iv)** $H_4 \le 1{,}431{,}556{,}072$. Uses Polymath8a MPZ result.

Blueprint: DHL[75845707, 5] → $H_4 \le H(75845707) \le 1{,}431{,}556{,}072$. -/
theorem H4_le_1431556072 : liminfGap 4 ≤ (1431556072 : ℕ∞) := by
  have hDHL : DHL 75845707 5 := dhl_75845707_5
  have h1 : liminfGap 4 ≤ (narrowness 75845707 : ℕ∞) :=
    dhl_implies_liminfGap 75845707 4 (by norm_num) hDHL
  calc liminfGap 4
      ≤ (narrowness 75845707 : ℕ∞) := h1
    _ ≤ (1431556072 : ℕ∞) := by exact_mod_cast narrowness_75845707_le

/-- **(v)** $H_5 \le 80{,}550{,}202{,}480$. Uses Polymath8a MPZ result.

Blueprint: DHL[3473955908, 6] → $H_5 \le H(3473955908) \le 80{,}550{,}202{,}480$. -/
theorem H5_le_80550202480 : liminfGap 5 ≤ (80550202480 : ℕ∞) := by
  have hDHL : DHL 3473955908 6 := dhl_3473955908_6
  have h1 : liminfGap 5 ≤ (narrowness 3473955908 : ℕ∞) :=
    dhl_implies_liminfGap 3473955908 5 (by norm_num) hDHL
  calc liminfGap 5
      ≤ (narrowness 3473955908 : ℕ∞) := h1
    _ ≤ (80550202480 : ℕ∞) := by exact_mod_cast narrowness_3473955908_le

/-- **(vi)** Asymptotic: $H_m \le C m \exp((4 - 28/157) m)$ for an effective $C$.

Blueprint: asymptotic DHL (`dhl_asymptotic_unconditional`) combined with the
narrowness asymptotic upper bound, packaged via `hm_asymp_from_dhl_and_narrowness`. -/
theorem Hm_asymptotic_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp ((4 - 28/157) * m)) := by
  obtain ⟨Cdhl, hCdhl_pos, hDHL_asymp⟩ := dhl_asymptotic_unconditional
  exact hm_asymp_from_dhl_and_narrowness (4 - 28/157) (by norm_num) Cdhl hCdhl_pos
    hDHL_asymp narrowness_asymptotic_upper

/-! ### Under EH[ϑ] for all $0 < \vartheta < 1$ (Theorem main, (vii)-(xi)) -/

/-- **(vii)** Under EH: $H_2 \le 270$.

Blueprint: DHL[54, 3] under EH → $H_2 \le H(54) = 270$ (Engelsma 54-tuple +
Clark-Jarvis lower bound, packaged in `narrowness_54`). -/
theorem H2_le_270_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 2 ≤ (270 : ℕ∞) := by
  have hDHL : DHL 54 3 := dhl_54_3_under_EH hEH
  have h1 : liminfGap 2 ≤ (narrowness 54 : ℕ∞) :=
    dhl_implies_liminfGap 54 2 (by norm_num) hDHL
  calc liminfGap 2
      ≤ (narrowness 54 : ℕ∞) := h1
    _ = (270 : ℕ∞) := by rw [narrowness_54]; norm_cast

/-- **(viii)** Under EH: $H_3 \le 52{,}116$.

Blueprint: DHL[5511, 4] under EH → $H_3 \le H(5511) \le 52{,}116$. -/
theorem H3_le_52116_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 3 ≤ (52116 : ℕ∞) := by
  have hDHL : DHL 5511 4 := dhl_5511_4_under_EH hEH
  have h1 : liminfGap 3 ≤ (narrowness 5511 : ℕ∞) :=
    dhl_implies_liminfGap 5511 3 (by norm_num) hDHL
  calc liminfGap 3
      ≤ (narrowness 5511 : ℕ∞) := h1
    _ ≤ (52116 : ℕ∞) := by exact_mod_cast narrowness_5511_le

/-- **(ix)** Under EH: $H_4 \le 474{,}266$.

Blueprint: DHL[41588, 5] under EH → $H_4 \le H(41588) \le 474{,}266$. -/
theorem H4_le_474266_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 4 ≤ (474266 : ℕ∞) := by
  have hDHL : DHL 41588 5 := dhl_41588_5_under_EH hEH
  have h1 : liminfGap 4 ≤ (narrowness 41588 : ℕ∞) :=
    dhl_implies_liminfGap 41588 4 (by norm_num) hDHL
  calc liminfGap 4
      ≤ (narrowness 41588 : ℕ∞) := h1
    _ ≤ (474266 : ℕ∞) := by exact_mod_cast narrowness_41588_le

/-- **(x)** Under EH: $H_5 \le 4{,}137{,}854$.

Blueprint: DHL[309661, 6] under EH → $H_5 \le H(309661) \le 4{,}137{,}854$. -/
theorem H5_le_4137854_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    liminfGap 5 ≤ (4137854 : ℕ∞) := by
  have hDHL : DHL 309661 6 := dhl_309661_6_under_EH hEH
  have h1 : liminfGap 5 ≤ (narrowness 309661 : ℕ∞) :=
    dhl_implies_liminfGap 309661 5 (by norm_num) hDHL
  calc liminfGap 5
      ≤ (narrowness 309661 : ℕ∞) := h1
    _ ≤ (4137854 : ℕ∞) := by exact_mod_cast narrowness_309661_le

/-- **(xi)** Under EH, asymptotic: $H_m \le C m \exp(2m)$ for an effective $C$.

Blueprint: same combinator as (vi), but at the sharper EH exponent $2m$. -/
theorem Hm_asymptotic_under_EH
    (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp (2 * m)) := by
  obtain ⟨Cdhl, hCdhl_pos, hDHL_asymp⟩ := dhl_asymptotic_under_EH hEH
  exact hm_asymp_from_dhl_and_narrowness 2 (by norm_num) Cdhl hCdhl_pos
    hDHL_asymp narrowness_asymptotic_upper

/-! ### Under GEH[ϑ] for all $0 < \vartheta < 1$ (Theorem main, (xii)-(xiii))

These are the **parity-barrier optimal** results. The bound $H_1 \le 6$ is the
best possible from sieve-theoretic methods alone (Polymath8b §7, heuristic;
see §7 comment block below — not formalized in this project). -/

/-- **(xii)** Under GEH: $H_1 \le 6$.

This is the parity-barrier-tight bound. Blueprint: DHL[3, 2] under GEH +
the admissible 3-tuple $(0, 2, 6)$ of diameter 6 gives `BoundedGap 6`,
equivalent to `liminfGap 1 ≤ 6` by `liminfGap_one_le_iff`. -/
theorem H1_le_6_under_GEH (hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    liminfGap 1 ≤ (6 : ℕ∞) := by
  have hDHL : DHL 3 2 := dhl_3_2_under_GEH hGEH
  have hBounded : BoundedGap (diameter (admissibleTuple 3)) :=
    dhl_two_implies_boundedGap 3 hDHL
      (admissibleTuple 3) admissibleTuple_3_admissible admissibleTuple_length_3
  have hDiam : diameter (admissibleTuple 3) = 6 := by decide
  rw [hDiam] at hBounded
  exact (liminfGap_one_le_iff 6).mpr hBounded

/-- **(xiii)** Under GEH: $H_2 \le 252$.

Blueprint: DHL[51, 3] under GEH → $H_2 \le H(51) = 252$ (Engelsma 51-tuple +
Clark-Jarvis lower bound, packaged in `narrowness_51`). -/
theorem H2_le_252_under_GEH (hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    liminfGap 2 ≤ (252 : ℕ∞) := by
  have hDHL : DHL 51 3 := dhl_51_3_under_GEH hGEH
  have h1 : liminfGap 2 ≤ (narrowness 51 : ℕ∞) :=
    dhl_implies_liminfGap 51 2 (by norm_num) hDHL
  calc liminfGap 2
      ≤ (narrowness 51 : ℕ∞) := h1
    _ = (252 : ℕ∞) := by rw [narrowness_51]; norm_cast

/-! ## §7 — The parity barrier (heuristic; not formalized)

**Polymath8b §7 (after Selberg) — the parity barrier.** No purely
sieve-theoretic argument can establish $H_1 \le 4$, even under the
generalized Elliott-Halberstam conjecture. Equivalently, the parity-tight
bound from this framework is $H_1 \le 6$ (Theorem `H1_le_6_under_GEH`
above).

**Why this is a comment block, not an `axiom`** (cleanup 2026-05-27,
ROADMAP Tier 2): "sieve-theoretic argument" is not a formal predicate
in Lean. A previous version encoded the barrier as a pair of axioms
(`SieveTheoreticArgument : Prop → Prop` + `parity_barrier : ¬ STA (H_1
≤ 4)`), but the wrapper was opaque with no destructor, so `parity_barrier`
asserted nothing checkable — pure documentation-as-axiom, never consumed
by any theorem. Removed because `axiom` should be for citations the
trust base needs; not for heuristic prose.

A *formal* version would require reformulating the parity barrier as a
precise non-existence claim about a specific class of weight functions
(e.g. Selberg-type squares $\nu = (\sum_j c_j \prod_i \lambda_{F_{j,i}})^2$
and a precise asymptotic threshold). Polymath8b doesn't do this either;
the §7 statement is informal. Future PR could attempt the formal version
if the substantive Polymath8b §7 argument is mechanized. -/

/-! ## §8 — The twin-primes-or-Goldbach disjunction (Theorem disj) -/

/-- **Twin Primes Conjecture**: there are infinitely many primes $p$ with
$p + 2$ also prime. Equivalently, $H_1 = 2$. -/
def TwinPrimesConjecture : Prop :=
  Set.Infinite { p : ℕ | p.Prime ∧ (p + 2).Prime }

/-- **Near-miss Goldbach** (Polymath8b Theorem 1.4(b)): for every sufficiently
large multiple of 6, *both* of the following hold — at least one of $n, n-2$
is a sum of two primes, and at least one of $n, n+2$ is also.

(I.e., every sufficiently large even number lies within 2 of a sum of two
primes.) -/
def NearMissGoldbach : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, 6 ∣ n →
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨
     (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 2 = p + q)) ∧
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨
     (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n + 2 = p + q))

/-- **Polymath8b Theorem 1.4 (disjunction)**: under GEH, at least one of
the twin primes conjecture or the near-miss Goldbach statement holds. -/
-- TRIAGE: BLUEPRINT — Polymath8b §8 proof uses Maynard sieve applied to
-- pairs (n, n+2) with weight that detects either both prime (twin) or
-- prime-pair representations (Goldbach). Large lift: depends on the full
-- maynard/epsilon_beyond + Goldbach-pair density estimates. ~weeks of work.
theorem twin_primes_or_near_miss_Goldbach
    (_hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    TwinPrimesConjecture ∨ NearMissGoldbach := sorry

end BoundedGaps.Polymath8b

