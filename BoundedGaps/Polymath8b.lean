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
import BoundedGaps.Maynard
import BoundedGaps.Engelsma

namespace BoundedGaps.Polymath8b

open BoundedGaps

/-! ## §3 — The DHL reformulation (Theorem main-dhl)

The numerical bounds in §1 (Theorem main) all factor through DHL[k, j] claims.

Each DHL claim below is blueprint-split into an application of one of
`Sieve.{maynard_thm, maynard_trunc, epsilon_trick, epsilon_beyond}` together
with the matching $M_k$ (or $M_{k, \varepsilon}$) numerical witness — a
focused sorry stating the specific variational inequality Polymath8b §6
establishes by direct numerical (Maple) computation. -/

/-! ### Mk-witness leaves (Polymath8b §6 numerical claims)

These are the leaf sorries the §3 DHL chains route through. Each captures a
specific variational inequality that Polymath8b §6 establishes via direct
numerical computation on the Maynard quadratic form on the simplex. -/

/-- Polymath8b §6: $\exists \varepsilon > 0$ with $M_{50, \varepsilon} > 4$.
Drives DHL[50, 2] via `Sieve.epsilon_trick`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical; Polymath8b reports M_{50,ε} ≈ 4.0019.
theorem mk_eps_50_witness : ∃ ε : ℝ, 0 < ε ∧ Sieve.Mk_eps 50 ε > 4 * 1 := sorry

/-- Polymath8b §6: MPZ parameters $\varpi, \delta$ with $M_{35410} > 8/(1/2 + 2\varpi)$.
Drives DHL[35410, 3] via `Sieve.maynard_trunc`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical; Polymath8a §2 + Polymath8b §6.
theorem mk_35410_witness :
    ∃ ϖ δ : ℝ, Prerequisites.MPZ ϖ δ ∧ Sieve.Mk 35410 > 4 * 2 / (1/2 + 2 * ϖ) := sorry

/-- Polymath8b §6: MPZ parameters and $M_{1649821} > 12/(1/2 + 2\varpi)$.
Drives DHL[1649821, 4] via `Sieve.maynard_trunc`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical.
theorem mk_1649821_witness :
    ∃ ϖ δ : ℝ, Prerequisites.MPZ ϖ δ ∧ Sieve.Mk 1649821 > 4 * 3 / (1/2 + 2 * ϖ) := sorry

/-- Polymath8b §6: MPZ parameters and $M_{75845707} > 16/(1/2 + 2\varpi)$.
Drives DHL[75845707, 5] via `Sieve.maynard_trunc`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical.
theorem mk_75845707_witness :
    ∃ ϖ δ : ℝ, Prerequisites.MPZ ϖ δ ∧ Sieve.Mk 75845707 > 4 * 4 / (1/2 + 2 * ϖ) := sorry

/-- Polymath8b §6: MPZ parameters and $M_{3473955908} > 20/(1/2 + 2\varpi)$.
Drives DHL[3473955908, 6] via `Sieve.maynard_trunc`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical.
theorem mk_3473955908_witness :
    ∃ ϖ δ : ℝ, Prerequisites.MPZ ϖ δ ∧ Sieve.Mk 3473955908 > 4 * 5 / (1/2 + 2 * ϖ) := sorry

/-- Polymath8b §6: $\vartheta \in (0, 1)$ with $M_{54} > 8/\vartheta$ for DHL[54, 3]
under EH. Drives `dhl_54_3_under_EH` via `Sieve.maynard_thm`. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, EH-flavored.
theorem mk_54_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 54 > 4 * 2 / ϑ := sorry

/-- Polymath8b §6: $M_{5511} > 12/\vartheta$ for DHL[5511, 4] under EH. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, EH-flavored.
theorem mk_5511_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 5511 > 4 * 3 / ϑ := sorry

/-- Polymath8b §6: $M_{41588} > 16/\vartheta$ for DHL[41588, 5] under EH. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, EH-flavored.
theorem mk_41588_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 41588 > 4 * 4 / ϑ := sorry

/-- Polymath8b §6: $M_{309661} > 20/\vartheta$ for DHL[309661, 6] under EH. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, EH-flavored.
theorem mk_309661_witness_under_EH :
    ∃ ϑ : ℝ, (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk 309661 > 4 * 5 / ϑ := sorry

/-- Polymath8b §6: $\varepsilon, \vartheta$ with $M_{3, \varepsilon} > 2/\vartheta$
for DHL[3, 2] under GEH. The parity-tight flagship. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, GEH-flavored, the parity-tight k=3 case.
theorem mk_eps_3_witness_under_GEH :
    ∃ ε ϑ : ℝ, 0 < ε ∧ (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk_eps 3 ε > 2 * 1 / ϑ := sorry

/-- Polymath8b §6: $\varepsilon, \vartheta$ with $M_{51, \varepsilon} > 4/\vartheta$
for DHL[51, 3] under GEH. -/
-- TRIAGE: BLUEPRINT_LEAF — numerical, GEH-flavored.
theorem mk_eps_51_witness_under_GEH :
    ∃ ε ϑ : ℝ, 0 < ε ∧ (0 < ϑ ∧ ϑ < 1) ∧ Sieve.Mk_eps 51 ε > 2 * 2 / ϑ := sorry

/-! ### DHL[k, m+1] claims (chained through Sieve.maynard_* + Mk witnesses) -/

/-- **DHL[50, 2]** unconditional → $H_1 \le H(50) = 246$.

Blueprint: ε-trick at $k=50, m=1$ with the §6 numerical witness `mk_eps_50_witness`. -/
theorem dhl_50_2 : DHL 50 2 := by
  obtain ⟨ε, hε, hMk⟩ := mk_eps_50_witness
  exact Sieve.epsilon_trick 50 1 ε hε (by exact_mod_cast hMk)

/-- **DHL[35410, 3]** unconditional.

Blueprint: maynard_trunc at $k=35410, m=2$ with MPZ parameters from `mk_35410_witness`. -/
theorem dhl_35410_3 : DHL 35410 3 := by
  obtain ⟨ϖ, δ, hMPZ, hMk⟩ := mk_35410_witness
  exact Sieve.maynard_trunc 35410 2 ϖ δ hMPZ hMk

/-- **DHL[1649821, 4]** unconditional. -/
theorem dhl_1649821_4 : DHL 1649821 4 := by
  obtain ⟨ϖ, δ, hMPZ, hMk⟩ := mk_1649821_witness
  exact Sieve.maynard_trunc 1649821 3 ϖ δ hMPZ hMk

/-- **DHL[75845707, 5]** unconditional. -/
theorem dhl_75845707_5 : DHL 75845707 5 := by
  obtain ⟨ϖ, δ, hMPZ, hMk⟩ := mk_75845707_witness
  exact Sieve.maynard_trunc 75845707 4 ϖ δ hMPZ hMk

/-- **DHL[3473955908, 6]** unconditional. -/
theorem dhl_3473955908_6 : DHL 3473955908 6 := by
  obtain ⟨ϖ, δ, hMPZ, hMk⟩ := mk_3473955908_witness
  exact Sieve.maynard_trunc 3473955908 5 ϖ δ hMPZ hMk

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
  exact Sieve.maynard_thm 54 2 ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[5511, 4]**. -/
theorem dhl_5511_4_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 5511 4 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_5511_witness_under_EH
  exact Sieve.maynard_thm 5511 3 ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[41588, 5]**. -/
theorem dhl_41588_5_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 41588 5 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_41588_witness_under_EH
  exact Sieve.maynard_thm 41588 4 ϑ hϑ (hEH ϑ hϑ) hMk

/-- Under EH: **DHL[309661, 6]**. -/
theorem dhl_309661_6_under_EH (hEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.EH ϑ) :
    DHL 309661 6 := by
  obtain ⟨ϑ, hϑ, hMk⟩ := mk_309661_witness_under_EH
  exact Sieve.maynard_thm 309661 5 ϑ hϑ (hEH ϑ hϑ) hMk

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
  obtain ⟨ε, ϑ, hε, hϑ, hMk⟩ := mk_eps_3_witness_under_GEH
  exact Sieve.epsilon_beyond 3 1 ε ϑ (hGEH ϑ hϑ) hε (by exact_mod_cast hMk)

/-- Under GEH: **DHL[51, 3]**. -/
theorem dhl_51_3_under_GEH (hGEH : ∀ ϑ : ℝ, 0 < ϑ ∧ ϑ < 1 → Prerequisites.GEH ϑ) :
    DHL 51 3 := by
  obtain ⟨ε, ϑ, hε, hϑ, hMk⟩ := mk_eps_51_witness_under_GEH
  exact Sieve.epsilon_beyond 51 2 ε ϑ (hGEH ϑ hϑ) hε hMk

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

/-- **$H(50) = 246$**: an admissible 50-tuple of diameter 246 exists, and no
narrower one. The 246 bound. The $\le 246$ direction is now proven via
`Engelsma.narrowness_50_le_246` (the Engelsma 50-tuple witnesses it); the
$\ge 246$ direction (no admissible 50-tuple has smaller diameter) is exact
by Clark-Jarvis 2001 for $k \le 342$ but requires exhaustive enumeration. -/
theorem narrowness_50 : narrowness 50 = 246 := by
  apply le_antisymm
  · exact Engelsma.narrowness_50_le_246
  -- TRIAGE: CLARK_JARVIS — exhaustive enumeration, exact for k ≤ 342 in
  -- Clark-Jarvis 2001. Stays sorry; not in this project's scope. To replace
  -- with a real proof you'd need a verified search procedure over candidate
  -- 50-tuples of diameter < 246 with admissibility check — substantial.
  · sorry  -- ≥ 246: Clark-Jarvis exhaustive enumeration, out of current scope

/-- $H(51) = 252$. The $\le 252$ direction is proven via
`Engelsma.narrowness_51_le_252` (the Engelsma 51-tuple witnesses it); the
$\ge 252$ direction is exact by Clark-Jarvis (2001) for $k \le 342$ but
requires exhaustive enumeration. -/
theorem narrowness_51 : narrowness 51 = 252 := by
  apply le_antisymm
  · exact Engelsma.narrowness_51_le_252
  -- TRIAGE: CLARK_JARVIS — same status as narrowness_50.
  · sorry  -- ≥ 252: Clark-Jarvis exhaustive enumeration, out of current scope

/-- $H(54) = 270$. The $\le 270$ direction is proven via
`Engelsma.narrowness_54_le_270` (the Engelsma 54-tuple witnesses it); the
$\ge 270$ direction is exact by Clark-Jarvis (2001) for $k \le 342$ but
requires exhaustive enumeration. -/
theorem narrowness_54 : narrowness 54 = 270 := by
  apply le_antisymm
  · exact Engelsma.narrowness_54_le_270
  -- TRIAGE: CLARK_JARVIS — same status as narrowness_50.
  · sorry  -- ≥ 270: Clark-Jarvis exhaustive enumeration, out of current scope

-- LARGE-k NARROWNESS BOUNDS — all 7 below: each would land if we ran the
-- tuple harvest at that k (analogous to today's k=51, k=54 harvest from MIT
-- primegaps). At k > ~1000 the harvest is non-trivial — Engelsma's database
-- caps at moderate k, and `native_decide` admissibility may stop scaling.
-- For very large k (35410+) admissibility must use an asymptotic construction
-- (e.g. greedy/Erdős-style), not direct enumeration.

/-- $H(5511) \le 52116$. -/
-- TRIAGE: TUPLE_HARVEST — check if MIT primegaps has admissible_5511_52116;
-- if yes, mechanical extension of today's PR #2. If no, needs construction.
theorem narrowness_5511_le : narrowness 5511 ≤ 52116 := sorry

/-- $H(35410) \le 398130$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — too large for Engelsma database. Needs
-- explicit asymptotic admissible-tuple construction (Hensley-Richards or
-- analogous greedy). Larger lift.
theorem narrowness_35410_le : narrowness 35410 ≤ 398130 := sorry

/-- $H(41588) \le 474266$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — same status as 35410.
theorem narrowness_41588_le : narrowness 41588 ≤ 474266 := sorry

/-- $H(309661) \le 4137854$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — same status, larger k.
theorem narrowness_309661_le : narrowness 309661 ≤ 4137854 := sorry

/-- $H(1649821) \le 24797814$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — same status, larger k.
theorem narrowness_1649821_le : narrowness 1649821 ≤ 24797814 := sorry

/-- $H(75845707) \le 1431556072$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — same status, very large k.
theorem narrowness_75845707_le : narrowness 75845707 ≤ 1431556072 := sorry

/-- $H(3473955908) \le 80550202480$. -/
-- TRIAGE: ASYMPTOTIC_TUPLE — same status, k ≈ 3.5×10⁹.
theorem narrowness_3473955908_le : narrowness 3473955908 ≤ 80550202480 := sorry

/-- Asymptotic upper bound: $H(k) \le k \log k + k \log \log k - k + o(k)$. -/
-- TRIAGE: PROVABLE (~3-5h) — Hensley-Richards 1973 type construction
-- (admissible tuples from primes in a window). Mathlib has the prerequisites
-- (PNT-like prime-counting bounds); the construction itself is elementary.
theorem narrowness_asymptotic_upper :
    (fun k : ℕ => (narrowness k : ℝ))
      =O[Filter.atTop]
      (fun k : ℕ => (k : ℝ) * Real.log k) := sorry

/-- Brun-Titchmarsh lower bound: $H(k) \ge (\tfrac12 + o(1)) k \log k$. -/
-- TRIAGE: NEEDS_PREREQ — Brun-Titchmarsh sieve bound on primes in short
-- intervals. Mathlib does not have this; would need to be axiomatized or
-- separately formalized. Adjacent to BV territory.
theorem narrowness_asymptotic_lower :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in Filter.atTop,
      (narrowness k : ℝ) ≥ (1/2 - ε) * k * Real.log k := sorry

/-! ## §1 — Main Theorem (Theorem 1.3 in the paper, labeled `main`)

All bounds are stated as `liminfGap m ≤ (constant : ℕ∞)`.

Each bound below is blueprint-split: the proof body chains through a §3 DHL
claim, a §3 narrowness bound, and one of the `Basic.dhl_*_implies_*` bridges.
The chain is type-checked even though individual leaves remain `sorry`. -/

/-! ### Asymptotic combinator (helper for the asymptotic §1 bounds) -/

/-- Bookkeeping combinator: an asymptotic DHL claim together with the
narrowness $=O(k \log k)$ bound produces an asymptotic $H_m$ bound at the
matching exponent. -/
-- TRIAGE: BLUEPRINT_LEAF — pure bookkeeping (pick k = ⌈C * exp(α m)⌉, apply
-- DHL there, transfer narrowness bound through `dhl_implies_liminfGap`,
-- absorb constants into the output `C`). ~50 lines of Filter/asymptotics
-- plumbing; no deep math beyond the asymptotics calculus already in mathlib.
theorem hm_asymp_from_dhl_and_narrowness (α : ℝ)
    (Cdhl : ℝ) (_hCdhl_pos : 0 < Cdhl)
    (_hDHL_asymp : ∀ k m : ℕ, m ≥ 1 →
      (k : ℝ) ≥ Cdhl * Real.exp (α * m) → DHL k (m + 1))
    (_hNarrow_asymp : (fun k : ℕ => (narrowness k : ℝ))
        =O[Filter.atTop] (fun k : ℕ => (k : ℝ) * Real.log k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≥ 1 →
      (liminfGap m : ENNReal) ≤ ENNReal.ofReal (C * m * Real.exp (α * m)) := sorry

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
  exact hm_asymp_from_dhl_and_narrowness (4 - 28/157) Cdhl hCdhl_pos
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
  exact hm_asymp_from_dhl_and_narrowness 2 Cdhl hCdhl_pos
    hDHL_asymp narrowness_asymptotic_upper

/-! ### Under GEH[ϑ] for all $0 < \vartheta < 1$ (Theorem main, (xii)-(xiii))

These are the **parity-barrier optimal** results. The bound $H_1 \le 6$ is the
best possible from sieve-theoretic methods alone (Theorem parity_barrier below). -/

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

/-! ## §7 — The parity barrier -/

/-- **The parity barrier** (Polymath8b §7, after Selberg): no purely
sieve-theoretic argument can establish $H_1 \le 4$, even under the
generalized Elliott-Halberstam conjecture.

Statement is informal — "sieve-theoretic" isn't a formal predicate. Captured
here as a propositional placeholder for the paper's heuristic theorem. -/
axiom SieveTheoreticArgument (proves : Prop) : Prop

-- TRIAGE: META — "sieve-theoretic argument" is not a formal predicate. This
-- theorem cannot be proven *as stated* without first axiomatizing what it
-- means for an argument to be sieve-theoretic. Two reasonable end-states:
-- (a) leave as sorry indefinitely (informal placeholder for the paper's
-- heuristic claim); (b) reformulate as a precise non-existence claim about a
-- specific class of weight functions. Stays sorry; consider deletion if
-- structurally honest.
theorem parity_barrier :
    ¬ SieveTheoreticArgument (liminfGap 1 ≤ (4 : ℕ∞)) := sorry

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
