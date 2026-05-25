/-
# Explicit narrow admissible tuples.

The five tuples that determine the current and adjacent bounds on $H_1$:

| k  | diameter | source                              | bound it gives (if $M_k > 4$) |
|----|----------|-------------------------------------|-------------------------------|
| 48 | 236      | Engelsma table (MIT primegaps)      | $H_1 \le 236$ (would lower by 10) |
| 49 | 240      | Engelsma table (MIT primegaps)      | $H_1 \le 240$ (would lower by 6)  |
| 50 | 246      | Polymath8b §8, Engelsma 50-tuple    | $H_1 \le 246$ (current)       |
| 51 | 252      | Engelsma table (MIT primegaps)      | $H_1 \le 252$ (loosens by 6)  |
| 54 | 270      | Engelsma table (MIT primegaps)      | $H_1 \le 270$ (loosens by 24) |

$H(k)$ values are *exact* for $k \le 342$ (Clark-Jarvis 2001, Polymath8b §8.1),
so these are the actual narrowest tuples — there is no admissible 50-tuple of
diameter $< 246$, etc.

The path to improvement: prove $M_k > 4$ for $k = 49$ (resp. 48). Polymath8b
hit a wall here with their polynomial sieve weights; an improved basis (e.g.
piecewise polynomials with carefully chosen polytope supports — see §7
"Additional remarks", item 2) could plausibly cross the threshold.

The k=51 and k=54 tuples come into play under stronger hypotheses: Polymath8b
proves $\mathrm{DHL}[51, 3]$ under GEH, giving $H_2 \le 252$, and uses larger
tuples for the asymptotic chain.

Sources:
- Polymath8b §8 (the 50-tuple is reproduced explicitly there)
- MIT primegaps server: <http://math.mit.edu/~primegaps/tuples/>
- Local copies: [../papers/tuples/admissible_50_246.txt](../papers/tuples/admissible_50_246.txt) etc.
-/
import Mathlib
import BoundedGaps.Basic

-- These are finite, decidable checks on concrete data; `native_decide` is the
-- right tool here, but we acknowledge it trusts the Lean compiler.
set_option linter.style.nativeDecide false

namespace BoundedGaps.Engelsma

/-! ## The three target tuples -/

/-- Engelsma's 50-tuple of diameter 246. Matches Polymath8b §8 exactly. -/
def tuple_50 : List ℕ :=
  [0, 4, 6, 16, 30, 34, 36, 46, 48, 58, 60, 64, 70, 78, 84, 88, 90, 94, 100, 106,
   108, 114, 118, 126, 130, 136, 144, 148, 150, 156, 160, 168, 174, 178, 184,
   190, 196, 198, 204, 210, 214, 216, 220, 226, 228, 234, 238, 240, 244, 246]

/-- Engelsma's 49-tuple of diameter 240. Source: MIT primegaps server. -/
def tuple_49 : List ℕ :=
  [0, 4, 10, 12, 18, 22, 28, 30, 52, 54, 58, 60, 64, 70, 72, 78, 82, 84, 88, 94,
   100, 102, 108, 114, 120, 124, 130, 138, 142, 148, 154, 162, 168, 172, 180,
   184, 190, 192, 198, 204, 208, 210, 214, 220, 228, 232, 234, 238, 240]

/-- Engelsma's 48-tuple of diameter 236. Source: MIT primegaps server. -/
def tuple_48 : List ℕ :=
  [0, 6, 8, 14, 18, 24, 26, 48, 50, 54, 56, 60, 66, 68, 74, 78, 80, 84, 90, 96,
   98, 104, 110, 116, 120, 126, 134, 138, 144, 150, 158, 164, 168, 176, 180,
   186, 188, 194, 200, 204, 206, 210, 216, 224, 228, 230, 234, 236]

/-- Engelsma's 51-tuple of diameter 252. Source: MIT primegaps server. -/
def tuple_51 : List ℕ :=
  [0, 6, 10, 12, 22, 36, 40, 42, 52, 54, 64, 66, 70, 76, 84, 90, 94, 96, 100, 106,
   112, 114, 120, 124, 132, 136, 142, 150, 154, 156, 162, 166, 174, 180, 184, 190,
   196, 202, 204, 210, 216, 220, 222, 226, 232, 234, 240, 244, 246, 250, 252]

/-- Engelsma's 54-tuple of diameter 270. Source: MIT primegaps server. -/
def tuple_54 : List ℕ :=
  [0, 4, 10, 18, 24, 28, 30, 40, 54, 58, 60, 70, 72, 82, 84, 88, 94, 102, 108,
   112, 114, 118, 124, 130, 132, 138, 142, 150, 154, 160, 168, 172, 174, 180,
   184, 192, 198, 202, 208, 214, 220, 222, 228, 234, 238, 240, 244, 250, 252,
   258, 262, 264, 268, 270]

/-! ## Length + diameter + sortedness — finite checks, mechanically verified -/

theorem tuple_50_length : tuple_50.length = 50 := by native_decide
theorem tuple_49_length : tuple_49.length = 49 := by native_decide
theorem tuple_48_length : tuple_48.length = 48 := by native_decide
theorem tuple_51_length : tuple_51.length = 51 := by native_decide
theorem tuple_54_length : tuple_54.length = 54 := by native_decide

theorem tuple_50_diameter : diameter tuple_50 = 246 := by native_decide
theorem tuple_49_diameter : diameter tuple_49 = 240 := by native_decide
theorem tuple_48_diameter : diameter tuple_48 = 236 := by native_decide
theorem tuple_51_diameter : diameter tuple_51 = 252 := by native_decide
theorem tuple_54_diameter : diameter tuple_54 = 270 := by native_decide

theorem tuple_50_sorted : tuple_50.Pairwise (· < ·) := by native_decide
theorem tuple_49_sorted : tuple_49.Pairwise (· < ·) := by native_decide
theorem tuple_48_sorted : tuple_48.Pairwise (· < ·) := by native_decide
theorem tuple_51_sorted : tuple_51.Pairwise (· < ·) := by native_decide
theorem tuple_54_sorted : tuple_54.Pairwise (· < ·) := by native_decide

/-! ## Admissibility — the hard part

For each of these tuples we need to show: ∀ p prime, ∃ r : ZMod p, the offsets
miss class r.

**Reduction**: for any prime $p > k$, the tuple has only $k$ offsets but $p$
residue classes, so by pigeonhole some class is missed. So admissibility
reduces to a *finite check* on primes $p \le k$ — for $k = 50$, that's the
15 primes $\{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47\}$.

The Engelsma tables were *constructed* by exactly this finite check (using
greedy / simulated-annealing search across residue choices), so admissibility
is empirically verified — we just don't yet have the Lean machinery to
discharge it via `native_decide` without first proving the pigeonhole
reduction lemma. Left for follow-up. -/

theorem tuple_50_admissible : Admissible tuple_50 := by
  apply admissible_of_check_small_primes tuple_50_sorted
  intro p hp hple
  rw [tuple_50_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

theorem tuple_49_admissible : Admissible tuple_49 := by
  apply admissible_of_check_small_primes tuple_49_sorted
  intro p hp hple
  rw [tuple_49_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

theorem tuple_48_admissible : Admissible tuple_48 := by
  apply admissible_of_check_small_primes tuple_48_sorted
  intro p hp hple
  rw [tuple_48_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

theorem tuple_51_admissible : Admissible tuple_51 := by
  apply admissible_of_check_small_primes tuple_51_sorted
  intro p hp hple
  rw [tuple_51_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

theorem tuple_54_admissible : Admissible tuple_54 := by
  apply admissible_of_check_small_primes tuple_54_sorted
  intro p hp hple
  rw [tuple_54_length] at hple
  have hp2 := hp.two_le
  interval_cases p <;>
    first
      | (exfalso; revert hp; decide)
      | native_decide

/-! ## Narrowness upper bounds

Each Engelsma tuple is an admissible $k$-tuple of known diameter, so it
witnesses an upper bound on $H(k) = $ `narrowness k`. The matching lower
bound (e.g. $H(50) \ge 246$) is exact for $k \le 342$ by Clark-Jarvis
(2001) but requires exhaustive enumeration — out of current scope. -/

/-- $H(50) \le 246$: the Engelsma 50-tuple of diameter 246 is admissible. -/
theorem narrowness_50_le_246 : narrowness 50 ≤ 246 :=
  narrowness_le_of_admissible_tuple tuple_50_admissible tuple_50_length tuple_50_diameter

/-- $H(49) \le 240$: the Engelsma 49-tuple of diameter 240 is admissible. -/
theorem narrowness_49_le_240 : narrowness 49 ≤ 240 :=
  narrowness_le_of_admissible_tuple tuple_49_admissible tuple_49_length tuple_49_diameter

/-- $H(48) \le 236$: the Engelsma 48-tuple of diameter 236 is admissible. -/
theorem narrowness_48_le_236 : narrowness 48 ≤ 236 :=
  narrowness_le_of_admissible_tuple tuple_48_admissible tuple_48_length tuple_48_diameter

/-- $H(51) \le 252$: the Engelsma 51-tuple of diameter 252 is admissible. -/
theorem narrowness_51_le_252 : narrowness 51 ≤ 252 :=
  narrowness_le_of_admissible_tuple tuple_51_admissible tuple_51_length tuple_51_diameter

/-- $H(54) \le 270$: the Engelsma 54-tuple of diameter 270 is admissible. -/
theorem narrowness_54_le_270 : narrowness 54 ≤ 270 :=
  narrowness_le_of_admissible_tuple tuple_54_admissible tuple_54_length tuple_54_diameter

end BoundedGaps.Engelsma
