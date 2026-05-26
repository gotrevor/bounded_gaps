/-
# Zhang 2013 — Bounded gaps between primes.

The 70-million breakthrough. Proof relies on the MPZ distributional estimate
(a strengthening of Bombieri-Vinogradov to smooth moduli with level of
distribution > 1/2). In Polymath8a this was sharpened to
$\MPZ[\varpi, \delta]$ with $600\varpi + 180\delta < 7$.

Reference: Zhang, "Bounded gaps between primes", Annals of Math 179 (2014).
Local copy: [../papers/pdf/zhang-2014-bounded-gaps.pdf](../papers/pdf/zhang-2014-bounded-gaps.pdf)
(Annals-only — no arXiv source.)
-/
import Mathlib
import BoundedGaps.Basic
import BoundedGaps.Prerequisites
import BoundedGaps.Polymath8b

namespace BoundedGaps.Zhang

open BoundedGaps

/-- **Zhang's theorem** (2013): $H_1 \le 70{,}000{,}000$.

Proof needs MPZ at $\varpi, \delta < 1/1168$ in Zhang's original argument
(superseded by Polymath8a's $600\varpi + 180\delta < 7$). This is the
*method-faithful* version: aiming at Zhang's actual GPY + MPZ-based sieve
proof. Currently a sorry; see `H1_le_70M_via_Polymath8b` below for the
*result-only* corollary that ships free as a consequence of the stronger
Polymath8b bound. -/
-- TRIAGE: NEEDS_SIEVE — Zhang's original GPY+MPZ argument. Uses MPZ as
-- hypothesis (now a clean axiom). Needs a Zhang-specific sieve weight setup
-- (different from Maynard's multidimensional sieve). ~bigger ticket; would
-- not start until the Maynard chain (Sieve.dhl_criterion + maynard_thm) is up.
theorem H1_le_70M
    (_hMPZ : Prerequisites.MPZ (1 / 1200) (1 / 1200)) :
    liminfGap 1 ≤ (70000000 : ℕ∞) := sorry

/-- **Zhang's bound as a corollary of Polymath8b**: the *result* of Zhang's
theorem (H_1 ≤ 70,000,000) is subsumed by Polymath8b's stronger H_1 ≤ 246
(`Polymath8b.H1_le_246`). This routes the Zhang bound through the (better,
more recent) Maynard-Polymath8b chain, dropping the MPZ hypothesis that
Zhang's *method* required.

This is the result-only version; for the historical method-faithful
formalization (which would actually walk Zhang's GPY+MPZ argument), see
`H1_le_70M` above. -/
theorem H1_le_70M_via_Polymath8b : liminfGap 1 ≤ (70000000 : ℕ∞) := by
  calc liminfGap 1
      ≤ (246 : ℕ∞) := Polymath8b.H1_le_246
    _ ≤ (70000000 : ℕ∞) := by norm_num

end BoundedGaps.Zhang
