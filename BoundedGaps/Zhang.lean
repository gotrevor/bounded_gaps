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

namespace BoundedGaps.Zhang

open BoundedGaps

/-- **Zhang's theorem** (2013): $H_1 \le 70{,}000{,}000$.

Proof needs MPZ at $\varpi, \delta < 1/1168$ in Zhang's original argument
(superseded by Polymath8a's $600\varpi + 180\delta < 7$). -/
theorem H1_le_70M
    (_hMPZ : Prerequisites.MPZ (1 / 1200) (1 / 1200)) :
    liminfGap 1 ≤ (70000000 : ℕ∞) := sorry

end BoundedGaps.Zhang
