/-
# Bounded Gaps Between Primes — top-level imports.

Project scaffolding. Top-level theorems have statements; proofs are `sorry`.
The point is to make the *shape* of Zhang → Maynard → Polymath8b → twin primes
explicit and machine-checkable, so individual leaves can be filled in over time.

See [README](../README.md) for context and the
[side-quest doc](../../../personal/claude/knowledge/core/projects/lean-journey/side-quests/bounded-gaps.md)
for the math background.
-/
import BoundedGaps.Basic
import BoundedGaps.Prerequisites
import BoundedGaps.Sieve
import BoundedGaps.SieveExpansion
import BoundedGaps.SingularSeries
import BoundedGaps.SharpMertens
import BoundedGaps.Maynard
import BoundedGaps.Zhang
import BoundedGaps.Polymath8b
import BoundedGaps.TwinPrimes
import BoundedGaps.Engelsma
import BoundedGaps.Targets
import BoundedGaps.SievePolynomial
import BoundedGaps.SimplexCutoff
import BoundedGaps.SymmetricReduction
import BoundedGaps.SymmetricReductionFiberAlt
import BoundedGaps.EpsScaling
import BoundedGaps.EpsBridge
import BoundedGaps.SymmetricReductionEps
import BoundedGaps.SymmetricReductionOrbitFree
import BoundedGaps.SymmetricReductionEpsOrbitFree
import BoundedGaps.MultinomialFast
import BoundedGaps.MkWitness200
import BoundedGaps.Mertens
import BoundedGaps.RiemannSumLogWeight
import BoundedGaps.WeightedMertens
import BoundedGaps.PolyaUniform
import BoundedGaps.WeightedRiemann2D
import BoundedGaps.InnerUniformReduction
import BoundedGaps.WeightedRiemann3D
import BoundedGaps.WeightedRiemannKD
import BoundedGaps.WeightedRiemannGen
import BoundedGaps.WeightedRiemannSigned
import BoundedGaps.S1Fubini
import BoundedGaps.S1ConnectionK1
import BoundedGaps.S1MainTermDecomp
import BoundedGaps.Antiderivative
