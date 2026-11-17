# Executable examples

Start with [Quickstart.lean](Quickstart.lean) for calls to the three representative
runtime results. [ProbabilityTools.lean](ProbabilityTools.lean) demonstrates direct
Mathlib reuse for the exponential inequality, union bound, expectation linearity
and Markov/first-moment bounds.

The remaining files preserve mathematical examples used by the documentation:

| File | Mathematical purpose |
| --- | --- |
| [Conditioning.lean](Conditioning.lean) | Separate raw-level, stopped and surviving-level drift conditions. |
| [TailConditions.lean](TailConditions.lean) | Separate geometric-tail constants, exponential-moment directions and strictness. |
| [ExpectationConditions.lean](ExpectationConditions.lean) | Real-center and signed-variable counterexamples for tail-to-mean displays. |
| [FiniteRangeDrift.lean](FiniteRangeDrift.lean) | Show the obstruction to global away-drift in a common finite range. |

`check.ps1` builds the library and Lean-checks all six files. They are selected
clients and mathematical examples, not the complete internal test suite.
The relations to the specified textbook edition are in
[SOURCE_NOTES](../docs/SOURCE_NOTES.md).
