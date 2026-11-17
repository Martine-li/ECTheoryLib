# Architecture

The library follows mathematical dependencies. Textbook order is provided by
[COVERAGE](COVERAGE.md); proofs are not duplicated into chapter directories.
Existing public names and import paths are retained.

| Layer | Responsibility | Recommended entry |
| --- | --- | --- |
| [SearchSpaces](../ECTheoryLib/SearchSpaces/README.md) | Bit strings, finite alphabets and population states | `BitString.lean` |
| [Problems](../ECTheoryLib/Problems/README.md) | Objective functions, targets and Pareto predicates | `OneMax.lean`, `Linear.lean` |
| [Operators](../ECTheoryLib/Operators/README.md) | Mutation, crossover and survivor selection | `Mutation/OneBit.lean`, `Mutation/IndependentBit.lean` |
| [Algorithms](../ECTheoryLib/Algorithms/README.md) | Transition kernels, initialization, runs and invariants | `RLS.lean`, `OnePlusOneEA.lean` |
| [Probability](../ECTheoryLib/Probability/README.md) | Laws, processes, conditional means, concentration and stochastic order | `Processes/Transition.lean`, `HittingTimes/Expectation.lean` |
| [Tools/Drift](../ECTheoryLib/Tools/Drift/README.md) | Drift theorems for abstract random processes | `Additive.lean`, `Variable.lean`, `Multiplicative.lean` |
| [Tools/Runtime](../ECTheoryLib/Tools/Runtime/README.md) | Lift local kernel inequalities to runtime claims | `LocalDrift.lean`, `FiniteRange.lean` |
| [Analysis](../ECTheoryLib/Analysis/README.md) | Concrete algorithm/problem analyses | OneMax/RLS, LeadingOnes/RLS, Linear/OnePlusOneEA |

The three analysis entry points serve different inputs:

1. **Tools/Drift:** supply a process, its range and the relevant drift/conditional
   hypotheses, then derive a hitting-time statement.
2. **Tools/Runtime:** supply an algorithm transition PMF, initial law, target,
   potential and local mean inequality. The bridge handles the corresponding
   trajectory law and hitting time.
3. **Analysis:** inspect completed applications, including how the algorithm
   model satisfies those hypotheses. A model or invariant alone is not a general
   runtime theorem for the named algorithm.

Small executable clients and mathematically useful counterexamples live in
[Examples](../Examples/README.md). The complete internal regression suite and
acceptance tooling remain in the development workspace; their evidence is
summarized separately in [VALIDATION](VALIDATION.md).

The [content guide](CONTENTS.md) contains the single full file index. Directory
READMEs select entry modules and cases rather than repeating that inventory.
