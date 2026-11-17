# Probability toolkit

Reusable probability interfaces and Mathlib bridges for drift and runtime analysis. Many Chapter 1 results can be used without choosing an evolutionary algorithm.

## Recommended entries

- [Processes/Transition.lean](Processes/Transition.lean): Transition kernels and generated paths.
- [HittingTimes/Expectation.lean](HittingTimes/Expectation.lean): Expected hitting times, including nontermination.
- [StochasticOrder/StochasticDomination.lean](StochasticOrder/StochasticDomination.lean): Stochastic order, tails and law interfaces.
- [Concentration/BoundedDifferences.lean](Concentration/BoundedDifferences.lean): Independent coordinates and future conditional means.
- [Distributions/GeometricWaiting.lean](Distributions/GeometricWaiting.lean): Waiting times starting at one.

Use [the Chapter 1 map](../../docs/COVERAGE.md#chapter-1-available-probability-tools) to choose a textbook tool. [ProbabilityTools](../../Examples/ProbabilityTools.lean) shows direct upstream reuse; [LeadingOnes initialization](../Analysis/LeadingOnes/RLS/UniformInitialization.lean) is a concrete application.

The [complete file index](../../docs/CONTENTS.md) lists every module once.
