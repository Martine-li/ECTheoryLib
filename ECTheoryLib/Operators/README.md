# Variation and selection

Probability laws for proposals and survivor selection. An operator bound is distinct from the selected algorithm’s trajectory or runtime.

## Recommended entries

- [Mutation/OneBit.lean](Mutation/OneBit.lean): One uniformly chosen bit flip.
- [Mutation/IndependentBit.lean](Mutation/IndependentBit.lean): Independent mutation and the standard rate 1/n.
- [Selection/Elitist.lean](Selection/Elitist.lean): Explicit candidate-to-parent acceptance.
- [Crossover/Uniform.lean](Crossover/Uniform.lean): Uniform crossover law.
- [Crossover/SinglePoint.lean](Crossover/SinglePoint.lean): Symmetric single-point crossover law.

[Bit-mutation analyses](../Analysis/BitMutation/) and [crossover expectations](../Analysis/Crossover/) connect the actual proposal laws to probability estimates.

The [complete file index](../../docs/CONTENTS.md) lists every module once.
