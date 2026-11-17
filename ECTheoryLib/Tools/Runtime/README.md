# From kernels to runtime

Derive hitting-time bounds from an algorithm’s actual transition kernel, initial law, potential and local inequalities.

## Recommended entries

- [LocalDrift.lean](LocalDrift.lean): Finite-state additive and natural-valued multiplicative interfaces.
- [FiniteRange.lean](FiniteRange.lean): Real potentials with a specified finite range.
- [NonabsorbingFiniteRange.lean](NonabsorbingFiniteRange.lean): Bridges that do not freeze the original process after success.
- [FitnessLevelsFromHistory.lean](FitnessLevelsFromHistory.lean): History-conditional fitness-level domination.
- [Cost.lean](Cost.lean): Fixed initialization and per-update evaluation costs.

Follow the [local-drift guide](../../../docs/LOCAL_DRIFT.md), then [RLS–OneMax](../../Analysis/OneMax/RLS/RuntimeBounds.lean) or the [positive-linear EA](../../Analysis/Linear/OnePlusOneEA/RuntimeUpperBounds.lean).

The [complete file index](../../../docs/CONTENTS.md) lists every module once.
