# Drift theorems

Apply these theorems to an abstract random process with its range, stopping rule and conditional drift or moment hypotheses.

## Recommended entries

- [Additive.lean](Additive.lean): Additive mean upper and lower bounds.
- [Variable.lean](Variable.lean): Reciprocal-integral upper bounds.
- [Multiplicative.lean](Multiplicative.lean): Logarithmic mean bounds.
- [MultiplicativeTail.lean](MultiplicativeTail.lean): Multiplicative upper tails.
- [GeneralGeometricJumpNegative.lean](GeneralGeometricJumpNegative.lean): Interval-local negative drift.
- [Potential/Canonical.lean](Potential/Canonical.lean): Conditional expected remaining-time potential.

The [Chapter 2 map](../../../docs/COVERAGE.md#chapter-2-ten-main-theorems) identifies raw-level, full-history, surviving-level and revised interfaces. See [RLS–OneMax](../../Analysis/OneMax/RLS.lean) for a concrete client; the [runtime layer](../Runtime/README.md) can lift local transition inequalities for you.

The [complete file index](../../../docs/CONTENTS.md) lists every module once.
