# Algorithm and problem analyses

Concrete analyses connect a specified algorithm and initialization to local drift, probability estimates and runtime conclusions.

## Recommended entries

- [OneMax/RLS/ExactRuntime.lean](OneMax/RLS/ExactRuntime.lean): Exact fixed-state nH_k for weak-elitist RLS, n>0.
- [LeadingOnes/RLS/ExactRuntime.lean](LeadingOnes/RLS/ExactRuntime.lean): Exact n²/2 under uniform initialization, n>0.
- [Linear/RLS/PositiveWeights.lean](Linear/RLS/PositiveWeights.lean): Exact nH_k for positive-weight weak-minimizing RLS, k initial one bits and n>0; this includes BinVal.
- [Linear/OnePlusOneEA/RuntimeUpperBounds.lean](Linear/OnePlusOneEA/RuntimeUpperBounds.lean): Positive-weight standard minimizing EA: arbitrary-initial-law 4en(1+log(2n)) bound.
- [OneMax/RLSWithShortcuts/RuntimeLowerBounds.lean](OneMax/RLSWithShortcuts/RuntimeLowerBounds.lean): Uniform Θ(n) runtime and logarithmic overestimate ratio.
- [CouponCollector/ExactRuntime.lean](CouponCollector/ExactRuntime.lean): Actual coupon collection exact mean and asymptotics.
- [RandomWalk/WeakDriftTail.lean](RandomWalk/WeakDriftTail.lean): A finite weak-drift walk’s cubic high-probability bound.

These results count updates/draws in their specified models. [Cost conversion](../Tools/Runtime/Cost.lean) supplies evaluation units. Additional archive and population cases are indexed below; their model, initialization and capacity conditions are part of each result. A file under Algorithms alone does not establish a general runtime theory.

The [complete file index](../../docs/CONTENTS.md) lists every module once.
