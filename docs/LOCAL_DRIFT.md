# From one-step drift to runtime

Use [Tools/Runtime/LocalDrift.lean](../ECTheoryLib/Tools/Runtime/LocalDrift.lean)
when the local analysis is expressed directly under an algorithm’s transition
PMF. The finite-state additive interface is
`ECTheoryLib.Tools.Runtime.AdditiveRuntimeUpperBound`.

1. Specify the actual `Step : Transition State`, `Initial : PMF State` and target
   predicate. `Step x` includes both accepted offspring and rejection mass.
2. Choose a real potential `V`, prove it is nonnegative and that `V x = 0`
   exactly describes success. Use `Valid` for any necessary invariant.
3. Show validity initially and after one transition. For this absorbing
   interface, also show a zero potential remains zero on valid transitions.
4. Prove the one-step integral is at least a positive `Delta` at every valid
   non-target state. The resulting mean bound is the initial expected potential
   divided by `Delta`.

The following is a runnable generic client of that interface:

```lean
import ECTheoryLib.Tools.Runtime.LocalDrift

open MeasureTheory ECTheoryLib.Probability

example {State : Type*} [Fintype State] [MeasurableSpace State]
    [MeasurableSingletonClass State]
    (Step : Transition State) (Initial : PMF State)
    (V : State → Real) (Goal Valid : State → Prop)
    (Nonnegative : ∀ x, 0 ≤ V x)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure,
      Valid x → V x = 0 → V y = 0)
    (Delta : Real) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta ≤ ∫ y, V x - V y ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤
      ENNReal.ofReal ((∫ x, V x ∂Initial.toMeasure) / Delta) := by
  exact ECTheoryLib.Tools.Runtime.AdditiveRuntimeUpperBound
    Step Initial V Goal Valid Nonnegative ZeroIffGoal Initially
    PreservesValid PreservesZero Delta PositiveDelta LocalDrift
```

For a complete concrete application, follow the potential and one-step
calculation in [RLS–OneMax](../ECTheoryLib/Analysis/OneMax/RLS/Drift.lean), then
its [runtime bounds](../ECTheoryLib/Analysis/OneMax/RLS/RuntimeBounds.lean).
The harmonic-potential calculation yields the stronger exact result used in
[Quickstart](../Examples/Quickstart.lean).

The multiplicative interface in the same module uses a natural-valued potential
with minimum positive value 1 and a zero-safe logarithmic transform. For a real
potential with a specified finite range, use
[FiniteRange](../ECTheoryLib/Tools/Runtime/FiniteRange.lean). For a process that can
leave the target after its first hit, choose the appropriate
[nonabsorbing bridge](../ECTheoryLib/Tools/Runtime/NonabsorbingFiniteRange.lean)
and check its conditioning hypotheses; the absorbing interface above cannot be
used just by discarding its zero-preservation premise.

These conclusions count updates. Use
[`ExpectedEvaluationCostEq`](../ECTheoryLib/Tools/Runtime/Cost.lean)
to charge a fixed initial cost and a fixed cost per completed update on the same
path law. Within-generation early stopping is a different cost model.
