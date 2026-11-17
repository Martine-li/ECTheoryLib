import ECTheoryLib.Probability.Processes.PastEventTransition
import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite unions of next-state events on one trajectory

A uniform transition bound controls events at coordinates 1 through T under
the same PathMeasure. The proof reuses the existing past-event transition
bridge and Mathlib finite union bound. No independence between the events is
assumed; T=0 gives the empty union. A client must prove the local premise from
its actual transition and retain any raw proposals used by its event.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A uniform local next-state event bound controls the first T transitions of
the same path law. No independence between the T events is assumed. -/
theorem PathNextEventUnionBound {State : Type*} [MeasurableSpace State]
    [Countable State] [MeasurableSingletonClass State]
    (Step : Transition State) (Initial : PMF State)
    (C : Set State) (T : ℕ) (r : ℝ) (Nonnegative : 0 ≤ r)
    (LocalBound : ∀ s, (Step s).toMeasure.real C ≤ r) :
    (PathMeasure Step Initial).real
      (⋃ t ∈ Finset.range T, {path | path (t + 1) ∈ C}) ≤ (T : ℝ) * r := by
  have Each (t : ℕ) :
      (PathMeasure Step Initial).real {path | path (t + 1) ∈ C} ≤ r := by
    have Bound := PathPastEventTransitionBound Step Initial t Set.univ
      MeasurableSet.univ C r Nonnegative
      (Filter.Eventually.of_forall (fun path _ => LocalBound (path t)))
    simpa [Measure.real] using Bound
  calc
    _ ≤ ∑ t ∈ Finset.range T,
        (PathMeasure Step Initial).real {path | path (t + 1) ∈ C} :=
      measureReal_biUnion_finset_le (Finset.range T) _
    _ ≤ ∑ _t ∈ Finset.range T, r :=
      Finset.sum_le_sum (fun t _ => Each t)
    _ = (T : ℝ) * r := by simp

end
end ECTheoryLib.Probability
