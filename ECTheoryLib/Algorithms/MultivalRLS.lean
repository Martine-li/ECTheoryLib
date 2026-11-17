import ECTheoryLib.Operators.Mutation.OneCoordinate
import ECTheoryLib.Operators.Selection.Elitist
import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.HittingTimes.HittingTime

/-!
# Generic multi-valued RLS transitions

Each iteration samples a coordinate and a different replacement value uniformly,
then selects a survivor using the supplied candidate-to-parent relation. No
specific objective is imported. Initialization is time zero; steps count mutations.
-/

open MeasureTheory
open scoped ENNReal

namespace ECTheoryLib

/-- One deterministic iteration with a specified coordinate and replacement value. -/
def MultivalRLSUpdate {n r : Nat}
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) (i : Fin n) (v : Fin r) : MultiValues n r :=
  ElitistSelect NotWorse State (Function.update State i v)

/-- An acceptable replacement is retained. -/
theorem MultivalRLSUpdateAccept {n r : Nat}
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) (i : Fin n) (v : Fin r)
    (Acceptable : NotWorse (Function.update State i v) State) :
    MultivalRLSUpdate NotWorse State i v = Function.update State i v := by
  exact ElitistSelectAccept NotWorse State (Function.update State i v) Acceptable

/-- A rejected replacement leaves the current state unchanged. -/
theorem MultivalRLSUpdateReject {n r : Nat}
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) (i : Fin n) (v : Fin r)
    (Unacceptable : ¬ NotWorse (Function.update State i v) State) :
    MultivalRLSUpdate NotWorse State i v = State := by
  exact ElitistSelectReject NotWorse State (Function.update State i v) Unacceptable

noncomputable section

/-- Uniform legal one-coordinate replacement followed by elitist selection. -/
def MultivalRLSStep {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetAtLeastTwo : 2 ≤ r)
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) : PMF (MultiValues n r) :=
  (UniformCoordinateChoice PositiveLength AlphabetAtLeastTwo State).map
    (fun Choice => MultivalRLSUpdate NotWorse State Choice.1 Choice.2.val)

/-- The successor expectation equals the equally weighted sum over complete choices. -/
theorem MultivalRLSStepIntegral {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetAtLeastTwo : 2 ≤ r)
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) (f : MultiValues n r → ℝ) :
    (∫ Next, f Next ∂(MultivalRLSStep PositiveLength AlphabetAtLeastTwo
      NotWorse State).toMeasure) =
      (1 / ((n * (r - 1) : Nat) : ℝ)) *
        ∑ Choice : CoordinateChoice State,
          f (MultivalRLSUpdate NotWorse State Choice.1 Choice.2.val) := by
  unfold MultivalRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite _)
    (measurable_of_finite f).stronglyMeasurable]
  exact UniformCoordinateChoiceIntegral PositiveLength AlphabetAtLeastTwo State _

/-- A property true after every deterministic choice holds almost surely under
the actual successor PMF. This bridges local reasoning and trajectory invariants. -/
theorem MultivalRLSStepProperty {n r : Nat} (PositiveLength : 0 < n)
    (AlphabetAtLeastTwo : 2 ≤ r)
    (NotWorse : MultiValues n r → MultiValues n r → Prop) [DecidableRel NotWorse]
    (State : MultiValues n r) {Q : MultiValues n r → Prop}
    (AllChoices : ∀ Choice : CoordinateChoice State,
      Q (MultivalRLSUpdate NotWorse State Choice.1 Choice.2.val)) :
    ∀ᵐ Next ∂(MultivalRLSStep PositiveLength AlphabetAtLeastTwo NotWorse State).toMeasure,
      Q Next := by
  have SupportMeasurable : MeasurableSet
      (MultivalRLSStep PositiveLength AlphabetAtLeastTwo NotWorse State).support := by
    exact (Set.to_countable _).measurableSet
  have Supported : ∀ᵐ Next
      ∂(MultivalRLSStep PositiveLength AlphabetAtLeastTwo NotWorse State).toMeasure,
      Next ∈ (MultivalRLSStep PositiveLength AlphabetAtLeastTwo NotWorse State).support := by
    apply (mem_ae_iff_prob_eq_one SupportMeasurable).mpr
    exact (PMF.toMeasure_apply_eq_one_iff _ SupportMeasurable).mpr (Set.Subset.refl _)
  filter_upwards [Supported] with Next Possible
  unfold MultivalRLSStep at Possible
  obtain ⟨Choice, _ChoicePossible, NextEqualsUpdate⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp Possible
  rw [← NextEqualsUpdate]
  exact AllChoices Choice

end
end ECTheoryLib
