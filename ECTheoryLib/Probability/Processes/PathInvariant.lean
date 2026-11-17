import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.Processes.Invariant

/-! State invariants hold almost surely at every time on the actual path law. -/
namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section

variable {State : Type*} [MeasurableSpace State] [Countable State]
  [MeasurableSingletonClass State]

/-- An invariant of initialization and of every supported transition holds on paths.
The conclusion is almost sure, not a claim about arbitrary sequences. -/
theorem PathMeasurePreservesProperty (Step : Transition State) (Initial : PMF State)
    (Property : State → Prop)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Property x)
    (Preserved : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Property x → Property y)
    (t : Nat) :
    ∀ᵐ Path ∂PathMeasure Step Initial, Property (Path t) := by
  induction t with
  | zero =>
      have InitialMap : ∀ᵐ x ∂(PathMeasure Step Initial).map
          (fun Path : Nat → State => Path 0), Property x := by
        rw [PathMeasureInitial]
        exact Initially
      exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable InitialMap
  | succ t Previous =>
      have Follows := PathMeasureFollowsTransition Step Initial
        (fun x y => Property x → Property y) Preserved t
      filter_upwards [Previous, Follows] with Path Valid NextValid
      exact NextValid Valid

/-- Countably many per-time invariants may be required simultaneously. -/
theorem PathMeasurePreservesPropertyAllTimes (Step : Transition State) (Initial : PMF State)
    (Property : State → Prop)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Property x)
    (Preserved : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Property x → Property y) :
    ∀ᵐ Path ∂PathMeasure Step Initial, ∀ t, Property (Path t) := by
  exact ae_all_iff.mpr (PathMeasurePreservesProperty Step Initial Property Initially Preserved)

end
end ECTheoryLib.Probability
