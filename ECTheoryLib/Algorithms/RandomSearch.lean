import ECTheoryLib.Probability.Processes.Transition

/-!
# Independent random search

Each transition replaces the current candidate by a fresh sample from
a specified law. The target is not frozen and there is no acceptance filter.
-/

namespace ECTheoryLib
open Probability
noncomputable section

/-- Replace the current candidate by a fresh sample from the specified law.
The actual trajectory kernel supplies a fresh conditional draw each time.
No acceptance rule or stopping rule is built into the algorithm. -/
def IndependentRandomSearchStep {State : Type*} (Samples : PMF State) : Transition State :=
  fun _ => Samples

theorem IndependentRandomSearchStepProbability {State : Type*} (Samples : PMF State) (x y : State) :
    IndependentRandomSearchStep Samples x y=Samples y := rfl

end
end ECTheoryLib
