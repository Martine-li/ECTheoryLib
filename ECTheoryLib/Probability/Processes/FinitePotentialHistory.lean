import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Probability.Processes.FiniteStateBounds

/-!
# Finite potential range on countably infinite state trajectories

The finite range supplies integrability for the existing full-history law.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Finite potential range supplies the integrability required by Mathlib's
countable-state conditional trajectory law. The complete state need not be finite. -/
theorem PathMeasureFinitePotentialConditionalDrift (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (S : Finset ℝ) (Values : ∀ x, V x∈S) (t : ℕ) :
    (PathMeasure Step Initial)[fun Path => V (Path t)-V (Path (t+1)) |
      Filtration.piLE (X := fun _ : ℕ => State) t] =ᵐ[PathMeasure Step Initial]
      (fun Path => ∫ y, V (Path t)-V y ∂(Step (Path t)).toMeasure) := by
  have IntegrableV (j : ℕ) : Integrable (fun Path => V (Path j)) (PathMeasure Step Initial) :=
    FiniteStateIntegrable _ _ S (CountablePathPotentialAdapted V).measurable
      (ae_of_all _ (fun Path => Values (Path j)))
  exact PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun x y => V x-V y) ((IntegrableV t).sub (IntegrableV (t+1)))

end
end ECTheoryLib.Probability
