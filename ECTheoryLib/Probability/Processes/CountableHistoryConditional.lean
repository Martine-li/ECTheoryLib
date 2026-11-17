import ECTheoryLib.Probability.Processes.Process
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Full-history conditional expectations on countable-state trajectories

Directly reuse Mathlib conditional trajectory distributions. Observations
may depend on the whole finite history and need only actual integrability.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The complete-history conditional expectation for a countable-state
trajectory, directly reusing Mathlib's conditional trajectory law. The
observation is integrable but may be unbounded and history-dependent. -/
theorem PathMeasureHistoryConditionalExpectationOfIntegrable (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : (Finset.Iic t → State) → State → ℝ)
    (IntegrableObservation : Integrable (fun Path => f (Preorder.frestrictLe t Path) (Path (t+1)))
      (PathMeasure Step Initial)) :
    (PathMeasure Step Initial)[fun Path => f (Preorder.frestrictLe t Path) (Path (t+1)) |
      Filtration.piLE (X := fun _ : ℕ => State) t] =ᵐ[PathMeasure Step Initial]
      (fun Path => ∫ y, f (Preorder.frestrictLe t Path) y ∂(Step (Path t)).toMeasure) := by
  obtain ⟨s,_Supported⟩ := Initial.support_nonempty
  let : Nonempty State := ⟨s⟩
  have Conditional := condExp_prod_ae_eq_integral_condDistrib
    (μ := PathMeasure Step Initial) (Preorder.measurable_frestrictLe t)
    (measurable_pi_apply (t+1)).aemeasurable
    (measurable_of_countable (fun p : (Finset.Iic t → State)×State => f p.1 p.2)).stronglyMeasurable
    IntegrableObservation
  have KernelLaw := Kernel.condDistrib_trajMeasure (X := fun _ : ℕ => State)
    (κ := HistoryKernel Step) (μ₀ := Initial.toMeasure) (a := t)
  have KernelAt := ae_of_ae_map (Preorder.measurable_frestrictLe t).aemeasurable KernelLaw
  rw [Filtration.piLE_eq_comap_frestrictLe]
  filter_upwards [Conditional,KernelAt] with Path Equal Law
  change (condDistrib (fun Path : ℕ → State => Path (t+1)) (Preorder.frestrictLe t)
    (PathMeasure Step Initial)) (Preorder.frestrictLe t Path)=(Step (Path t)).toMeasure at Law
  rw [Equal,Law]

theorem PathMeasureStateConditionalExpectationOfIntegrable (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : State → State → ℝ)
    (IntegrableObservation : Integrable (fun Path => f (Path t) (Path (t+1))) (PathMeasure Step Initial)) :
    (PathMeasure Step Initial)[fun Path => f (Path t) (Path (t+1)) |
      Filtration.piLE (X := fun _ : ℕ => State) t] =ᵐ[PathMeasure Step Initial]
      (fun Path => ∫ y, f (Path t) y ∂(Step (Path t)).toMeasure) :=
  PathMeasureHistoryConditionalExpectationOfIntegrable Step Initial t
    (fun h y => f (HistoryLast t h) y) IntegrableObservation

/-- Countable-state potentials are adapted; boundedness is not needed. -/
theorem CountablePathPotentialAdapted (V : State → ℝ) :
    Adapted (Filtration.piLE (X := fun _ : ℕ => State)) (fun t Path => V (Path t)) := by
  intro t
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable (fun h : Finset.Iic t → State => V (HistoryLast t h))).comp
    (measurable_iff_comap_le.mpr le_rfl)

end
end ECTheoryLib.Probability
