import ECTheoryLib.Algorithms.RLS
import Mathlib.Probability.UniformOn
import Mathlib.Tactic

/-!
# Independent coordinate law of the original binary RLS initialization

Derive the product law of RLSInit from Mathlib uniformOn_pi, including n=0.
This module depends on the existing algorithm definition, not on its analyses.
-/



namespace ECTheoryLib
open MeasureTheory ProbabilityTheory
noncomputable section

private theorem uniformFintypeMeasure {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (PMF.uniformOfFintype A).toMeasure = uniformOn (Set.univ : Set A) := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, uniformOn_univ]
  simp only [Measure.count_singleton, one_div]

theorem RLSInitProduct (n : ℕ) :
    (RLSInit n).toMeasure =
      Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) := by
  rw [RLSInit, uniformFintypeMeasure]
  simp_rw [uniformFintypeMeasure]
  simpa only [Set.pi_univ] using (uniformOn_pi (ι := Fin n) (f := fun _ => (Set.univ : Set Bool)))

end
end ECTheoryLib

