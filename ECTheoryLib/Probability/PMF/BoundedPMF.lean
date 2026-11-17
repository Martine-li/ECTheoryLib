import ECTheoryLib.Probability.PMF.FinitePMF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Bounded expectations for countable PMFs

These bridges use mathlib's measurable kernels and iterated integration for
countable state types. Uniform boundedness supplies integrability, including for
list-valued transitions whose full state type is infinite. No finite-support or
finite-runtime premise is required.
-/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Every bounded real function on a countable discrete PMF is integrable. -/
theorem PMFIntegrableOfBounded {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) (B : ℝ)
    (Bound : ∀ x, ‖f x‖ ≤ B) : Integrable f p.toMeasure :=
  (integrable_const B).mono' (measurable_of_countable f).aestronglyMeasurable (ae_of_all _ Bound)

/-- A deterministic map transfers a real integrand to the source PMF.
Countability and measurable singletons make both functions measurable. -/
theorem PMFIntegralMapCountable {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (Update : α → β) (f : β → ℝ) :
    (∫ y, f y ∂(p.map Update).toMeasure) = ∫ x, f (Update x) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map Update p (measurable_of_countable _)]
  exact integral_map_of_stronglyMeasurable (measurable_of_countable Update)
    (measurable_of_countable f).stronglyMeasurable

/-- Iterated expectation for countable PMF composition with a bounded real
integrand. The outer expectation remains an integral, not a finite sum. -/
theorem PMFIntegralBindOfBounded {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) (B : ℝ)
    (Bound : ∀ y, ‖f y‖ ≤ B) :
    (∫ y, f y ∂(p.bind q).toMeasure) = ∫ x, (∫ y, f y ∂(q x).toMeasure) ∂p.toMeasure := by
  let K : Kernel α β := ⟨fun x => (q x).toMeasure, measurable_of_countable _⟩
  have Markov : IsMarkovKernel K := ⟨fun x => by change IsProbabilityMeasure (q x).toMeasure; infer_instance⟩
  let := Markov
  have Law : K ∘ₘ p.toMeasure = (p.bind q).toMeasure := by
    ext S MeasurableS
    rw [Measure.bind_apply MeasurableS (Kernel.aemeasurable K),
      PMF.toMeasure_bind_apply _ _ _ MeasurableS, lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), mul_comm]
    rfl
  have IntegrableF : Integrable f (K ∘ₘ p.toMeasure) := by
    rw [Law]
    exact PMFIntegrableOfBounded _ f B Bound
  rw [← Law]
  rw [Measure.comp_eq_comp_const_apply] at IntegrableF ⊢
  exact Kernel.integral_comp IntegrableF

end
end ECTheoryLib.Probability
