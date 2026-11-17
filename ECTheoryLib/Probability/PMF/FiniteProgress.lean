import ECTheoryLib.Probability.PMF.FinitePMF

/-!
# Lower bounds from a specified finite-PMF outcome

A nonnegative progress function permits retaining just one event. This interface
keeps its exact probability visible and is useful for waiting-time and population
arguments; independence is encoded by the supplied PMF composition, never assumed
from a scalar potential.
-/
namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section

/-- A nonnegative expectation is at least the contribution of any specified
outcome, including an outcome of probability zero. -/
theorem PMFIntegralLowerOfPoint {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ)
    (Nonnegative : ∀ y, 0 ≤ f y) (x : α) :
    (p x).toReal * f x ≤ ∫ y, f y ∂p.toMeasure := by
  have Bound := PMFIntegralLowerOfInjection (ι := Unit) p f (fun _ => x)
    (fun _ _ _ => Subsingleton.elim _ _) Nonnegative (p x).toReal (fun _ => le_rfl)
  simpa only [Fintype.sum_unique] using Bound

end
end ECTheoryLib.Probability
