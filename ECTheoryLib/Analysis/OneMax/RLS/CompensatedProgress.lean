import ECTheoryLib.Probability.Moments.ConditionalSubGaussian
import ECTheoryLib.Analysis.OneMax.RLS.Drift
import ECTheoryLib.Probability.Processes.HistoryConditional
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith

/-!
# Conditional MGF of compensated RLS progress

The original standard OneMax RLS trajectory has selected zero-count decrease
minus its current zero count divided by n. Its conditional mean is zero
given the complete past and its absolute value is at most one. These facts
supply a conditional sub-Gaussian MGF without independent increments.
-/
namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Compensated selected progress has conditional mean zero given the complete past. -/
theorem PathCompensatedProgressConditionalMean {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    (PathMeasure (Step PositiveLength) Initial)[
      fun Path => Potential (Path t) - Potential (Path (t + 1)) - Potential (Path t) / (n : ℝ) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) t] =ᵐ[PathMeasure (Step PositiveLength) Initial]
        (fun _ => 0) := by
  have StateCentered (x : Bits n) :
      (∫ y, Potential x - Potential y - Potential x / (n : ℝ)
        ∂(Step PositiveLength x).toMeasure) = 0 := by
    rw [integral_sub Integrable.of_finite (integrable_const _),
      OneStepDrift PositiveLength x, integral_const, probReal_univ, one_smul, sub_self]
  have Conditional := PathMeasureStateConditionalExpectation (Step PositiveLength) Initial t
    (fun x y => Potential x - Potential y - Potential x / (n : ℝ))
  simpa only [StateCentered] using Conditional

/-- The original RLS transition, not arbitrary state sequences, bounds the compensated progress. -/
theorem PathCompensatedProgressBounded {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) Initial,
      |Potential (Path t) - Potential (Path (t + 1)) - Potential (Path t) / (n : ℝ)| ≤ 1 := by
  have Binary := PathMeasureFollowsTransition (Step PositiveLength) Initial
    (fun x y => Potential x - Potential y = 0 ∨ Potential x - Potential y = 1)
    (StepPotentialDecreaseBinary PositiveLength) t
  filter_upwards [Binary] with Path Decrease
  have PositiveN : 0 < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have MeanNonnegative : 0 ≤ Potential (Path t) / (n : ℝ) :=
    div_nonneg (PotentialNonnegative _) PositiveN.le
  have MeanLeOne : Potential (Path t) / (n : ℝ) ≤ 1 :=
    (div_le_one PositiveN).mpr (PotentialLeLength _)
  apply abs_le.mpr
  rcases Decrease with Zero | One
  · rw [Zero]
    constructor <;> linarith
  · rw [One]
    constructor <;> linarith

/-- A direct call to the generic bridge on the actual full-history RLS trajectory law. -/
theorem PathCompensatedProgressSubGaussian {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    HasCondSubgaussianMGF (Filtration.piLE (X := fun _ : ℕ => Bits n) t)
      (Filtration.piLE.le t)
      (fun Path => Potential (Path t) - Potential (Path (t + 1)) - Potential (Path t) / (n : ℝ))
      1 (PathMeasure (Step PositiveLength) Initial) := by
  have Coordinate (j : ℕ) : Measurable (fun Path : ℕ → Bits n => Potential (Path j)) :=
    (measurable_of_finite Potential).comp (measurable_pi_apply j)
  have Observable : Measurable (fun Path : ℕ → Bits n =>
      Potential (Path t) - Potential (Path (t + 1)) - Potential (Path t) / (n : ℝ)) :=
    ((Coordinate t).sub (Coordinate (t + 1))).sub ((Coordinate t).div_const (n : ℝ))
  simpa only [one_pow, NNReal.coe_one] using
    (ConditionalSubGaussianOfBoundedCentered (PathMeasure (Step PositiveLength) Initial)
      (Filtration.piLE (X := fun _ : ℕ => Bits n) t) (Filtration.piLE.le t) _ 1
      Observable.aemeasurable (PathCompensatedProgressBounded PositiveLength Initial t)
      (PathCompensatedProgressConditionalMean PositiveLength Initial t))

end
end ECTheoryLib.Analysis.RLSOnOneMax

