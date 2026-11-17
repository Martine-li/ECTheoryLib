import ECTheoryLib.SearchSpaces.BitString
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ECTheoryLib

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Fair choice of the source parent, including when their coordinate values agree. -/
def UniformCrossoverHalf : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Each offspring coordinate independently chooses either parent with equal probability.
The upstream probability-measure construction supplies normalization, including n = 0. -/
def UniformCrossover {n : Nat} (Parent Other : Bits n) : PMF (Bits n) :=
  (Measure.pi (fun i : Fin n =>
    bernoulliMeasure (Parent i) (Other i) UniformCrossoverHalf)).toPMF

/-- The actual PMF has the full independent product law, not just fair marginals. -/
theorem UniformCrossoverProductLaw {n : Nat} (Parent Other : Bits n) :
    (UniformCrossover Parent Other).toMeasure =
      Measure.pi (fun i : Fin n =>
        bernoulliMeasure (Parent i) (Other i) UniformCrossoverHalf) :=
  Measure.toPMF_toMeasure _

/-- A point probability factors into its coordinate masses, with equal-parent atoms combined. -/
theorem UniformCrossoverProbability {n : Nat} (Parent Other Candidate : Bits n) :
    UniformCrossover Parent Other Candidate =
      ∏ i : Fin n, bernoulliMeasure (Parent i) (Other i) UniformCrossoverHalf {Candidate i} := by
  change (Measure.pi (fun i : Fin n =>
    bernoulliMeasure (Parent i) (Other i) UniformCrossoverHalf)) {Candidate} = _
  exact Measure.pi_singleton _ _

/-- The coordinate law remains valid for coinciding parental bits. -/
theorem UniformCrossoverCoordinateLaw {n : Nat} (Parent Other : Bits n) (i : Fin n) :
    (UniformCrossover Parent Other).toMeasure.map (fun Candidate => Candidate i) =
      bernoulliMeasure (Parent i) (Other i) UniformCrossoverHalf := by
  rw [UniformCrossoverProductLaw]
  exact (measurePreserving_eval _ i).map_eq

/-- Coordinate independence is a property of the actual offspring law. -/
theorem UniformCrossoverIndependent {n : Nat} (Parent Other : Bits n) :
    iIndepFun (fun i : Fin n => fun Candidate : Bits n => Candidate i)
      (UniformCrossover Parent Other).toMeasure := by
  rw [UniformCrossoverProductLaw]
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Every real coordinate statistic has the arithmetic mean of its parental values. -/
theorem UniformCrossoverCoordinateIntegral {n : Nat} (Parent Other : Bits n)
    (i : Fin n) (f : Bool → ℝ) :
    (∫ Candidate, f (Candidate i) ∂(UniformCrossover Parent Other).toMeasure) =
      (f (Parent i) + f (Other i)) / 2 := by
  have MapIntegral := integral_map_of_stronglyMeasurable (measurable_pi_apply i)
    (measurable_of_finite f).stronglyMeasurable
    (μ := (UniformCrossover Parent Other).toMeasure)
  rw [UniformCrossoverCoordinateLaw] at MapIntegral
  rw [← MapIntegral, integral_bernoulliMeasure]
  simp only [UniformCrossoverHalf, smul_eq_mul]
  ring

end
end ECTheoryLib

