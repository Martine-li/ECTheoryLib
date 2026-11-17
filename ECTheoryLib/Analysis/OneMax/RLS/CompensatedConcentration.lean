import ECTheoryLib.Probability.Concentration.AzumaMaximal
import ECTheoryLib.Probability.Concentration.AzumaHoeffding
import ECTheoryLib.Analysis.OneMax.RLS.CompensatedProgress
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Concentration of actual RLS compensated progress

The sum of selected progress minus the true predictable mean is evaluated on the original path law.
This is not a hitting-time or fitness-evaluation runtime statement.
-/
namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Finite-horizon upper concentration of selected progress minus its compensator. -/
theorem PathCompensatedProgressUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (horizon : ℕ) (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    (PathMeasure (Step PositiveLength) Initial).real
      {Path | threshold ≤ Potential (Path 0) - Potential (Path horizon) -
        ∑ i ∈ Finset.range horizon, Potential (Path i) / (n : ℝ)} ≤
      Real.exp (-threshold ^ 2 / (2 * (horizon : ℝ))) := by
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  have Coordinate (i : ℕ) : StronglyMeasurable[F i]
      (fun Path : ℕ → Bits n => Potential (Path i)) :=
    (PathPotentialAdapted Potential i).stronglyMeasurable
  have Observable (i : ℕ) : StronglyMeasurable[F (i + 1)]
      (fun Path : ℕ → Bits n => Potential (Path i) - Potential (Path (i + 1)) -
        Potential (Path i) / (n : ℝ)) :=
    (((Coordinate i).mono (F.mono (Nat.le_succ i))).sub (Coordinate (i + 1))).sub
      (((Coordinate i).mono (F.mono (Nat.le_succ i))).div stronglyMeasurable_const)
  have Bound := BoundedConditionalSumUpperTail
    (PathMeasure (Step PositiveLength) Initial) F
    (fun i Path => Potential (Path i) - Potential (Path (i + 1)) - Potential (Path i) / (n : ℝ))
    (fun _ => 1) horizon (fun i _ => Observable i)
    (fun i _ => PathCompensatedProgressBounded PositiveLength Initial i)
    (fun i _ => PathCompensatedProgressConditionalMean PositiveLength Initial i)
    threshold Nonnegative
  have Telescope (Path : ℕ → Bits n) :
      (∑ i ∈ Finset.range horizon,
        (Potential (Path i) - Potential (Path (i + 1)) - Potential (Path i) / (n : ℝ))) =
      Potential (Path 0) - Potential (Path horizon) -
        ∑ i ∈ Finset.range horizon, Potential (Path i) / (n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub']
  simpa only [Telescope, NNReal.coe_one, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax



/-! Finite maximal concentration for the original RLS path law. -/
namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Upper concentration of the compensated actual RLS progress at any positive prefix. -/
theorem PathCompensatedProgressMaximalUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (horizon : ℕ) (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    (PathMeasure (Step PositiveLength) Initial).real
      {Path | ∃ k : ℕ, 1 ≤ k ∧ k ≤ horizon ∧ threshold ≤
        Potential (Path 0) - Potential (Path k) -
          ∑ i ∈ Finset.range k, Potential (Path i) / (n : ℝ)} ≤
      Real.exp (-threshold ^ 2 / (2 * (horizon : ℝ))) := by
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  have Coordinate (i : ℕ) : StronglyMeasurable[F i]
      (fun Path : ℕ → Bits n => Potential (Path i)) :=
    (PathPotentialAdapted Potential i).stronglyMeasurable
  have Observable (i : ℕ) : StronglyMeasurable[F (i + 1)]
      (fun Path : ℕ → Bits n => Potential (Path i) - Potential (Path (i + 1)) -
        Potential (Path i) / (n : ℝ)) :=
    (((Coordinate i).mono (F.mono (Nat.le_succ i))).sub (Coordinate (i + 1))).sub
      (((Coordinate i).mono (F.mono (Nat.le_succ i))).div stronglyMeasurable_const)
  have Bound := BoundedConditionalSumMaximalUpperTail
    (PathMeasure (Step PositiveLength) Initial) F
    (fun i Path => Potential (Path i) - Potential (Path (i + 1)) - Potential (Path i) / (n : ℝ))
    (fun _ => 1) horizon (fun i _ => Observable i)
    (fun i _ => PathCompensatedProgressBounded PositiveLength Initial i)
    (fun i _ => PathCompensatedProgressConditionalMean PositiveLength Initial i)
    threshold Nonnegative
  have Telescope (k : ℕ) (Path : ℕ → Bits n) :
      (∑ i ∈ Finset.range k,
        (Potential (Path i) - Potential (Path (i + 1)) - Potential (Path i) / (n : ℝ))) =
      Potential (Path 0) - Potential (Path k) -
        ∑ i ∈ Finset.range k, Potential (Path i) / (n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub']
  simpa only [Telescope, NNReal.coe_one, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
