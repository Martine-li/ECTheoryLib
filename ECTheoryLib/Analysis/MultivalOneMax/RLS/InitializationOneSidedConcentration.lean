import ECTheoryLib.Probability.Concentration.Cantelli
import ECTheoryLib.Analysis.MultivalOneMax.RLS.InitializationConcentration

/-!
# One-sided deviations of actual initial Hamming distance

The actual initialization supplies the second moment and exact mean/variance.
Both sides use Cantelli, with its sharper denominator variance + offset^2.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- Upper deviations from the actual initialization mean. -/
theorem UniformHammingUpperDeviationProbability {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveThreshold : 0 < c) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real
      {x | (n : ℝ) * (1 - 1 / (r : ℝ)) + c ≤ (Hamming Target x : ℝ)} ≤
      ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ))) /
        ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) + c ^ 2) := by
  have Law : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  have Bound := CantelliUpperTail _ (fun x => (Hamming Target x : ℝ))
    (BinomialNatMemLpOfLaw _ _ n _ 2 Law) c PositiveThreshold
  rw [UniformHammingExpectation, UniformHammingVariance] at Bound
  exact Bound

/-- Lower deviations from the actual initialization mean. -/
theorem UniformHammingLowerDeviationProbability {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveThreshold : 0 < c) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real
      {x | (Hamming Target x : ℝ) ≤ (n : ℝ) * (1 - 1 / (r : ℝ)) - c} ≤
      ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ))) /
        ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) + c ^ 2) := by
  have Law : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  have Bound := CantelliLowerTail _ (fun x => (Hamming Target x : ℝ))
    (BinomialNatMemLpOfLaw _ _ n _ 2 Law) c PositiveThreshold
  rw [UniformHammingExpectation, UniformHammingVariance] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSMultival

