import ECTheoryLib.Analysis.MultivalOneMax.RLS.UniformInitialLaw
import ECTheoryLib.Probability.Distributions.BinomialVariance

/-!
# Concentration of actual uniform initial Hamming distance

The complete initialization law supplies all moment assumptions. The target is
arbitrary; a one-symbol alphabet and an empty string are valid zero-variance cases.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- Exact variance n(1-1/r)/r, including the one-symbol alphabet. -/
theorem UniformHammingVariance {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) :
    variance (fun x => (Hamming Target x : ℝ)) (MultivalRLSInit n r PositiveAlphabet).toMeasure =
      (n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) := by
  have Law : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  rw [BinomialNatVarianceOfLaw _ _ n _ Law]
  change (n : ℝ) * (1 - 1 / (r : ℝ)) * (1 - (1 - 1 / (r : ℝ))) = _
  ring

/-- A two-sided deviation bound around the actual initial mean. -/
theorem UniformHammingDeviationProbability {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveThreshold : 0 < c) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure
      {x | c ≤ |(Hamming Target x : ℝ) - (n : ℝ) * (1 - 1 / (r : ℝ))|} ≤
      ENNReal.ofReal ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) / c ^ 2) := by
  have Law : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  have Bound := BinomialNatDeviationProbabilityOfLaw _ _ n _ Law c PositiveThreshold
  change _ ≤ ENNReal.ofReal ((n : ℝ) * (1 - 1 / (r : ℝ)) *
    (1 - (1 - 1 / (r : ℝ))) / c ^ 2) at Bound
  rw [show (1 : ℝ) - (1 - 1 / (r : ℝ)) = 1 / (r : ℝ) by ring] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSMultival

