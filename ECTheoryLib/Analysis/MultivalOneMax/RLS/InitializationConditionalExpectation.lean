import ECTheoryLib.Analysis.MultivalOneMax.RLS.InitializationConditioning
import ECTheoryLib.Probability.Distributions.ConditionalBinomialExpectation

/-!
# Expected initial distance under lower-distance conditioning

The actual uniform initialization supplies its binomial law and positivity of
the conditioning event. This concerns time-zero distance, not conditional runtime.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- A finite conditional Hamming mean, with positivity proved by the library. -/
theorem UniformHammingConditionalIntegrable {n r : ℕ} (PositiveAlphabet : 0 < r)
    (NontrivialAlphabet : 2 ≤ r) (Target : MultiValues n r) (k : ℕ) (Threshold : k ≤ n) :
    Integrable (fun y => (Hamming Target y : ℝ))
      (cond (MultivalRLSInit n r PositiveAlphabet).toMeasure {y | k ≤ Hamming Target y}) := by
  have InitialLaw : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  exact ConditionalBinomialIntegrableOfLaw _ _ n k _ (measurable_of_finite _) InitialLaw
    (UniformHammingConditionEventPositive PositiveAlphabet NontrivialAlphabet Target k Threshold)

/-- Explicit initial-distance mean bound for any target and nontrivial alphabet. -/
theorem UniformHammingConditionalExpectation {n r : ℕ} (PositiveAlphabet : 0 < r)
    (NontrivialAlphabet : 2 ≤ r) (Target : MultiValues n r) (k : ℕ) (Threshold : k ≤ n) :
    (∫ y, (Hamming Target y : ℝ) ∂cond (MultivalRLSInit n r PositiveAlphabet).toMeasure
      {y | k ≤ Hamming Target y}) ≤
      (k : ℝ) + ((n - k : ℕ) : ℝ) * (1 - 1 / (r : ℝ)) := by
  have InitialLaw : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  exact ConditionalBinomialExpectationOfLaw _ _ n k _ (measurable_of_finite _) InitialLaw
    Threshold (UniformHammingConditionEventPositive PositiveAlphabet NontrivialAlphabet Target k Threshold)

end
end ECTheoryLib.Analysis.RLSMultival

