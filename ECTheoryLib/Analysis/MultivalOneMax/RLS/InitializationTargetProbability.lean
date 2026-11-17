import ECTheoryLib.Probability.Concentration.SecondMoment
import ECTheoryLib.Analysis.MultivalOneMax.RLS.InitializationConcentration

/-!
# A second-moment bound for hitting a target at initialization

Zero Hamming distance is equivalent to equality with the target. The true
uniform initialization law supplies its finite moments and positive mean.
This polynomial estimate is a reuse example, not a claim to improve the exact
exponentially small uniform singleton probability.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- Initial target probability is at most 1/(1+n(r-1)) for n>0 and r>=2. -/
theorem UniformInitialTargetProbabilitySecondMoment {n r : ℕ} (PositiveLength : 0 < n)
    (PositiveAlphabet : 0 < r) (NontrivialAlphabet : 2 ≤ r) (Target : MultiValues n r) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real {Target} ≤
      1 / (1 + (n : ℝ) * ((r : ℝ) - 1)) := by
  have PositiveN : (0 : ℝ) < n := by exact_mod_cast PositiveLength
  have PositiveR : (0 : ℝ) < r := by exact_mod_cast PositiveAlphabet
  have GreaterR : (1 : ℝ) < r := by exact_mod_cast NontrivialAlphabet
  have PositiveMismatch : 0 < 1 - 1 / (r : ℝ) :=
    sub_pos.mpr ((div_lt_one PositiveR).mpr GreaterR)
  have PositiveMean : 0 < (n : ℝ) * (1 - 1 / (r : ℝ)) := mul_pos PositiveN PositiveMismatch
  have Law : HasLaw (Hamming Target) (binomial n (MismatchProbability r PositiveAlphabet))
      (MultivalRLSInit n r PositiveAlphabet).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable, UniformHammingBinomial PositiveAlphabet Target⟩
  have SquareIntegrable := BinomialNatMemLpOfLaw _ _ n _ 2 Law
  have MeanNeZero : (∫ y, (Hamming Target y : ℝ) ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) ≠ 0 := by
    rw [UniformHammingExpectation]
    exact PositiveMean.ne'
  have Bound := ZeroProbabilitySecondMoment _ _ SquareIntegrable MeanNeZero
  have SecondMoment : (∫ y, (Hamming Target y : ℝ) ^ 2 ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) =
      (n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) +
        ((n : ℝ) * (1 - 1 / (r : ℝ))) ^ 2 := by
    have Identity := variance_eq_sub SquareIntegrable
    change variance (fun y => (Hamming Target y : ℝ)) (MultivalRLSInit n r PositiveAlphabet).toMeasure =
      (∫ y, (Hamming Target y : ℝ) ^ 2 ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) -
        (∫ y, (Hamming Target y : ℝ) ∂(MultivalRLSInit n r PositiveAlphabet).toMeasure) ^ 2 at Identity
    rw [UniformHammingExpectation, UniformHammingVariance] at Identity
    linarith
  have EventEq : {y | (Hamming Target y : ℝ) = 0} = {Target} := by
    ext y
    change (Hamming Target y : ℝ) = 0 ↔ y = Target
    rw [Nat.cast_eq_zero, HammingEqZeroIffEq]
  rw [EventEq, UniformHammingVariance, SecondMoment] at Bound
  have DenominatorPositive : 0 < (n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) +
      ((n : ℝ) * (1 - 1 / (r : ℝ))) ^ 2 := by positivity
  have FinalDenominatorPositive : 0 < 1 + (n : ℝ) * ((r : ℝ) - 1) := by positivity
  calc
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real {Target} ≤
      ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ))) /
        ((n : ℝ) * (1 - 1 / (r : ℝ)) * (1 / (r : ℝ)) +
          ((n : ℝ) * (1 - 1 / (r : ℝ))) ^ 2) := Bound
    _ = 1 / (1 + (n : ℝ) * ((r : ℝ) - 1)) := by
      apply (div_eq_div_iff DenominatorPositive.ne' FinalDenominatorPositive.ne').mpr
      field_simp

end
end ECTheoryLib.Analysis.RLSMultival

