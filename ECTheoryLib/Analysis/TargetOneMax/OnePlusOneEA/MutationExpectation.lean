import ECTheoryLib.Analysis.BitMutation.HammingExpectation
import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Probability.PMF.FinitePMF

namespace ECTheoryLib.Analysis.TargetOneMaxEA

open MeasureTheory ECTheoryLib.Problems ECTheoryLib.Problems.TargetOneMax
open ECTheoryLib.Probability ECTheoryLib.Analysis.BitMutation

noncomputable section

/-- The existing EA's weak minimization selection truncates the candidate distance.
The objective uses the source's offspring-first Hamming order. -/
theorem StepHammingExpectation {n : Nat} (PositiveLength : 0 < n)
    (Parent Target : Bits n) :
    (∫ Next, (Hamming Next Target : ℝ)
      ∂(OnePlusOneEAStep PositiveLength
        (MinNotWorse (fun State => Hamming State Target)) Parent).toMeasure) =
      ∫ Candidate, min (Hamming Parent Target : ℝ) (Hamming Candidate Target : ℝ)
        ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  rw [OnePlusOneEAStep, PMFIntegralMap]
  apply integral_congr_ae
  apply ae_of_all
  intro Candidate
  dsimp only
  rw [← Nat.cast_min]
  apply congrArg (fun k : Nat => (k : ℝ))
  unfold ElitistSelect
  split_ifs with Accept
  · exact (min_eq_right Accept).symm
  · exact (min_eq_left (le_of_not_ge Accept)).symm

/-- The selected mean is no larger than the raw mutation mean or the parent distance.
This bound does not identify the candidate mean with the selected mean. -/
theorem StepHammingExpectationLe {n : Nat} (PositiveLength : 0 < n)
    (Parent Target : Bits n) :
    (∫ Next, (Hamming Next Target : ℝ)
      ∂(OnePlusOneEAStep PositiveLength
        (MinNotWorse (fun State => Hamming State Target)) Parent).toMeasure) ≤
      min (Hamming Parent Target : ℝ)
        ((Hamming Parent Target : ℝ) + 1 - 2 * (Hamming Parent Target : ℝ) / (n : ℝ)) := by
  rw [StepHammingExpectation]
  apply le_min
  · calc
      _ ≤ ∫ _Candidate : Bits n, (Hamming Parent Target : ℝ)
          ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
        apply integral_mono Integrable.of_finite (integrable_const _)
        intro Candidate
        exact min_le_left _ _
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  · calc
      _ ≤ ∫ Candidate, (Hamming Candidate Target : ℝ)
          ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro Candidate
        exact min_le_right _ _
      _ = _ := StandardMutationTargetHammingExpectation PositiveLength Parent Target

end
end ECTheoryLib.Analysis.TargetOneMaxEA

