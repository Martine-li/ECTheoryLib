import ECTheoryLib.Analysis.BitMutationConcentration
import ECTheoryLib.Probability.Concentration.FailureThreshold
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Power and failure-probability bounds for mutation distance

These bounds concern Hamming distance under the actual IndependentBitMutation
proposal law. They reuse its expectation and Chernoff theorem; product laws and
independence are not rebuilt. The power bound includes every positive real
threshold, empty strings and both mutation-rate endpoints. The corrected inverse
threshold additionally requires positive alpha and the original failure range.
No selection or multiround path is represented by these one-step statements.
-/

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory Set ECTheoryLib ECTheoryLib.Problems.TargetOneMax
open ECTheoryLib.Probability.PowerTailThreshold
open scoped unitInterval
noncomputable section

/-- The power-form bound for actual independent bit mutation at any positive real threshold. Includes empty strings, zero rate, full rate and thresholds below the mean. -/
theorem MutationHammingPowerTail {n : ℕ} (p : I) (Parent : Bits n)
    (k : ℝ) (PositiveThreshold : 0 < k) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤
      (Real.exp 1 * ((n : ℝ) * (p : ℝ)) / k) ^ k := by
  classical
  let P :=
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let m : ℝ := (n : ℝ) * (p : ℝ)
  change P.real {y | k ≤ (Hamming Parent y : ℝ)} ≤ (Real.exp 1 * m / k) ^ k
  have NonnegativeMean : 0 ≤ m := mul_nonneg (Nat.cast_nonneg n) p.2.1
  have Mean : (∫ y, (Hamming Parent y : ℝ) ∂P) = m :=
    MutationHammingExpectation p Parent
  by_cases ZeroMean : m = 0
  · -- This handles both n=0 and p=0, without dividing by m.
    have Markov : k * P.real {y | k ≤ (Hamming Parent y : ℝ)} ≤
        ∫ y, (Hamming Parent y : ℝ) ∂P :=
      mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ (fun y => Nat.cast_nonneg (Hamming Parent y)))
        Integrable.of_finite k
    rw [Mean, ZeroMean] at Markov
    have TailZero : P.real {y | k ≤ (Hamming Parent y : ℝ)} ≤ 0 := by
      apply (mul_le_mul_iff_right₀ PositiveThreshold).1
      simpa only [mul_zero] using Markov
    simpa only [ZeroMean, mul_zero, zero_div, Real.zero_rpow PositiveThreshold.ne'] using TailZero
  · have PositiveMean : 0 < m := lt_of_le_of_ne NonnegativeMean (Ne.symm ZeroMean)
    by_cases ThresholdAtLeastMean : m ≤ k
    · let d : ℝ := k / m - 1
      have NonnegativeD : 0 ≤ d := by
        apply sub_nonneg.mpr
        apply (le_div_iff₀ PositiveMean).2
        simpa only [one_mul] using ThresholdAtLeastMean
      have OneAddD : 1 + d = k / m := by dsimp [d]; ring
      have Threshold : (1 + d) * m = k := by
        rw [OneAddD]
        exact div_mul_cancel₀ k PositiveMean.ne'
      have DTimesMean : d * m = k - m := by
        calc
          d * m = (1 + d) * m - m := by ring
          _ = k - m := by rw [Threshold]
      have LogRelative : Real.log (1 + d) = Real.log k - Real.log m := by
        rw [OneAddD, Real.log_div PositiveThreshold.ne' PositiveMean.ne']
      have PositiveBase : 0 < Real.exp 1 * m / k :=
        div_pos (mul_pos (Real.exp_pos 1) PositiveMean) PositiveThreshold
      have LogBase : Real.log (Real.exp 1 * m / k) = 1 + Real.log m - Real.log k := by
        rw [Real.log_div (mul_pos (Real.exp_pos 1) PositiveMean).ne' PositiveThreshold.ne',
          Real.log_mul (Real.exp_pos 1).ne' PositiveMean.ne', Real.log_exp]
      have ExponentIdentity :
          -((1 + d) * Real.log (1 + d) - d) * m =
            Real.log (Real.exp 1 * m / k) * k - m := by
        rw [LogRelative, LogBase]
        calc
          -((1 + d) * (Real.log k - Real.log m) - d) * m =
              -(Real.log k - Real.log m) * ((1 + d) * m) + d * m := by ring
          _ = (1 + Real.log m - Real.log k) * k - m := by
            rw [Threshold, DTimesMean]
            ring
      have Bound := MutationHammingChernoff p Parent d NonnegativeD
      change P.real {y | (1 + d) * m ≤ (Hamming Parent y : ℝ)} ≤
        Real.exp (-((1 + d) * Real.log (1 + d) - d) * m) at Bound
      rw [Threshold] at Bound
      refine Bound.trans ?_
      rw [Real.rpow_def_of_pos PositiveBase]
      apply Real.exp_le_exp.mpr
      rw [ExponentIdentity]
      exact sub_le_self _ NonnegativeMean
    · -- A small positive threshold is controlled by the probability bound one.
      have ThresholdBelowMean : k ≤ m := le_of_lt (lt_of_not_ge ThresholdAtLeastMean)
      have ExpAtLeastOne : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      have MeanLeExpMean : m ≤ Real.exp 1 * m := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ExpAtLeastOne NonnegativeMean
      have BaseAtLeastOne : 1 ≤ Real.exp 1 * m / k := by
        apply (le_div_iff₀ PositiveThreshold).2
        simpa only [one_mul] using ThresholdBelowMean.trans MeanLeExpMean
      exact measureReal_le_one.trans (Real.one_le_rpow BaseAtLeastOne PositiveThreshold.le)

/-- Book Lemma 1.10.3(a) at legal rate alpha/n. Includes alpha = 0 and all positive real thresholds. -/
theorem MutationHammingPowerTailAlpha {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (α k : ℝ) (AlphaNonnegative : 0 ≤ α)
    (AlphaAtMostLength : α ≤ (n : ℝ)) (PositiveThreshold : 0 < k) :
    let p : I := ⟨α / (n : ℝ),
      ⟨div_nonneg AlphaNonnegative (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.mpr PositiveLength)).2 AlphaAtMostLength⟩⟩
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤ (Real.exp 1 * α / k) ^ k := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨α / (n : ℝ),
    ⟨div_nonneg AlphaNonnegative (Nat.cast_nonneg n),
      (div_le_one PositiveReal).2 AlphaAtMostLength⟩⟩
  change
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤ (Real.exp 1 * α / k) ^ k
  have Mean : (n : ℝ) * (p : ℝ) = α := by
    change (n : ℝ) * (α / (n : ℝ)) = α
    rw [mul_comm]
    exact div_mul_cancel₀ α PositiveReal.ne'
  have Bound := MutationHammingPowerTail p Parent k PositiveThreshold
  simpa only [Mean] using Bound

/-- The corrected book Lemma 1.10.3(b) for the actual alpha/n candidate law, with the original q range and every larger threshold. -/
theorem MutationHammingFailureThreshold {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (α q k : ℝ) (PositiveAlpha : 0 < α)
    (AlphaAtMostLength : α ≤ (n : ℝ)) (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)))
    (LargeThreshold : failureThreshold α q ≤ k) :
    let p : I := ⟨α / (n : ℝ),
      ⟨div_nonneg PositiveAlpha.le (Nat.cast_nonneg n),
        (div_le_one (Nat.cast_pos.mpr PositiveLength)).mpr AlphaAtMostLength⟩⟩
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤ q := by
  have Range := failureThreshold_originalRange α q PositiveAlpha PositiveQ SourceRange
  have PositiveK : 0 < k :=
    (mul_pos PositiveAlpha (repairedThreshold_positive _ Range)).trans_le LargeThreshold
  exact (MutationHammingPowerTailAlpha PositiveLength Parent α k PositiveAlpha.le
    AlphaAtMostLength PositiveK).trans
    (failureThreshold_powerBound α q k PositiveAlpha PositiveQ SourceRange LargeThreshold)

end
end ECTheoryLib.Analysis.BitMutation
