import ECTheoryLib.Analysis.BitMutationConcentration
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift

/-!
# Jump-distance tail for the actual selected OneMax EA transition

The candidate has the standard-mutation Chernoff bound. Pointwise, elitist
selection either accepts that candidate or returns the parent, so the
distance of the actual next state is no greater. The result is valid for
every positive bit-string length, including the one-bit boundary.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax ECTheoryLib.Analysis.BitMutation
noncomputable section

/-- Selection either retains the candidate or returns the parent, so the actual step inherits the tail. -/
theorem StepHammingChernoff {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (Step PositiveLength Parent).toMeasure.real {Next | 1+d ≤ (Hamming Parent Next : ℝ)} ≤
      Real.exp (-((1+d)*Real.log (1+d)-d)) := by
  have DistanceBound (Candidate : Bits n) : Hamming Parent (Update Parent Candidate) ≤ Hamming Parent Candidate := by
    unfold Update ElitistSelect
    split_ifs
    · exact le_rfl
    · rw [(HammingEqZeroIffEq Parent Parent).mpr rfl]
      exact Nat.zero_le _
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (StandardBitMutation PositiveLength Parent).toMeasure.real
        {y | 1+d ≤ (Hamming Parent y : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Candidate Member
      change 1+d ≤ (Hamming Parent (Update Parent Candidate) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (DistanceBound Candidate))
    _ ≤ _ := StandardMutationHammingChernoff PositiveLength Parent d Nonnegative

end
end ECTheoryLib.Analysis.EAOneMax

/-!
## Base-two bound for large selected jumps

The threshold 2*e is independent of bit-string length because standard
mutation has expected Hamming distance one.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax ECTheoryLib.Analysis.BitMutation
noncomputable section

/-- The actual selected EA next state inherits the base-two jump-distance tail. -/
theorem StepHammingBaseTwoTail {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (k : ℝ) (LargeThreshold : 2*Real.exp 1 ≤ k) :
    (Step PositiveLength Parent).toMeasure.real {Next | k ≤ (Hamming Parent Next : ℝ)} ≤
      (2 : ℝ)^(-k) := by
  have DistanceBound (Candidate : Bits n) : Hamming Parent (Update Parent Candidate) ≤ Hamming Parent Candidate := by
    unfold Update ElitistSelect
    split_ifs
    · exact le_rfl
    · rw [(HammingEqZeroIffEq Parent Parent).mpr rfl]
      exact Nat.zero_le _
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (StandardBitMutation PositiveLength Parent).toMeasure.real
        {y | k ≤ (Hamming Parent y : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Candidate Member
      change k ≤ (Hamming Parent (Update Parent Candidate) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (DistanceBound Candidate))
    _ ≤ _ := StandardMutationHammingBaseTwoTail PositiveLength Parent k LargeThreshold

end
end ECTheoryLib.Analysis.EAOneMax

/-!
## Quadratic-rational jump bound
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
noncomputable section

/-- The actual selected EA step inherits the quadratic-rational Chernoff distance bound. -/
theorem StepHammingChernoffQuadratic {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (Step PositiveLength Parent).toMeasure.real {Next | 1+d ≤ (Hamming Parent Next : ℝ)} ≤
      Real.exp (-(d^2)/(2+2*d/3)) := by
  apply (StepHammingChernoff PositiveLength Parent d Nonnegative).trans
  apply Real.exp_le_exp.mpr
  have Lower := ChernoffExponentQuadraticLower d Nonnegative
  simpa only [neg_div] using neg_le_neg Lower

end
end ECTheoryLib.Analysis.EAOneMax

/-!
## Finite-size bound for the selected next state

Pointwise distance order transfers the strongest expression, including
the exact zero beyond the bit-string length.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax ECTheoryLib.Analysis.BitMutation
noncomputable section

/-- The actual selected EA next state inherits the full finite-size jump-distance bound. -/
theorem StepHammingFiniteChernoff {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (Step PositiveLength Parent).toMeasure.real {Next | 1+d ≤ (Hamming Parent Next : ℝ)} ≤
      FiniteChernoffUpperBound n 1 d := by
  have DistanceBound (Candidate : Bits n) : Hamming Parent (Update Parent Candidate) ≤ Hamming Parent Candidate := by
    unfold Update ElitistSelect
    split_ifs
    · exact le_rfl
    · rw [(HammingEqZeroIffEq Parent Parent).mpr rfl]
      exact Nat.zero_le _
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (StandardBitMutation PositiveLength Parent).toMeasure.real
        {y | 1+d ≤ (Hamming Parent y : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Candidate Member
      change 1+d ≤ (Hamming Parent (Update Parent Candidate) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (DistanceBound Candidate))
    _ ≤ _ := StandardMutationHammingFiniteChernoff PositiveLength Parent d Nonnegative

end
end ECTheoryLib.Analysis.EAOneMax

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax ECTheoryLib.Analysis.BitMutation
noncomputable section

/-- The actual selected zero-count jump has a closed geometric tail at every
natural threshold. The constant is `exp 1`, with no large-threshold restriction. -/
theorem StepPotentialGeometricTail {n : ℕ} (PositiveLength : 0 < n)
    (Parent : Bits n) (k : ℕ) :
    (Step PositiveLength Parent).toMeasure.real
      {Next | (k : ℝ) ≤ |Potential Next - Potential Parent|} ≤
      Real.exp 1 / (2 : ℝ) ^ k := by
  classical
  have SelectedDistance (Candidate : Bits n) :
      |Potential (Update Parent Candidate) - Potential Parent| ≤
        (Hamming Parent Candidate : ℝ) := by
    unfold Update ElitistSelect
    split_ifs
    · exact ZeroCountDifferenceLeHamming Parent Candidate
    · simpa only [sub_self, abs_zero] using
        (Nat.cast_nonneg (Hamming Parent Candidate) :
          (0 : ℝ) ≤ (Hamming Parent Candidate : ℝ))
  have Moment :
      mgf (fun y => (Hamming Parent y : ℝ))
        (StandardBitMutation PositiveLength Parent).toMeasure (Real.log 2) ≤
        Real.exp 1 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) - 1 = 1 by norm_num] using
      StandardMutationHammingMGFBound PositiveLength Parent (Real.log 2)
  have ExponentialFactor : Real.exp (-(Real.log 2) * (k : ℝ)) =
      ((2 : ℝ) ^ k)⁻¹ := by
    rw [show -(Real.log 2) * (k : ℝ) = -((k : ℝ) * Real.log 2) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have CandidateTail : (StandardBitMutation PositiveLength Parent).toMeasure.real
      {Candidate | (k : ℝ) ≤ (Hamming Parent Candidate : ℝ)} ≤
        Real.exp 1 / (2 : ℝ) ^ k := by
    calc
      _ ≤ Real.exp (-(Real.log 2) * (k : ℝ)) *
          mgf (fun y => (Hamming Parent y : ℝ))
            (StandardBitMutation PositiveLength Parent).toMeasure (Real.log 2) :=
        measure_ge_le_exp_mul_mgf (k : ℝ)
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le (Integrable.of_finite)
      _ ≤ Real.exp (-(Real.log 2) * (k : ℝ)) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left Moment (Real.exp_pos _).le
      _ = Real.exp 1 / (2 : ℝ) ^ k := by
        rw [ExponentialFactor, div_eq_mul_inv, mul_comm]
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (StandardBitMutation PositiveLength Parent).toMeasure.real
        {Candidate | (k : ℝ) ≤ (Hamming Parent Candidate : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Candidate Member
      change (k : ℝ) ≤ |Potential (Update Parent Candidate) - Potential Parent| at Member
      exact Member.trans (SelectedDistance Candidate)
    _ ≤ _ := CandidateTail

end
end ECTheoryLib.Analysis.EAOneMax
