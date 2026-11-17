import ECTheoryLib.Probability.RandomWalks.FiniteBiasedWalk
import ECTheoryLib.Tools.Drift.FiniteMarkovExact

/-!
# Exact mean runtime of a weak-drift random walk

The exact mean follows from the existing additive drift theorem, after checking
its local premises for the concrete transition law. For initial distance n and
bias 1/n^4 the mean is n^5. This corrects the displayed mean in Lengler's
Example 2.4.6; the example's high-probability assertion is not proved here.
-/

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval
noncomputable section

/-- Expected absorption time for any positive bias and any fixed initial state. -/
theorem FixedRuntimeExact (N : ℕ) (ε : I) (PositiveBias : 0 < (ε : ℝ)) (x : Fin (N+1)) :
    ExpectedHittingTime (Probability.FiniteBiasedWalk.Step N ε) (fun y => y.val=0) (PMF.pure x) =
      ENNReal.ofReal ((x.val : ℝ)/(ε : ℝ)) := by
  exact AdditiveRuntimeExactOfLocalDrift (Probability.FiniteBiasedWalk.Step N ε)
    Probability.FiniteBiasedWalk.Potential (fun y => y.val=0)
    (fun y => Nat.cast_nonneg y.val) (fun _ => Nat.cast_eq_zero)
    (ε : ℝ) PositiveBias (Probability.FiniteBiasedWalk.OneStepDrift N ε)
    (Probability.FiniteBiasedWalk.StepPreservesZero N ε) x

/-- The small drift parameter used by the book example. -/
def WeakBias (n : ℕ) (PositiveLength : 0 < n) : I := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have AtLeastOne : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  refine ⟨1/(n : ℝ)^4, ?_, ?_⟩
  · exact div_nonneg zero_le_one (pow_nonneg PositiveN.le 4)
  · exact (div_le_one (pow_pos PositiveN 4)).mpr (one_le_pow₀ AtLeastOne)

theorem WeakBiasPositive (n : ℕ) (PositiveLength : 0 < n) : 0 < (WeakBias n PositiveLength : ℝ) :=
  one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr PositiveLength) 4)

/-- With initial distance n and drift 1/n^4, the exact expectation is n^5, not n^4. -/
theorem WeakDriftExpectedRuntime (n : ℕ) (PositiveLength : 0 < n) (N : ℕ) (Capacity : n ≤ N) :
    ExpectedHittingTime (Probability.FiniteBiasedWalk.Step N (WeakBias n PositiveLength))
      (fun y => y.val=0) (PMF.pure ⟨n, Nat.lt_succ_iff.mpr Capacity⟩) = ENNReal.ofReal ((n : ℝ)^5) := by
  rw [FixedRuntimeExact N (WeakBias n PositiveLength) (WeakBiasPositive n PositiveLength)]
  apply congrArg ENNReal.ofReal
  change (n : ℝ)/(1/(n : ℝ)^4)=(n : ℝ)^5
  rw [one_div, div_inv_eq_mul]
  ring

end
end ECTheoryLib.Analysis.FiniteBiasedWalk
