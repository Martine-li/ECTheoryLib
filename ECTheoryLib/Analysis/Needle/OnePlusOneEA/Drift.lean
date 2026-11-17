import ECTheoryLib.Analysis.Needle.OnePlusOneEA.Model
import ECTheoryLib.Analysis.OneMax.MutationExpectation
import ECTheoryLib.Analysis.BitMutationConcentration

/-!
# Actual ordinary drift and absolute exponential moments on Needle

The signed decrease is 2V/n-1 away from the optimum. The Hamming MGF
bounds the absolute distance-change MGF uniformly in n.
-/

namespace ECTheoryLib.Analysis.EAOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Away from the target, ordinary expected signed progress is the same
2V/n-1 as for a one-bit proposal; multiple mutations are still retained. -/
theorem OneStepDriftAway {n : ℕ} (PositiveLength : 0<n) (x : Bits n) (Away : ¬ IsTarget x) :
    (∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure) =
      2*Potential x/(n : ℝ)-1 := by
  rw [StepAway PositiveLength x Away, integral_sub (integrable_const _) Integrable.of_finite,
    integral_const, probReal_univ, one_smul]
  change Potential x-(∫ y, (Problems.OneMax.ZeroCount y : ℝ)
    ∂(StandardBitMutation PositiveLength x).toMeasure)=_
  rw [OneMaxMutation.StandardMutationZeroCountExpectation]
  change Potential x-(1+(1-2/(n : ℝ))*Potential x)=_
  ring

/-- Absolute accepted-distance increments have an exponential moment bounded
by exp(1), uniformly in the dimension and including the absorbing target. -/
theorem OneStepAbsoluteExponentialMoment {n : ℕ} (PositiveLength : 0<n) (x : Bits n) :
    (∫ y, Real.exp (Real.log 2*|Potential y-Potential x|) ∂(Step PositiveLength x).toMeasure) ≤ Real.exp 1 := by
  have LogNonnegative : 0≤Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [Step, OnePlusOneEAStep, PMFIntegralMap]
  have Local (Candidate : Bits n) :
      Real.exp (Real.log 2*|Potential (ElitistSelect (Problems.MaxNotWorse Fitness) x Candidate)-Potential x|) ≤
        Real.exp (Real.log 2*(Problems.TargetOneMax.Hamming x Candidate : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (SelectedPotentialJumpBound x Candidate) LogNonnegative)
  have Bound := integral_mono_ae (μ := (StandardBitMutation PositiveLength x).toMeasure)
    Integrable.of_finite Integrable.of_finite (ae_of_all _ Local)
  have MGF := BitMutation.StandardMutationHammingMGFBound PositiveLength x (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ)<2), show (2 : ℝ)-1=1 by norm_num] at MGF
  exact Bound.trans MGF

end
end ECTheoryLib.Analysis.EAOnNeedle
