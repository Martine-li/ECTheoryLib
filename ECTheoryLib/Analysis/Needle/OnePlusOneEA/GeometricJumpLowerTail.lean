import ECTheoryLib.Analysis.Needle.OnePlusOneEA.Drift
import ECTheoryLib.Tools.Runtime.GeometricJumpLowerTail

/-!
# Geometric-jump negative drift for the actual standard-mutation EA

The accepted absolute increment has tail at most e/2^j. The generic runtime
interface yields a lower tail with explicit constants. The direct-moment
result in RuntimeLowerBounds remains sharper.
-/

namespace ECTheoryLib.Analysis.EAOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Actual accepted potential jumps have a geometric absolute tail. This
includes zero flips, multiple flips, and the absorbing optimum. -/
theorem OneStepAbsoluteJumpTail {n : ℕ} (PositiveLength : 0<n) (x : Bits n) (j : ℕ) :
    (Step PositiveLength x).toMeasure {y | (j : ℝ)≤|Potential y-Potential x|} ≤
      ENNReal.ofReal (Real.exp 1/(2 : ℝ)^j) := by
  let μ := (Step PositiveLength x).toMeasure
  have Markov := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun y => |Potential y-Potential x|)
    (j : ℝ) (Real.log_nonneg (by norm_num : (1 : ℝ)≤2)) Integrable.of_finite
  have Moment := OneStepAbsoluteExponentialMoment PositiveLength x
  have Bound : μ.real {y | (j : ℝ)≤|Potential y-Potential x|} ≤
      Real.exp (-(Real.log 2)*(j : ℝ))*Real.exp 1 := by
    exact Markov.trans (mul_le_mul_of_nonneg_left Moment (Real.exp_pos _).le)
  have Power : Real.exp (-(Real.log 2)*(j : ℝ)) = 1/(2 : ℝ)^j := by
    rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)]
    rw [one_div]
  rw [Power, one_div, inv_mul_eq_div] at Bound
  have BoundENN := ENNReal.ofReal_le_ofReal Bound
  rw [ofReal_measureReal] at BoundENN
  exact BoundENN

/-- Exponent produced when the actual mutation tail is supplied through the
geometric-jump interface instead of a directly available moment bound. -/
def GeometricRuntimeExponent : ℝ := GeometricJumpDriftExponent 1 (1/2) (Real.exp 1)

theorem GeometricRuntimeExponentPositive : 0<GeometricRuntimeExponent :=
  GeometricJumpDriftExponentPositive _ _ _ (by norm_num) (by norm_num) (Real.exp_pos _)

/-- Actual standard-mutation EA on Needle, validating the complete
kernel-to-path geometric-jump interface. The direct-moment bound is sharper. -/
theorem FixedRuntimeGeometricJumpLowerTail {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4≤Potential InitialState) (t : ℕ) :
    PathMeasure (Step PositiveLength) (PMF.pure InitialState)
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*(6*Real.exp 1)*Real.exp (-GeometricRuntimeExponent*((n : ℝ)/4))) := by
  have Initial : ∀ᵐ x ∂(PMF.pure InitialState).toMeasure, (n : ℝ)/4≤Potential x := by
    rw [PMF.toMeasure_pure]
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr InitiallyFar
  have Bound := Tools.Runtime.GeometricJumpRuntimeLowerTail (Step PositiveLength) (PMF.pure InitialState)
    Potential IsTarget 0 ((n : ℝ)/4) 1 (1/2) (Real.exp 1)
    (div_pos (Nat.cast_pos.mpr PositiveLength) (by norm_num)) (by norm_num) (by norm_num) (Real.exp_pos _)
    (fun x => by
      rw [← PotentialEqZeroIffTarget]
      exact ⟨fun Zero => le_antisymm Zero (PotentialNonnegative _), fun Zero => Zero.le⟩)
    Initial (StepTargetAbsorbing PositiveLength) (by
      intro x _Above j
      simpa only [show (1 : ℝ)+1=2 by norm_num] using OneStepAbsoluteJumpTail PositiveLength x j)
    (by
      intro x Above Below
      have Away : ¬IsTarget x := fun Target => by
        have Zero := (PotentialEqZeroIffTarget x).mpr Target
        linarith
      rw [OneStepDriftAway PositiveLength x Away]
      have Ratio : 2*Potential x/(n : ℝ)<1/2 :=
        (div_lt_iff₀ (Nat.cast_pos.mpr PositiveLength)).mpr (by linarith)
      linarith) t
  have Constant : GeometricJumpMomentBound 1 (Real.exp 1)=6*Real.exp 1 := by
    dsimp [GeometricJumpMomentBound]
    ring
  simpa only [sub_zero, Constant, GeometricRuntimeExponent] using Bound

end
end ECTheoryLib.Analysis.EAOnNeedle
