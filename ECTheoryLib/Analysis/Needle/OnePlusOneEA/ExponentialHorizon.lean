import ECTheoryLib.Analysis.Needle.OnePlusOneEA.GeometricJumpLowerTail
import ECTheoryLib.Tools.Drift.GeometricJumpAsymptotics

/-!
# Exponential-time lower tail for the actual standard-mutation EA

The dimension threshold, initial distance and time horizon are all explicit.
The geometric-jump trajectory bound is retained unchanged.
-/

namespace ECTheoryLib.Analysis.EAOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- A fully explicit exponential horizon for the real standard-mutation EA.
The dimension threshold states exactly when the fixed prefactor is absorbed. -/
theorem FixedRuntimeExponentialHorizon {n : ℕ} (PositiveLength : 0<n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4≤Potential InitialState)
    (LongEnough : 16*Real.log (6*Real.exp 1)≤GeometricRuntimeExponent*(n : ℝ))
    (t : ℕ) (Horizon : (t : ℝ)≤Real.exp (GeometricRuntimeExponent*(n : ℝ)/8)) :
    PathMeasure (Step PositiveLength) (PMF.pure InitialState)
      {Path | FirstHittingTime IsTarget Path≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-GeometricRuntimeExponent*(n : ℝ)/16)) := by
  have Bound := FixedRuntimeGeometricJumpLowerTail PositiveLength InitialState InitiallyFar t
  have Numeric := NegativeDriftExponentialHorizonValue (t : ℝ) (n : ℝ) 1 (6*Real.exp 1)
    (GeometricRuntimeExponent/4) (GeometricRuntimeExponent/4)
    (Nat.cast_nonneg _) (by norm_num) (mul_pos (by norm_num) (Real.exp_pos _))
    (by simp) (by simpa only [mul_one, div_div] using (show Real.log (6*Real.exp 1)≤
      GeometricRuntimeExponent/4*(n : ℝ)/4 by nlinarith [LongEnough])) (by
      simpa only [mul_one,
        show GeometricRuntimeExponent/4*(n : ℝ)/2=GeometricRuntimeExponent*(n : ℝ)/8 by ring]
        using Horizon)
  apply Bound.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show -(GeometricRuntimeExponent/4)*(n : ℝ)/(4*1)=
    -GeometricRuntimeExponent*(n : ℝ)/16 by ring] at Numeric
  rw [mul_one, show -(GeometricRuntimeExponent/4)*(n : ℝ)=
    -GeometricRuntimeExponent*((n : ℝ)/4) by ring] at Numeric
  exact Numeric

end
end ECTheoryLib.Analysis.EAOnNeedle
