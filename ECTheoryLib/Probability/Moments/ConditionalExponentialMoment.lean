import ECTheoryLib.Probability.Moments.AbsoluteExponentialMoment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Integrability and full-history exponential remainder bounds

Explicit integrability prevents default real integral values from entering.
Mathlib conditional-expectation linearity and monotonicity lift the remainder.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Absolute exponential integrability controls a smaller negative exponent. -/
theorem NegativeExponentialIntegrableOfAbsolute (μ : Measure Ω) (Z : Ω → ℝ)
    (q Lambda : ℝ) (NonnegativeLambda : 0≤Lambda) (Small : Lambda≤q)
    (Observable : AEMeasurable Z μ)
    (IntegrableAbsExp : Integrable (fun ω => Real.exp (q*|Z ω|)) μ) :
    Integrable (fun ω => Real.exp (-Lambda*Z ω)) μ := by
  apply IntegrableAbsExp.mono'
    (Real.measurable_exp.comp_aemeasurable (Observable.const_mul (-Lambda))).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖Real.exp (-Lambda*Z ω)‖≤Real.exp (q*|Z ω|)
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have Negated := mul_le_mul_of_nonneg_left (neg_le_abs (Z ω)) NonnegativeLambda
    have Scaled := mul_le_mul_of_nonneg_right Small (abs_nonneg (Z ω))
    nlinarith)

/-- Conditional Taylor bound with genuine integrability premises, so the
default value of a nonintegrable real conditional expectation cannot enter. -/
theorem ConditionalNegativeExponentialQuadraticUpper (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (Below : m ≤ m0) (Z : Ω → ℝ)
    (q Lambda : ℝ) (PositiveQ : 0<q) (NonnegativeLambda : 0≤Lambda) (Small : Lambda≤q/2)
    (IntegrableZ : Integrable Z μ)
    (IntegrableAbsExp : Integrable (fun ω => Real.exp (q*|Z ω|)) μ) :
    (μ[fun ω => Real.exp (-Lambda*Z ω) | m]) ≤ᵐ[μ]
      (fun ω => 1-Lambda*(μ[Z | m]) ω+(8*Lambda^2/q^2)*(μ[fun u => Real.exp (q*|Z u|) | m]) ω) := by
  let A := fun ω => Real.exp (q*|Z ω|)
  let C := 8*Lambda^2/q^2
  have IntegrableExp := NegativeExponentialIntegrableOfAbsolute (m0 := m0) μ Z q Lambda
    NonnegativeLambda (by linarith) IntegrableZ.aemeasurable IntegrableAbsExp
  have Linear : Integrable (fun ω => (1 : ℝ)-Lambda*Z ω) μ :=
    (integrable_const 1).sub (IntegrableZ.const_mul Lambda)
  have Bound := condExp_mono (m := m) IntegrableExp (Linear.add (IntegrableAbsExp.const_mul C))
    (ae_of_all _ (fun ω => NegativeExponentialQuadraticUpper (Z ω) q Lambda PositiveQ NonnegativeLambda Small))
  have Add := condExp_add Linear (IntegrableAbsExp.const_mul C) m
  have Sub := condExp_sub (integrable_const (1 : ℝ)) (IntegrableZ.const_mul Lambda) m
  have LinearScale := condExp_smul (μ := μ) Lambda Z m
  have MomentScale := condExp_smul (μ := μ) C A m
  filter_upwards [Bound,Add,Sub,LinearScale,MomentScale] with ω Bound Add Sub LinearScale MomentScale
  change (μ[fun ω => (1 : ℝ)-Lambda*Z ω | m]) ω =
    (μ[fun _ => (1 : ℝ) | m]) ω-(μ[fun ω => Lambda*Z ω | m]) ω at Sub
  change (μ[fun ω => Real.exp (-Lambda*Z ω) | m]) ω ≤
    (μ[(fun ω => (1 : ℝ)-Lambda*Z ω)+(fun ω => C*A ω) | m]) ω at Bound
  rw [Add] at Bound
  change (μ[fun ω => Real.exp (-Lambda*Z ω) | m]) ω ≤
    (μ[fun ω => (1 : ℝ)-Lambda*Z ω | m]) ω+(μ[fun ω => C*A ω | m]) ω at Bound
  rw [Sub] at Bound
  rw [condExp_const Below] at Bound
  change (μ[fun ω => Real.exp (-Lambda*Z ω) | m]) ω ≤
    1-(μ[Lambda • Z | m]) ω+(μ[C • A | m]) ω at Bound
  rw [LinearScale,MomentScale] at Bound
  exact Bound

end
end ECTheoryLib.Probability
