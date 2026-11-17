import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Negative exponential moments from positive means and absolute moments

Mathlib supplies the exponential-series remainder and positive-term lower
bound. Real specialization and integration yield a quadratic error bound,
then a nonincreasing negative exponential moment at an explicit small parameter.
-/

namespace ECTheoryLib.Probability

/-- Real specialization of Mathlib's exponential-series remainder estimate. -/
theorem ExponentialQuadraticUpper (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp |x| := by
  have Bound := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add] at Bound
  have RealBound : |Real.exp x-(1+x)| ≤ x^2*Real.exp |x| := by
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using Bound
  have Upper := (abs_le.mp RealBound).2
  linarith

/-- A quadratic factor can be absorbed into an exponential with a larger
parameter, using Mathlib's positive exponential-series lower bound. -/
theorem SquaredWeightedExponentialBound (x q Lambda : ℝ) (PositiveQ : 0<q)
    (Small : Lambda≤q/2) :
    x^2*Real.exp (Lambda*|x|) ≤ (8/q^2)*Real.exp (q*|x|) := by
  have Series := Real.pow_div_factorial_le_exp (q*|x|/2)
    (div_nonneg (mul_nonneg PositiveQ.le (abs_nonneg x)) (by norm_num)) 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.mul_one, Nat.cast_ofNat] at Series
  have Numerator : x^2*q^2 ≤ 8*Real.exp (q*|x|/2) := by
    have SquareAbs := sq_abs x
    nlinarith
  have SquareBound : x^2 ≤ (8/q^2)*Real.exp (q*|x|/2) := by
    calc
      _ ≤ (8*Real.exp (q*|x|/2))/q^2 := (le_div_iff₀ (sq_pos_of_pos PositiveQ)).mpr Numerator
      _ = _ := by ring
  have ExpBound : Real.exp (Lambda*|x|) ≤ Real.exp (q*|x|/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg x]
  calc
    _ ≤ x^2*Real.exp (q*|x|/2) := mul_le_mul_of_nonneg_left ExpBound (sq_nonneg x)
    _ ≤ ((8/q^2)*Real.exp (q*|x|/2))*Real.exp (q*|x|/2) :=
      mul_le_mul_of_nonneg_right SquareBound (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_halves]

theorem NegativeExponentialQuadraticUpper (x q Lambda : ℝ) (PositiveQ : 0<q)
    (NonnegativeLambda : 0≤Lambda) (Small : Lambda≤q/2) :
    Real.exp (-Lambda*x) ≤ 1-Lambda*x+(8*Lambda^2/q^2)*Real.exp (q*|x|) := by
  have Taylor := ExponentialQuadraticUpper (-Lambda*x)
  have Absolute : |-Lambda*x|=Lambda*|x| := by rw [abs_mul, abs_neg, abs_of_nonneg NonnegativeLambda]
  rw [Absolute] at Taylor
  have Weighted := SquaredWeightedExponentialBound x q Lambda PositiveQ Small
  have Scaled := mul_le_mul_of_nonneg_left Weighted (sq_nonneg Lambda)
  calc
    _ ≤ 1-Lambda*x+Lambda^2*(x^2*Real.exp (Lambda*|x|)) := by nlinarith [Taylor]
    _ ≤ 1-Lambda*x+Lambda^2*((8/q^2)*Real.exp (q*|x|)) := add_le_add le_rfl Scaled
    _ = _ := by ring

end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Control of an absolute exponential moment supplies the integrability and
quadratic error needed for a negative exponential moment. -/
theorem PositiveMeanNegativeMomentOfAbsMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (q Delta M Lambda : ℝ) (PositiveQ : 0<q)
    (NonnegativeLambda : 0≤Lambda) (Small : Lambda≤q/2)
    (IntegrableZ : Integrable Z μ)
    (IntegrableAbsExp : Integrable (fun ω => Real.exp (q*|Z ω|)) μ)
    (MeanLower : Delta ≤ ∫ ω, Z ω ∂μ)
    (MomentUpper : (∫ ω, Real.exp (q*|Z ω|) ∂μ) ≤ M)
    (ParameterBound : 8*Lambda*M ≤ Delta*q^2) :
    (∫ ω, Real.exp (-Lambda*Z ω) ∂μ) ≤ 1 := by
  have ParameterLeQ : Lambda≤q := by linarith
  have ExpLeAbs (z : ℝ) : Real.exp (-Lambda*z) ≤ Real.exp (q*|z|) := by
    apply Real.exp_le_exp.mpr
    have NegativeLe := neg_le_abs z
    have Scaled := mul_le_mul_of_nonneg_left NegativeLe NonnegativeLambda
    have ParameterScale := mul_le_mul_of_nonneg_right ParameterLeQ (abs_nonneg z)
    nlinarith
  have IntegrableExp : Integrable (fun ω => Real.exp (-Lambda*Z ω)) μ := by
    apply IntegrableAbsExp.mono'
      (Real.measurable_exp.comp_aemeasurable (IntegrableZ.aemeasurable.const_mul (-Lambda))).aestronglyMeasurable
    apply ae_of_all
    intro ω
    change ‖Real.exp (-Lambda*Z ω)‖ ≤ Real.exp (q*|Z ω|)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact ExpLeAbs (Z ω)
  let C : ℝ := 8*Lambda^2/q^2
  have NonnegativeC : 0≤C := div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lambda)) (sq_nonneg q)
  have LinearIntegrable : Integrable (fun ω => 1-Lambda*Z ω) μ :=
    (integrable_const 1).sub (IntegrableZ.const_mul Lambda)
  have ScaledIntegrable : Integrable (fun ω => C*Real.exp (q*|Z ω|)) μ :=
    IntegrableAbsExp.const_mul C
  have AffineIntegrable : Integrable (fun ω => 1-Lambda*Z ω+C*Real.exp (q*|Z ω|)) μ :=
    LinearIntegrable.add ScaledIntegrable
  have PointwiseBound : (∫ ω, Real.exp (-Lambda*Z ω) ∂μ) ≤
      ∫ ω, 1-Lambda*Z ω+C*Real.exp (q*|Z ω|) ∂μ := by
    apply integral_mono_ae IntegrableExp AffineIntegrable
    exact ae_of_all _ (fun ω => NegativeExponentialQuadraticUpper (Z ω) q Lambda PositiveQ NonnegativeLambda Small)
  rw [integral_add LinearIntegrable ScaledIntegrable,
    integral_sub (integrable_const 1) (IntegrableZ.const_mul Lambda), integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_const_mul] at PointwiseBound
  have Error : C*M ≤ Lambda*Delta := by
    have Scaled := mul_le_mul_of_nonneg_left ParameterBound NonnegativeLambda
    dsimp [C]
    have Rearrange : 8*Lambda^2/q^2*M=(8*Lambda^2*M)/q^2 := by ring
    rw [Rearrange]
    apply (div_le_iff₀ (sq_pos_of_pos PositiveQ)).mpr
    nlinarith
  have MeanScale := mul_le_mul_of_nonneg_left MeanLower NonnegativeLambda
  have MomentScale := mul_le_mul_of_nonneg_left MomentUpper NonnegativeC
  linarith

end
end ECTheoryLib.Probability
