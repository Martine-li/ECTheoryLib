import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uncentered bounded-variable exponential moments

Mathlib supplies Hoeffding's centered MGF lemma. This module only removes
centering, normalizes the interval width, and exposes a positive-mean
negative-exponential corollary for subsequent drift applications.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The uncentered form of Mathlib's bounded-variable Hoeffding MGF lemma.
No independence assumption is involved in this single-variable statement. -/
theorem BoundedVariableExponentialMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (a b t : ℝ)
    (MeasurableZ : AEMeasurable Z μ) (Bounded : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc a b) :
    (∫ ω, Real.exp (t*Z ω) ∂μ) ≤
      Real.exp (t*(∫ ω, Z ω ∂μ)+(b-a)^2*t^2/8) := by
  let Mean := ∫ ω, Z ω ∂μ
  have Centered := hasSubgaussianMGF_of_mem_Icc MeasurableZ Bounded
  have Bound := Centered.mgf_le t
  have Parameter : (((‖b-a‖₊/2)^2 : NNReal) : ℝ)=(b-a)^2/4 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
    rw [div_pow, sq_abs]
    ring
  rw [Parameter] at Bound
  have Recenter : (∫ ω, Real.exp (t*Z ω) ∂μ) =
      Real.exp (t*Mean) * mgf (fun ω => Z ω-Mean) μ t := by
    rw [mgf, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Recenter]
  calc
    _ ≤ Real.exp (t*Mean)*Real.exp ((b-a)^2/4*t^2/2) :=
      mul_le_mul_of_nonneg_left Bound (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [Mean]; ring

/-- A bounded increment with positive mean has a nonincreasing negative
exponential moment at a sufficiently small nonnegative parameter. -/
theorem BoundedPositiveMeanNegativeMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (c Delta Lambda : ℝ)
    (MeasurableZ : AEMeasurable Z μ) (Bounded : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc (-c) c)
    (MeanLower : Delta ≤ ∫ ω, Z ω ∂μ) (NonnegativeLambda : 0 ≤ Lambda)
    (SmallParameter : Lambda*c^2 ≤ 2*Delta) :
    (∫ ω, Real.exp (-Lambda*Z ω) ∂μ) ≤ 1 := by
  have Bound := BoundedVariableExponentialMoment μ Z (-c) c (-Lambda) MeasurableZ Bounded
  apply Bound.trans
  apply Real.exp_le_one_iff.mpr
  have MeanScale := mul_le_mul_of_nonneg_left MeanLower NonnegativeLambda
  have SmallScale := mul_le_mul_of_nonneg_left SmallParameter NonnegativeLambda
  nlinarith

end
end ECTheoryLib.Probability
