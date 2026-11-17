import ECTheoryLib.Tools.Drift.ExponentialMomentNegative
import ECTheoryLib.Tools.Drift.IntegrableExponentialBarrier
import ECTheoryLib.Probability.Moments.ConditionalExponentialMoment

/-!
# Negative drift for integrable increments and absolute exponential moments

No common finite range or integrability of the level itself is required.
Increment and absolute-moment integrability, adaptation and absorption are explicit.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full-history absolute-moment negative drift on a general real-valued
process, with explicit increment and absolute exponential integrability.
There is no common finite potential range. This entry retains absorption. -/
theorem GeneralExponentialMomentNegativeDriftTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (a b q Delta M : ℝ)
    (Ordered : a<b) (PositiveQ : 0<q) (PositiveDelta : 0<Delta) (PositiveM : 0<M)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (IncrementIntegrable : ∀ t, Integrable (fun ω => X (t+1) ω-X t ω) μ)
    (AbsoluteIntegrable : ∀ t, Integrable (fun ω => Real.exp (q*|X (t+1) ω-X t ω|)) μ)
    (AbsoluteMoment : ∀ t, ∀ᵐ ω ∂μ, a<X t ω →
      (μ[fun u => Real.exp (q*|X (t+1) u-X t u|) | F t]) ω ≤ M)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      Delta ≤ (μ[fun u => X (t+1) u-X t u | F t]) ω) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*M*Real.exp (-AbsoluteMomentDriftExponent q Delta M*(b-a))) := by
  let Lambda := AbsoluteMomentDriftExponent q Delta M
  have PositiveLambda : 0<Lambda := AbsoluteMomentDriftExponentPositive q Delta M PositiveQ PositiveDelta PositiveM
  have Small : Lambda≤q/2 := AbsoluteMomentDriftExponentLeHalf q Delta M
  have Parameter : 8*Lambda*M≤Delta*q^2 := AbsoluteMomentDriftExponentParameterBound q Delta M PositiveM
  have IntegrableExp (j : ℕ) : Integrable (fun ω => Real.exp (-Lambda*(X (j+1) ω-X j ω))) μ :=
    NegativeExponentialIntegrableOfAbsolute μ _ q Lambda PositiveLambda.le (by linarith)
      (IncrementIntegrable j).aemeasurable (AbsoluteIntegrable j)
  have Interior (j : ℕ) : ∀ᵐ ω ∂μ, a<X j ω ∧ X j ω<b →
      (μ[fun u => Real.exp (-Lambda*(X (j+1) u-X j u)) | F j]) ω≤1 := by
    have Bound := ConditionalNegativeExponentialQuadraticUpper μ (F j) (F.le j)
      (fun ω => X (j+1) ω-X j ω) q Lambda PositiveQ PositiveLambda.le Small
      (IncrementIntegrable j) (AbsoluteIntegrable j)
    have Error : (8*Lambda^2/q^2)*M≤Lambda*Delta := by
      have Scaled := mul_le_mul_of_nonneg_left Parameter PositiveLambda.le
      rw [show (8*Lambda^2/q^2)*M=(8*Lambda^2*M)/q^2 by ring]
      apply (div_le_iff₀ (sq_pos_of_pos PositiveQ)).mpr
      nlinarith
    filter_upwards [Bound,AbsoluteMoment j,Drift j] with ω Bound Moment Mean
    intro InRegion
    have MeanScale := mul_le_mul_of_nonneg_left (Mean InRegion) PositiveLambda.le
    have MomentScale := mul_le_mul_of_nonneg_left (Moment InRegion.1)
      (show 0≤8*Lambda^2/q^2 from div_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg Lambda)) (sq_nonneg q))
    linarith
  have Entrance (j : ℕ) : ∀ᵐ ω ∂μ, b≤X j ω →
      (μ[fun u => Real.exp (-Lambda*(X (j+1) u-X j u)) | F j]) ω≤M := by
    have Bound := condExp_mono (m := F j) (IntegrableExp j) (AbsoluteIntegrable j)
      (ae_of_all _ (fun ω => by
        apply Real.exp_le_exp.mpr
        have Negated := mul_le_mul_of_nonneg_left (neg_le_abs (X (j+1) ω-X j ω)) PositiveLambda.le
        have Scaled := mul_le_mul_of_nonneg_right (show Lambda≤q by linarith)
          (abs_nonneg (X (j+1) ω-X j ω))
        nlinarith))
    filter_upwards [Bound,AbsoluteMoment j] with ω Bound Moment
    intro Above
    exact Bound.trans (Moment (Ordered.trans_le Above))
  exact ExponentialBarrierHittingTailOfCondExp μ X F AdaptedX a b Lambda M Ordered
    PositiveLambda.le PositiveM.le InitiallyAbove Absorbing IntegrableExp Interior Entrance t

end
end ECTheoryLib.Tools.Drift
