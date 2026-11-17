import ECTheoryLib.Tools.Drift.GeometricJumpNegative
import ECTheoryLib.Probability.HittingTimes.StoppedHitting

/-!
# Geometric-jump negative drift without target absorption

Stop the process using Mathlib, transfer full-history conditional bounds to
stopped-state events, and preserve the original first-hitting event.
A common pointwise finite potential range is still required.
-/


namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full-history geometric-jump negative drift without target absorption.
Mathlib stopping preserves the first hitting event; conditional bounds are
transferred on stopped-state events, rather than assumed to survive stopping. -/
theorem GeometricJumpNegativeDriftTailNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r)
    (Values : ∀ t ω, X t ω∈S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (JumpTail : ∀ t (j : ℕ), ∀ᵐ ω ∂μ, a<X t ω →
      (μ[({u | (j : ℝ)≤|X (t+1) u-X t u|}).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        r/(1+eta)^j)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤a) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have CoordinatesX (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have CoordinatesY (j : ℕ) : Measurable (Y j) := AdaptedY.measurable
  have ValuesY (j : ℕ) (ω : Ω) : Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values j ω
  have Initial : ∀ᵐ ω ∂μ, b≤Y 0 ω := by
    simpa only [Y, StopAtFirstHitInitial] using InitiallyAbove
  have Absorbing (j : ℕ) : ∀ᵐ ω ∂μ, Y j ω≤a → Y (j+1) ω≤a :=
    ae_of_all _ (StopAtFirstHitAbsorbing (fun s : ℝ => s≤a) X j)
  have StepBefore (j : ℕ) (ω : Ω) (Above : a<Y j ω) :
      Y j ω=X j ω ∧ Y (j+1) ω=X (j+1) ω :=
    StopAtFirstHitStepBefore _ X j ω (not_le_of_gt Above)
  have Agreement (j : ℕ) (s : ℝ) (Above : a<s) :
      ∀ᵐ ω ∂cond μ (StateEvent Y j s), Y j ω=X j ω ∧ Y (j+1) ω=X (j+1) ω := by
    have Current : ∀ᵐ ω ∂cond μ (StateEvent Y j s), Y j ω=s :=
      ae_cond_mem (StateEventMeasurable Y j s (CoordinatesY j))
    filter_upwards [Current] with ω Equal
    exact StepBefore j ω (by rwa [Equal])
  have TailY (k : ℕ) (s : ℝ) (_Member : s∈S) (Above : a<s)
      (Positive : 0<μ (StateEvent Y k s)) (j : ℕ) :
      (cond μ (StateEvent Y k s)) {ω | (j : ℝ)≤|Y (k+1) ω-Y k ω|} ≤
        ENNReal.ofReal (r/(1+eta)^j) := by
    have EventMeasurable : MeasurableSet {ω | (j : ℝ)≤|X (k+1) ω-X k ω|} :=
      measurableSet_le measurable_const (((CoordinatesX (k+1)).sub (CoordinatesX k)).abs)
    have HistoryBound : ∀ᵐ ω ∂μ, a<Y k ω →
        (μ[({u | (j : ℝ)≤|X (k+1) u-X k u|}).indicator (fun _ => (1 : ℝ)) | F k]) ω ≤
          r/(1+eta)^j := by
      filter_upwards [JumpTail k j] with ω Local
      intro InRegion
      exact Local (by rwa [← (StepBefore k ω InRegion).1])
    have Bound := StateEventExpectationUpperBoundOfCondExpOn μ Y F AdaptedY (fun s => a<s)
      (fun _ => r/(1+eta)^j) k
      (({ω | (j : ℝ)≤|X (k+1) ω-X k ω|}).indicator (fun _ => (1 : ℝ)))
      ((integrable_const (1 : ℝ)).indicator EventMeasurable) HistoryBound s Above Positive
    rw [EventConditionalExpectationEqCondIntegral, integral_indicator_const _ EventMeasurable,
      smul_eq_mul, mul_one] at Bound
    have ConditionalProbability : IsProbabilityMeasure (cond μ (StateEvent Y k s)) :=
      cond_isProbabilityMeasure Positive.ne'
    have BoundENN := ENNReal.ofReal_le_ofReal Bound
    rw [ofReal_measureReal] at BoundENN
    have EventEqual : (cond μ (StateEvent Y k s)) {ω | (j : ℝ)≤|Y (k+1) ω-Y k ω|} =
        (cond μ (StateEvent Y k s)) {ω | (j : ℝ)≤|X (k+1) ω-X k ω|} := by
      apply measure_congr
      filter_upwards [Agreement k s Above] with ω Equal
      change ((j : ℝ)≤|Y (k+1) ω-Y k ω|)=((j : ℝ)≤|X (k+1) ω-X k ω|)
      rw [Equal.1, Equal.2]
    rw [EventEqual]
    exact BoundENN
  have DriftY (k : ℕ) (s : ℝ) (_Member : s∈S) (Above : a<s) (Below : s<b)
      (Positive : 0<μ (StateEvent Y k s)) : StateDrift μ Y k s ≤ -Delta := by
    have IntegrableX (j : ℕ) : Integrable (X j) μ :=
      FiniteStateIntegrable μ (X j) S (CoordinatesX j) (ae_of_all _ (Values j))
    have HistoryBound : ∀ᵐ ω ∂μ, a<Y k ω ∧ Y k ω<b →
        (μ[fun ω => X k ω-X (k+1) ω | F k]) ω ≤ -Delta := by
      filter_upwards [Drift k] with ω Local
      intro InRegion
      exact Local (by rwa [← (StepBefore k ω InRegion.1).1])
    have Bound := StateEventExpectationUpperBoundOfCondExpOn μ Y F AdaptedY
      (fun s => a<s ∧ s<b) (fun _ => -Delta) k (fun ω => X k ω-X (k+1) ω)
      ((IntegrableX k).sub (IntegrableX (k+1))) HistoryBound s ⟨Above,Below⟩ Positive
    rw [EventConditionalExpectationEqCondIntegral] at Bound
    rw [StateDrift, EventConditionalExpectationEqCondIntegral]
    have IntegralEqual : (∫ ω, Y k ω-Y (k+1) ω ∂cond μ (StateEvent Y k s)) =
        ∫ ω, X k ω-X (k+1) ω ∂cond μ (StateEvent Y k s) := by
      apply integral_congr_ae
      filter_upwards [Agreement k s Above] with ω Equal
      rw [Equal.1, Equal.2]
    rw [IntegralEqual]
    exact Bound
  have Bound := GeometricJumpNegativeDriftTail μ Y S a b eta Delta r Ordered PositiveEta
    PositiveDelta PositiveR CoordinatesY ValuesY Initial Absorbing TailY DriftY t
  rw [StopAtFirstHitEvent] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift
