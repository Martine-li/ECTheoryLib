import ECTheoryLib.Tools.Drift.IntegrableExponentialMomentNegative
import ECTheoryLib.Tools.Drift.GeometricJumpNegative
import ECTheoryLib.Probability.Moments.ConditionalGeometricJumpMoment
import ECTheoryLib.Probability.HittingTimes.StoppedIncrement

/-!
# General full-history geometric-jump negative drift

No finite potential range or target absorption is assumed.
Conditional tails imply active-increment and exponential integrability.
Drift is an increase away from the target on the open interval (a,b).
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Complete-history geometric-jump negative drift without absorption or
a common finite range. The signed drift uses the increment localized to
X_t>a; jumps taken after entering the target need no integrability premise. -/
theorem GeometricJumpNegativeDriftTailOfActiveIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (OneLeR : 1≤r)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (JumpTail : ∀ t (j : ℕ), ∀ᵐ ω ∂μ, a<X t ω →
      (μ[({u | (j : ℝ)≤|X (t+1) u-X t u|}).indicator (fun _ => (1 : ℝ)) | F t]) ω≤r/(1+eta)^j)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      Delta≤(μ[ActiveIncrement X a t | F t]) ω) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤a) X
  let q := GeometricJumpMomentRadius eta
  let M := GeometricJumpMomentBound eta r
  have PositiveQ : 0<q := GeometricJumpMomentRadiusPositive eta PositiveEta
  have PositiveR : 0<r := lt_of_lt_of_le zero_lt_one OneLeR
  have PositiveM : 0<M := GeometricJumpMomentBoundPositive eta r PositiveEta PositiveR
  have Coordinates (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have ActiveObservable (j : ℕ) : Measurable (ActiveIncrement X a j) :=
    Measurable.ite (measurableSet_lt measurable_const (Coordinates j))
      ((Coordinates (j+1)).sub (Coordinates j)) measurable_const
  have ActiveTail (j k : ℕ) :
      (μ[({u | (k : ℝ)≤|ActiveIncrement X a j u|}).indicator (fun _ => (1 : ℝ)) | F j]) ≤ᵐ[μ]
        (fun _ => r/(1+eta)^k) :=
    ConditionalJumpTailOfRestriction μ (F j) (F.le j) {ω | a<X j ω}
      (measurableSet_lt measurable_const (AdaptedX j)) (fun ω => X (j+1) ω-X j ω)
      ((Coordinates (j+1)).sub (Coordinates j)) eta r PositiveEta OneLeR (JumpTail j) k
  have ActiveMoment (j : ℕ) : Integrable (fun ω => Real.exp (q*|ActiveIncrement X a j ω|)) μ ∧
      (μ[fun ω => Real.exp (q*|ActiveIncrement X a j ω|) | F j]) ≤ᵐ[μ] (fun _ => M) :=
    ConditionalAbsoluteExponentialMomentOfJumpTail μ (F j) (F.le j) (ActiveIncrement X a j)
      eta r PositiveEta PositiveR.le (ActiveObservable j) (ActiveTail j)
  have ActiveIntegrable (j : ℕ) : Integrable (ActiveIncrement X a j) μ :=
    IntegrableOfAbsoluteExponential μ (ActiveIncrement X a j) q PositiveQ
      (ActiveObservable j) (ActiveMoment j).1
  have StoppedMean (j : ℕ) : Integrable (fun ω => Y (j+1) ω-Y j ω) μ ∧
      (μ[fun ω => Y (j+1) ω-Y j ω | F j]) =ᵐ[μ]
        (fun ω => if a<Y j ω then (μ[ActiveIncrement X a j | F j]) ω else 0) :=
    StoppedIncrementConditional μ X F AdaptedX a j id (ActiveIntegrable j)
  have StoppedMoment (j : ℕ) : Integrable (fun ω => Real.exp (q*|Y (j+1) ω-Y j ω|)) μ ∧
      (μ[fun ω => Real.exp (q*|Y (j+1) ω-Y j ω|) | F j]) =ᵐ[μ]
        (fun ω => if a<Y j ω then
          (μ[fun u => Real.exp (q*|ActiveIncrement X a j u|) | F j]) ω else 1) := by
    simpa only [abs_zero,mul_zero,Real.exp_zero] using
      StoppedIncrementConditional μ X F AdaptedX a j (fun z => Real.exp (q*|z|)) (ActiveMoment j).1
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have Initial : ∀ᵐ ω ∂μ, b≤Y 0 ω := by
    simpa only [Y,StopAtFirstHitInitial] using InitiallyAbove
  have Absorbing (j : ℕ) : ∀ᵐ ω ∂μ, Y j ω≤a → Y (j+1) ω≤a :=
    ae_of_all _ (StopAtFirstHitAbsorbing (fun s : ℝ => s≤a) X j)
  have AbsoluteBound (j : ℕ) : ∀ᵐ ω ∂μ, a<Y j ω →
      (μ[fun u => Real.exp (q*|Y (j+1) u-Y j u|) | F j]) ω≤M := by
    filter_upwards [(StoppedMoment j).2,(ActiveMoment j).2] with ω Equal Bound
    intro Above
    rw [Equal,if_pos Above]
    exact Bound
  have MeanLower (j : ℕ) : ∀ᵐ ω ∂μ, a<Y j ω ∧ Y j ω<b →
      Delta≤(μ[fun u => Y (j+1) u-Y j u | F j]) ω := by
    filter_upwards [(StoppedMean j).2,Drift j] with ω Equal Bound
    intro InRegion
    rw [Equal,if_pos InRegion.1]
    have Original := StopAtFirstHitStepBefore (fun s : ℝ => s≤a) X j ω (not_le_of_gt InRegion.1)
    apply Bound
    rwa [← Original.1]
  have Bound := GeneralExponentialMomentNegativeDriftTail μ Y F AdaptedY a b q Delta M
    Ordered PositiveQ PositiveDelta PositiveM Initial Absorbing
    (fun j => (StoppedMean j).1) (fun j => (StoppedMoment j).1) AbsoluteBound MeanLower t
  rw [StopAtFirstHitEvent] at Bound
  exact Bound

/-- The usual unlocalized history-conditioned increment can be supplied
when it is integrable. No absorption or finite-range premise is introduced. -/
theorem GeometricJumpNegativeDriftTailOfIntegrableIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (OneLeR : 1≤r)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (IncrementIntegrable : ∀ t, Integrable (fun ω => X (t+1) ω-X t ω) μ)
    (JumpTail : ∀ t (j : ℕ), ∀ᵐ ω ∂μ, a<X t ω →
      (μ[({u | (j : ℝ)≤|X (t+1) u-X t u|}).indicator (fun _ => (1 : ℝ)) | F t]) ω≤r/(1+eta)^j)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      Delta≤(μ[fun u => X (t+1) u-X t u | F t]) ω) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  apply GeometricJumpNegativeDriftTailOfActiveIncrement μ X F AdaptedX a b eta Delta r
    Ordered PositiveEta PositiveDelta OneLeR InitiallyAbove JumpTail _ t
  intro j
  have Event : MeasurableSet[F j] {ω | a<X j ω} := measurableSet_lt measurable_const (AdaptedX j)
  have Conditional := condExp_indicator (m := F j) (IncrementIntegrable j) Event
  filter_upwards [Conditional,Drift j] with ω Equal Bound
  intro InRegion
  change Delta≤(μ[({u | a<X j u}).indicator (fun u => X (j+1) u-X j u) | F j]) ω
  rw [Equal,Set.indicator_of_mem (show ω∈{u | a<X j u} from InRegion.1)]
  exact Bound InRegion

end
end ECTheoryLib.Tools.Drift
