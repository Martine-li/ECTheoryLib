import ECTheoryLib.Tools.Drift.ExponentialMomentNegative
import ECTheoryLib.Probability.Moments.GeometricTailMoment

/-!
# Negative drift with geometrically decaying absolute jumps

Drift is required in (a,b); tail control is required above a. Both state-event
and full-history interfaces retain a common finite range and target absorption.
The explicit finite-time bound does not itself claim the r-dependent asymptotic theorem.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Explicit exponent for geometric absolute-jump tails. -/
def GeometricJumpDriftExponent (eta Delta r : ℝ) : ℝ :=
  AbsoluteMomentDriftExponent (GeometricJumpMomentRadius eta) Delta (GeometricJumpMomentBound eta r)

theorem GeometricJumpDriftExponentPositive (eta Delta r : ℝ)
    (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r) :
    0<GeometricJumpDriftExponent eta Delta r :=
  AbsoluteMomentDriftExponentPositive _ _ _ (GeometricJumpMomentRadiusPositive eta PositiveEta)
    PositiveDelta (GeometricJumpMomentBoundPositive eta r PositiveEta PositiveR)

/-- Geometrically decaying probabilities of absolute jumps give an explicit
finite-time negative-drift bound. Drift is required only inside (a,b), while
the jump-tail bound is required at every state above a. -/
theorem GeometricJumpNegativeDriftTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω∈S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (JumpTail : ∀ t s, s∈S → a<s → 0<μ (StateEvent X t s) → ∀ j : ℕ,
      (cond μ (StateEvent X t s)) {ω | (j : ℝ)≤|X (t+1) ω-X t ω|} ≤
        ENNReal.ofReal (r/(1+eta)^j))
    (Drift : ∀ t s, s∈S → a<s → s<b → 0<μ (StateEvent X t s) →
      StateDrift μ X t s ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  apply ExponentialMomentNegativeDriftTail μ X S a b (GeometricJumpMomentRadius eta)
    Delta (GeometricJumpMomentBound eta r) Ordered (GeometricJumpMomentRadiusPositive eta PositiveEta)
    PositiveDelta (GeometricJumpMomentBoundPositive eta r PositiveEta PositiveR)
    Coordinates Values InitiallyAbove Absorbing _ Drift t
  intro j s Member Above Positive
  rw [EventConditionalExpectationEqCondIntegral]
  exact (AbsoluteExponentialMomentOfJumpTail (cond μ (StateEvent X j s))
    (fun ω => X (j+1) ω-X j ω) eta r PositiveEta PositiveR.le
    ((Coordinates (j+1)).sub (Coordinates j)) (JumpTail j s Member Above Positive)).2

/-- Full-history jump probabilities are expressed as conditional expectations
of event indicators. This avoids assuming a Markov property for the potential. -/
theorem GeometricJumpNegativeDriftTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r)
    (Values : ∀ t ω, X t ω∈S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (JumpTail : ∀ t (j : ℕ), ∀ᵐ ω ∂μ, a<X t ω →
      (μ[({u | (j : ℝ)≤|X (t+1) u-X t u|}).indicator (fun _ => (1 : ℝ)) | F t]) ω ≤
        r/(1+eta)^j)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  have Coordinates (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (Coordinates j) (ae_of_all _ (Values j))
  apply GeometricJumpNegativeDriftTail μ X S a b eta Delta r Ordered PositiveEta PositiveDelta PositiveR
    Coordinates Values InitiallyAbove Absorbing
  · intro k s _Member Above Positive j
    have EventMeasurable : MeasurableSet {ω | (j : ℝ)≤|X (k+1) ω-X k ω|} :=
      measurableSet_le measurable_const (((Coordinates (k+1)).sub (Coordinates k)).abs)
    have Bound := StateEventExpectationUpperBoundOfCondExpOn μ X F AdaptedX (fun s => a<s)
      (fun _ => r/(1+eta)^j) k
      (({ω | (j : ℝ)≤|X (k+1) ω-X k ω|}).indicator (fun _ => (1 : ℝ)))
      ((integrable_const (1 : ℝ)).indicator EventMeasurable) (JumpTail k j) s Above Positive
    rw [EventConditionalExpectationEqCondIntegral, integral_indicator_const _ EventMeasurable,
      smul_eq_mul, mul_one] at Bound
    have ConditionalProbability : IsProbabilityMeasure (cond μ (StateEvent X k s)) :=
      cond_isProbabilityMeasure Positive.ne'
    have BoundENN := ENNReal.ofReal_le_ofReal Bound
    rw [ofReal_measureReal] at BoundENN
    exact BoundENN
  · intro k s _Member Above Below Positive
    exact StateEventExpectationUpperBoundOfCondExpOn μ X F AdaptedX (fun s => a<s ∧ s<b)
      (fun _ => -Delta) k (fun ω => X k ω-X (k+1) ω)
      ((IntegrableX k).sub (IntegrableX (k+1))) (Drift k) s ⟨Above,Below⟩ Positive

end
end ECTheoryLib.Tools.Drift
