import ECTheoryLib.Tools.Drift.ExponentialBarrier
import ECTheoryLib.Probability.Moments.AbsoluteExponentialMoment
import ECTheoryLib.Probability.Processes.ConditionalDrift
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Negative drift under absolute-increment exponential moments

The interior drift and upper-region moment control remain separate.
A common pointwise finite range and an absorbing lower target are explicit.
The parameter is constructive; state-event and full-history versions are given.
Geometric jump-tail bounds are connected in GeometricJumpNegative.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A positive exponential parameter controlled by both the moment radius and
the drift-to-moment ratio. All three input parameters are explicit. -/
def AbsoluteMomentDriftExponent (q Delta M : ℝ) : ℝ :=
  min (q/2) (Delta*q^2/(8*M))

theorem AbsoluteMomentDriftExponentPositive (q Delta M : ℝ)
    (PositiveQ : 0<q) (PositiveDelta : 0<Delta) (PositiveM : 0<M) :
    0<AbsoluteMomentDriftExponent q Delta M := by
  apply lt_min
  · exact div_pos PositiveQ (by norm_num)
  · exact div_pos (mul_pos PositiveDelta (sq_pos_of_pos PositiveQ)) (mul_pos (by norm_num) PositiveM)

theorem AbsoluteMomentDriftExponentLeHalf (q Delta M : ℝ) :
    AbsoluteMomentDriftExponent q Delta M ≤ q/2 := min_le_left _ _

theorem AbsoluteMomentDriftExponentParameterBound (q Delta M : ℝ) (PositiveM : 0<M) :
    8*AbsoluteMomentDriftExponent q Delta M*M ≤ Delta*q^2 := by
  have Bound : AbsoluteMomentDriftExponent q Delta M ≤ Delta*q^2/(8*M) := min_le_right _ _
  have Multiplied := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<8) PositiveM)).mp Bound
  nlinarith

/-- Negative drift inside the interval and a uniform absolute-increment
exponential moment above the target imply a finite-time crossing bound.
No deterministic bound on individual jumps is required by this interface. -/
theorem ExponentialMomentNegativeDriftTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b q Delta M : ℝ)
    (Ordered : a<b) (PositiveQ : 0<q) (PositiveDelta : 0<Delta) (PositiveM : 0<M)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (AbsoluteMoment : ∀ t s, s∈S → a<s → 0<μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (q*|X (t+1) ω-X t ω|))
        (StateEvent X t s) ≤ M)
    (Drift : ∀ t s, s∈S → a<s → s<b → 0<μ (StateEvent X t s) →
      StateDrift μ X t s ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*M*Real.exp (-AbsoluteMomentDriftExponent q Delta M*(b-a))) := by
  let Lambda := AbsoluteMomentDriftExponent q Delta M
  have PositiveLambda : 0<Lambda := AbsoluteMomentDriftExponentPositive q Delta M PositiveQ PositiveDelta PositiveM
  have Small : Lambda≤q/2 := AbsoluteMomentDriftExponentLeHalf q Delta M
  have ParameterBound : 8*Lambda*M≤Delta*q^2 := AbsoluteMomentDriftExponentParameterBound q Delta M PositiveM
  have LocalMoment (j : ℕ) (s : ℝ) (Member : s∈S) (Above : a<s)
      (Positive : 0<μ (StateEvent X j s)) :
      (∫ ω, Real.exp (q*|X (j+1) ω-s|) ∂cond μ (StateEvent X j s)) ≤ M := by
    have Current : ∀ᵐ ω ∂cond μ (StateEvent X j s), X j ω=s :=
      ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have Bound := AbsoluteMoment j s Member Above Positive
    rw [EventConditionalExpectationEqCondIntegral] at Bound
    have Equal : (∫ ω, Real.exp (q*|X (j+1) ω-s|) ∂cond μ (StateEvent X j s)) =
        ∫ ω, Real.exp (q*|X (j+1) ω-X j ω|) ∂cond μ (StateEvent X j s) := by
      apply integral_congr_ae
      filter_upwards [Current] with ω Same
      rw [Same]
    rw [Equal]
    exact Bound
  have Interior (j : ℕ) (s : ℝ) (Member : s∈S) (Above : a<s) (Below : s<b)
      (Positive : 0<μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (j+1) ω-s)))
        (StateEvent X j s) ≤ 1 := by
    let ν := cond μ (StateEvent X j s)
    have Probability : IsProbabilityMeasure ν := cond_isProbabilityMeasure Positive.ne'
    have Current : ∀ᵐ ω ∂ν, X j ω=s := ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have MeanLower : Delta≤∫ ω, X (j+1) ω-s ∂ν := by
      have Decrease := Drift j s Member Above Below Positive
      rw [StateDrift, EventConditionalExpectationEqCondIntegral] at Decrease
      have Reverse : (∫ ω, X (j+1) ω-s ∂ν) = -(∫ ω, X j ω-X (j+1) ω ∂ν) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [Current] with ω Same
        rw [Same]
        ring
      rw [Reverse]
      linarith
    rw [EventConditionalExpectationEqCondIntegral]
    exact PositiveMeanNegativeMomentOfAbsMoment ν (fun ω => X (j+1) ω-s) q Delta M Lambda
      PositiveQ PositiveLambda.le Small
      (FiniteStateCompositionIntegrable ν (X (j+1)) S (fun v => v-s) (Coordinates (j+1)) (Values (j+1)))
      (FiniteStateCompositionIntegrable ν (X (j+1)) S (fun v => Real.exp (q*|v-s|))
        (Coordinates (j+1)) (Values (j+1)))
      MeanLower (LocalMoment j s Member Above Positive) ParameterBound
  have Entrance (j : ℕ) (s : ℝ) (Member : s∈S) (Above : b≤s)
      (Positive : 0<μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (j+1) ω-b)))
        (StateEvent X j s) ≤ M := by
    let ν := cond μ (StateEvent X j s)
    have Probability : IsProbabilityMeasure ν := cond_isProbabilityMeasure Positive.ne'
    have Comparison (v : ℝ) : Real.exp (-Lambda*(v-b)) ≤ Real.exp (q*|v-s|) := by
      have NegativeLe := neg_le_abs (v-s)
      have Scaled := mul_le_mul_of_nonneg_left NegativeLe PositiveLambda.le
      have Radius := mul_le_mul_of_nonneg_right (show Lambda≤q by linarith) (abs_nonneg (v-s))
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [EventConditionalExpectationEqCondIntegral]
    apply le_trans _ (LocalMoment j s Member (Ordered.trans_le Above) Positive)
    apply integral_mono_ae
      (FiniteStateCompositionIntegrable ν (X (j+1)) S (fun v => Real.exp (-Lambda*(v-b)))
        (Coordinates (j+1)) (Values (j+1)))
      (FiniteStateCompositionIntegrable ν (X (j+1)) S (fun v => Real.exp (q*|v-s|))
        (Coordinates (j+1)) (Values (j+1)))
    exact ae_of_all _ (fun ω => Comparison (X (j+1) ω))
  exact ExponentialBarrierHittingTail μ X S a b Lambda M Ordered PositiveLambda.le PositiveM.le
    Coordinates Values InitiallyAbove Absorbing Interior Entrance t

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full-history form with conditional absolute-increment exponential moments.
Adaptation places current-state events in the filtration; Mathlib supplies
the conditional-expectation integration identity. -/
theorem ExponentialMomentNegativeDriftTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a b q Delta M : ℝ)
    (Ordered : a<b) (PositiveQ : 0<q) (PositiveDelta : 0<Delta) (PositiveM : 0<M)
    (Values : ∀ t ω, X t ω∈S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (AbsoluteMoment : ∀ t, ∀ᵐ ω ∂μ, a<X t ω →
      (μ[fun ω => Real.exp (q*|X (t+1) ω-X t ω|) | F t]) ω ≤ M)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*M*Real.exp (-AbsoluteMomentDriftExponent q Delta M*(b-a))) := by
  classical
  have Coordinates (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (Coordinates j) (ae_of_all _ (Values j))
  have IntegrableMoment (j : ℕ) : Integrable (fun ω => Real.exp (q*|X (j+1) ω-X j ω|)) μ := by
    let R := (S.product S).image (fun p : ℝ×ℝ => Real.exp (q*|p.2-p.1|))
    apply FiniteStateIntegrable μ _ R
    · exact Real.measurable_exp.comp (((Coordinates (j+1)).sub (Coordinates j)).abs.const_mul q)
    · apply ae_of_all
      intro ω
      exact Finset.mem_image.mpr ⟨(X j ω,X (j+1) ω), Finset.mem_product.mpr ⟨Values j ω,Values (j+1) ω⟩,rfl⟩
  apply ExponentialMomentNegativeDriftTail μ X S a b q Delta M Ordered PositiveQ PositiveDelta PositiveM
    Coordinates Values InitiallyAbove Absorbing
  · intro j s _Member Above Positive
    exact StateEventExpectationUpperBoundOfCondExpOn μ X F AdaptedX (fun s => a<s) (fun _ => M)
      j (fun ω => Real.exp (q*|X (j+1) ω-X j ω|)) (IntegrableMoment j)
      (AbsoluteMoment j) s Above Positive
  · intro j s _Member Above Below Positive
    exact StateEventExpectationUpperBoundOfCondExpOn μ X F AdaptedX (fun s => a<s ∧ s<b)
      (fun _ => -Delta) j (fun ω => X j ω-X (j+1) ω)
      ((IntegrableX j).sub (IntegrableX (j+1))) (Drift j) s ⟨Above,Below⟩ Positive

end
end ECTheoryLib.Tools.Drift
