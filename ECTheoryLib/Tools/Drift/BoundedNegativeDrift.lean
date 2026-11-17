import ECTheoryLib.Tools.Drift.ExponentialBarrier
import ECTheoryLib.Probability.Moments.BoundedExponentialMoment
import ECTheoryLib.Probability.Processes.ConditionalDrift

/-!
# Bounded-jump negative drift across an interval

Negative drift is required only inside (a,b), whereas jump control extends
over the upper entrance region. The lower target is explicitly absorbing.
State-event and full-filtration versions retain pointwise common finite range.
An explicit exponential horizon is included. This is a bounded-jump special
case, not the general exponentially decaying jump-tail theorem.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Negative drift is only required inside (a,b); bounded absolute jumps are
required above a, including entrances from the upper side. The lower target
is absorbing. The bound is explicit for each finite time. -/
theorem BoundedJumpNegativeDriftTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b c Delta : ℝ)
    (Ordered : a<b) (PositiveC : 0<c) (PositiveDelta : 0<Delta)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b ≤ X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (Jumps : ∀ t, ∀ᵐ ω ∂μ, a<X t ω → |X (t+1) ω-X t ω| ≤ c)
    (Drift : ∀ t s, s ∈ S → a<s → s<b → 0 < μ (StateEvent X t s) →
      StateDrift μ X t s ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*Real.exp (-(Delta/c^2)*((b-a)-c))) := by
  let Lambda := Delta/c^2
  have NonnegativeLambda : 0≤Lambda := div_nonneg PositiveDelta.le (sq_nonneg c)
  have Small : Lambda*c^2 ≤ 2*Delta := by
    dsimp [Lambda]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 PositiveC.ne')]
    linarith
  have Interior (j : ℕ) (s : ℝ) (Member : s∈S) (Above : a<s) (Below : s<b)
      (Positive : 0<μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (j+1) ω-s)))
        (StateEvent X j s) ≤ 1 := by
    let ν := cond μ (StateEvent X j s)
    have Probability : IsProbabilityMeasure ν := cond_isProbabilityMeasure Positive.ne'
    have Current : ∀ᵐ ω ∂ν, X j ω=s := ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have Bounded : ∀ᵐ ω ∂ν, X (j+1) ω-s ∈ Set.Icc (-c) c := by
      filter_upwards [Current, cond_absolutelyContinuous.ae_le (Jumps j)] with ω Equal Jump
      have Bound := Jump (by rw [Equal]; exact Above)
      rw [Equal] at Bound
      exact abs_le.mp Bound
    have MeanLower : Delta ≤ ∫ ω, X (j+1) ω-s ∂ν := by
      have Decrease := Drift j s Member Above Below Positive
      rw [StateDrift, EventConditionalExpectationEqCondIntegral] at Decrease
      have Reverse : (∫ ω, X (j+1) ω-s ∂ν) = -(∫ ω, X j ω-X (j+1) ω ∂ν) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [Current] with ω Equal
        rw [Equal]
        ring
      rw [Reverse]
      linarith
    rw [EventConditionalExpectationEqCondIntegral]
    exact BoundedPositiveMeanNegativeMoment ν (fun ω => X (j+1) ω-s) c Delta Lambda
      ((Coordinates (j+1)).sub_const s).aemeasurable Bounded MeanLower NonnegativeLambda Small
  have Entrance (j : ℕ) (s : ℝ) (_Member : s∈S) (Above : b≤s)
      (Positive : 0<μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (j+1) ω-b)))
        (StateEvent X j s) ≤ Real.exp (Lambda*c) := by
    let ν := cond μ (StateEvent X j s)
    have Probability : IsProbabilityMeasure ν := cond_isProbabilityMeasure Positive.ne'
    have Current : ∀ᵐ ω ∂ν, X j ω=s := ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have Pointwise : ∀ᵐ ω ∂ν, Real.exp (-Lambda*(X (j+1) ω-b)) ≤ Real.exp (Lambda*c) := by
      filter_upwards [Current, cond_absolutelyContinuous.ae_le (Jumps j)] with ω Equal Jump
      have Bound := Jump (by rw [Equal]; exact Ordered.trans_le Above)
      rw [Equal] at Bound
      have Lower := (abs_le.mp Bound).1
      apply Real.exp_le_exp.mpr
      nlinarith
    have IntegrableNext := FiniteStateCompositionIntegrable ν (X (j+1)) S
      (fun v => Real.exp (-Lambda*(v-b))) (Coordinates (j+1)) (Values (j+1))
    have Bound := integral_mono_ae IntegrableNext (integrable_const (Real.exp (Lambda*c))) Pointwise
    rw [integral_const, probReal_univ, one_smul] at Bound
    rw [EventConditionalExpectationEqCondIntegral]
    exact Bound
  have Bound := ExponentialBarrierHittingTail μ X S a b Lambda (Real.exp (Lambda*c)) Ordered
    NonnegativeLambda (Real.exp_pos _).le Coordinates Values InitiallyAbove Absorbing Interior Entrance t
  rw [mul_assoc, ← Real.exp_add] at Bound
  have Exponent : Lambda*c+-Lambda*(b-a)= -Lambda*((b-a)-c) := by ring
  rw [Exponent] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full-filtration formulation, with ordinary bounded-jump negative drift
restricted to the crossing interval. Finite range supplies integrability. -/
theorem BoundedJumpNegativeDriftTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a b c Delta : ℝ)
    (Ordered : a<b) (PositiveC : 0<c) (PositiveDelta : 0<Delta)
    (Values : ∀ t ω, X t ω ∈ S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b ≤ X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (Jumps : ∀ t, ∀ᵐ ω ∂μ, a<X t ω → |X (t+1) ω-X t ω| ≤ c)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*Real.exp (-(Delta/c^2)*((b-a)-c))) := by
  have Coordinates (j : ℕ) : Measurable (X j) := AdaptedX.measurable
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S (Coordinates j) (ae_of_all _ (Values j))
  apply BoundedJumpNegativeDriftTail μ X S a b c Delta Ordered PositiveC PositiveDelta
    Coordinates Values InitiallyAbove Absorbing Jumps
  intro j s _Member Above Below Positive
  exact StateEventExpectationUpperBoundOfCondExpOn μ X F AdaptedX
    (fun s => a<s ∧ s<b) (fun _ => -Delta) j (fun ω => X j ω-X (j+1) ω)
    ((IntegrableX j).sub (IntegrableX (j+1))) (Drift j) s ⟨Above,Below⟩ Positive

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- An interval at least four jumps wide is crossed with exponentially small
probability even over an exponential time horizon. Constants are explicit. -/
theorem BoundedJumpNegativeDriftExponentialHorizon (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b c Delta : ℝ)
    (Ordered : a<b) (PositiveC : 0<c) (PositiveDelta : 0<Delta)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b ≤ X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (Jumps : ∀ t, ∀ᵐ ω ∂μ, a<X t ω → |X (t+1) ω-X t ω| ≤ c)
    (Drift : ∀ t s, s ∈ S → a<s → s<b → 0 < μ (StateEvent X t s) →
      StateDrift μ X t s ≤ -Delta)
    (Wide : 4*c ≤ b-a) (t : ℕ)
    (Horizon : (t : ℝ) ≤ Real.exp ((Delta/c^2)*(b-a)/2)) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal (Real.exp (-(Delta/c^2)*(b-a)/4)) := by
  have Bound := BoundedJumpNegativeDriftTail μ X S a b c Delta Ordered PositiveC PositiveDelta
    Coordinates Values InitiallyAbove Absorbing Jumps Drift t
  apply Bound.trans
  apply ENNReal.ofReal_le_ofReal
  have Nonnegative : 0 ≤ Delta/c^2 := div_nonneg PositiveDelta.le (sq_nonneg c)
  calc
    _ ≤ Real.exp ((Delta/c^2)*(b-a)/2)*Real.exp (-(Delta/c^2)*((b-a)-c)) :=
      mul_le_mul_of_nonneg_right Horizon (Real.exp_pos _).le
    _ = Real.exp ((Delta/c^2)*(b-a)/2-(Delta/c^2)*((b-a)-c)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have Scaled := mul_le_mul_of_nonneg_left Wide Nonnegative
      nlinarith

end
end ECTheoryLib.Tools.Drift
