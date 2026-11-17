import ECTheoryLib.Probability.HittingTimes.HittingTime
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.ConditionalProbability

/-!
# Scalar processes, event-conditioned drift, and first hitting zero

A process `X : Nat → Ω → ℝ` records its value at time `t` on a complete sample
`ω`. No Markov property is assumed. Event-conditioned expectation is the integral
over the event divided by its probability. Its probabilistic interpretation
requires positive event probability and integrability on that event. Lean's total
division assigns a formal value even to null events; drift theorems exclude those
events explicitly. Hitting-time expectations use extended nonnegative integrals.
-/

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued expectation, with the usual probabilistic interpretation when
`Y` is integrable. Finite measurable ranges provide this in the drift interfaces. -/
def ExpectedValue (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, Y ω ∂μ

/-- The event average `(∫_A Y dμ) / Pr(A)`. Its probabilistic interpretation
requires positive event probability and integrability on the event. -/
def EventConditionalExpectation (μ : Measure Ω) (Y : Ω → ℝ)
    (A : Set Ω) : ℝ :=
  (∫ ω in A, Y ω ∂μ) / (μ A).toReal

/-- Event-conditioned expectation equals mathlib's set average, including the
formal null-event value; positive probability is still required for conditioning. -/
theorem EventConditionalExpectationEqAverage (μ : Measure Ω) (Y : Ω → ℝ)
    (A : Set Ω) :
    EventConditionalExpectation μ Y A = ⨍ ω in A, Y ω ∂μ := by
  rw [setAverage_eq]
  unfold EventConditionalExpectation
  rw [measureReal_def, smul_eq_mul, div_eq_inv_mul]

/-- Event averaging equals integration under mathlib's conditional measure.
This bridge enables reuse of theorems about `ProbabilityTheory.cond`. -/
theorem EventConditionalExpectationEqCondIntegral (μ : Measure Ω) (Y : Ω → ℝ)
    (A : Set Ω) :
    EventConditionalExpectation μ Y A = ∫ ω, Y ω ∂ProbabilityTheory.cond μ A := by
  rw [EventConditionalExpectationEqAverage, setAverage_eq']
  rfl

/-- The event that the process has value `s` at time `t`. -/
def StateEvent (X : Nat → Ω → ℝ) (t : Nat) (s : ℝ) : Set Ω :=
  {ω | X t ω = s}

/-- Expected signed decrease conditioned on the current potential-level event.
The event must have positive probability when this is interpreted as conditional drift. -/
def StateDrift (μ : Measure Ω) (X : Nat → Ω → ℝ)
    (t : Nat) (s : ℝ) : ℝ :=
  EventConditionalExpectation μ
    (fun ω => X t ω - X (t + 1) ω) (StateEvent X t s)

/-- The first time the scalar process reaches zero, with infinity for no hit. -/
def ZeroHittingTime (X : Nat → Ω → ℝ) (ω : Ω) : WithTop Nat :=
  FirstHittingTime (fun s : ℝ => s = 0) (fun t => X t ω)

/-- Extended expected time to reach zero, preserving infinite values. -/
def ExpectedZeroHittingTime (μ : Measure Ω) (X : Nat → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENat.toENNReal (ZeroHittingTime X ω) ∂μ

/-- Zero is absorbing almost surely at each step; exceptional null samples are allowed. -/
def ZeroIsAbsorbing (μ : Measure Ω) (X : Nat → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂μ, X t ω = 0 → X (t + 1) ω = 0

/-- A measurable coordinate has measurable potential-level events. -/
theorem StateEventMeasurable (X : Nat → Ω → ℝ) (t : Nat) (s : ℝ)
    (CoordinateMeasurable : Measurable (X t)) :
    MeasurableSet (StateEvent X t s) := by
  have SingletonMeasurable : MeasurableSet ({s} : Set ℝ) := by
    exact measurableSet_singleton s
  change MeasurableSet ((X t) ⁻¹' {s})
  exact CoordinateMeasurable SingletonMeasurable

/-- The first zero of a measurable process is measurable without a Markov assumption. -/
theorem ZeroHittingTimeMeasurable (X : Nat → Ω → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) :
    Measurable (ZeroHittingTime X) := by
  have ZeroMeasurable : MeasurableSet ({0} : Set ℝ) := by
    exact measurableSet_singleton 0
  exact FirstHittingTimeProcessMeasurable (fun s : ℝ => s = 0) X
    ZeroMeasurable CoordinatesMeasurable

/-- The extended nonnegative integrand defining expected zero-hitting time is measurable. -/
theorem ZeroHittingTimeValueMeasurable (X : Nat → Ω → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) :
    Measurable (fun ω => ENat.toENNReal (ZeroHittingTime X ω)) := by
  have ConversionMeasurable :
      Measurable (fun t : WithTop Nat => ENat.toENNReal t) := by
    exact measurable_of_countable _
  exact ConversionMeasurable.comp (ZeroHittingTimeMeasurable X CoordinatesMeasurable)

/-- A measurable real variable with an almost-sure finite range is integrable.
This ensures initial means in applications are ordinary expectations, rather than
the default value of a nonintegrable Bochner integral. -/
theorem FiniteStateIntegrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (S : Finset ℝ)
    (VariableMeasurable : Measurable Y)
    (ValuesInS : ∀ᵐ ω ∂μ, Y ω ∈ S) :
    Integrable Y μ := by
  classical
  -- The sum of norms over the finite range bounds every possible value.
  have NormBound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ ∑ s ∈ S, ‖s‖ := by
    filter_upwards [ValuesInS] with ω ValueInS
    apply Finset.single_le_sum
    · intro s _InS
      exact norm_nonneg s
    · exact ValueInS
  have VariableAEStronglyMeasurable : AEStronglyMeasurable Y μ := by
    exact VariableMeasurable.aestronglyMeasurable
  exact Integrable.of_bound VariableAEStronglyMeasurable (∑ s ∈ S, ‖s‖) NormBound

end

end ECTheoryLib.Probability
