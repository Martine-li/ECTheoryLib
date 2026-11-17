import ECTheoryLib.Probability.Processes.ScalarProcess
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Expectation bounds for finite nonnegative ranges

A variable in a fixed finite nonnegative set contributes only on its nonzero
event. A uniform value bound controls its expectation by the probability of
that event. Thus vanishing nonzero probabilities imply vanishing expectations.
No Markov property or stopping-time premise is required.
-/

namespace ECTheoryLib.Probability

open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A variable with finite nonnegative range has nonnegative real expectation. -/
theorem FiniteStateExpectedValueNonneg (μ : Measure Ω)
    (Y : Ω → ℝ) (S : Finset ℝ)
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ ω, Y ω ∈ S) :
    0 ≤ ExpectedValue μ Y := by
  have VariableNonnegative : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact StatesNonnegative (Y ω) (ValuesInS ω)
  unfold ExpectedValue
  exact integral_nonneg VariableNonnegative

/-- Bound expectation by a uniform norm bound times the nonzero-event
probability. Finite measure, measurability, and finite range ensure integrability. -/
theorem FiniteStateExpectedValueLeNonzeroProbability
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (S : Finset ℝ)
    (VariableMeasurable : Measurable Y)
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ ω, Y ω ∈ S) :
    ExpectedValue μ Y ≤
      (∑ s ∈ S, ‖s‖) * (μ {ω | Y ω ≠ 0}).toReal := by
  classical
  let NonzeroEvent : Set Ω := {ω | Y ω ≠ 0}
  let StateBound : ℝ := ∑ s ∈ S, ‖s‖
  have NonzeroEventMeasurable : MeasurableSet NonzeroEvent := by
    have ZeroEventMeasurable : MeasurableSet {ω | Y ω = 0} := by
      exact VariableMeasurable (measurableSet_singleton 0)
    exact ZeroEventMeasurable.compl
  have VariableIntegrable : Integrable Y μ := by
    apply FiniteStateIntegrable μ Y S VariableMeasurable
    exact ae_of_all μ ValuesInS
  have VariableLeStateBound : ∀ ω, Y ω ≤ StateBound := by
    intro ω
    have VariableNonnegative : 0 ≤ Y ω := by
      exact StatesNonnegative (Y ω) (ValuesInS ω)
    have VariableNormLeStateBound : ‖Y ω‖ ≤ StateBound := by
      apply Finset.single_le_sum
      · intro s _InS
        exact norm_nonneg s
      · exact ValuesInS ω
    rw [Real.norm_of_nonneg VariableNonnegative] at VariableNormLeStateBound
    exact VariableNormLeStateBound
  -- Off the nonzero event the variable vanishes; on it the uniform bound applies.
  have ComparisonIntegrable :
      Integrable (NonzeroEvent.indicator (fun _ : Ω => StateBound)) μ := by
    exact (integrable_const StateBound).indicator NonzeroEventMeasurable
  have VariableLeComparison :
      ∀ ω, Y ω ≤ NonzeroEvent.indicator (fun _ : Ω => StateBound) ω := by
    intro ω
    by_cases NonzeroValue : Y ω ≠ 0
    · have InNonzeroEvent : ω ∈ NonzeroEvent := NonzeroValue
      rw [Set.indicator_of_mem InNonzeroEvent]
      exact VariableLeStateBound ω
    · have ZeroValue : Y ω = 0 := by
        exact not_not.mp NonzeroValue
      have OutsideNonzeroEvent : ω ∉ NonzeroEvent := NonzeroValue
      rw [Set.indicator_of_notMem OutsideNonzeroEvent, ZeroValue]
  have IntegralComparison :
      (∫ ω, Y ω ∂μ) ≤
        ∫ ω, NonzeroEvent.indicator (fun _ : Ω => StateBound) ω ∂μ := by
    exact integral_mono VariableIntegrable ComparisonIntegrable VariableLeComparison
  have ComparisonIntegral :
      (∫ ω, NonzeroEvent.indicator (fun _ : Ω => StateBound) ω ∂μ) =
        StateBound * (μ NonzeroEvent).toReal := by
    rw [integral_indicator_const StateBound NonzeroEventMeasurable]
    change (μ NonzeroEvent).toReal * StateBound = StateBound * (μ NonzeroEvent).toReal
    exact mul_comm _ _
  unfold ExpectedValue
  calc
    (∫ ω, Y ω ∂μ) ≤
        ∫ ω, NonzeroEvent.indicator (fun _ : Ω => StateBound) ω ∂μ := IntegralComparison
    _ = StateBound * (μ NonzeroEvent).toReal := ComparisonIntegral

/-- For a sequence with a common finite nonnegative range, vanishing
nonzero-event probabilities imply vanishing expectations. -/
theorem FiniteStateExpectedValueTendstoZero
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (NonzeroProbabilityTendstoZero :
      Tendsto (fun t => (μ {ω | X t ω ≠ 0}).toReal) atTop (nhds 0)) :
    Tendsto (fun t => ExpectedValue μ (X t)) atTop (nhds 0) := by
  have ExpectationNonnegative : ∀ t, 0 ≤ ExpectedValue μ (X t) := by
    intro t
    exact FiniteStateExpectedValueNonneg μ (X t) S StatesNonnegative (ValuesInS t)
  have ExpectationLeBound : ∀ t, ExpectedValue μ (X t) ≤
      (∑ s ∈ S, ‖s‖) * (μ {ω | X t ω ≠ 0}).toReal := by
    intro t
    exact FiniteStateExpectedValueLeNonzeroProbability
      μ (X t) S (CoordinatesMeasurable t) StatesNonnegative (ValuesInS t)
  have BoundTendstoZero : Tendsto
      (fun t => (∑ s ∈ S, ‖s‖) * (μ {ω | X t ω ≠ 0}).toReal) atTop (nhds 0) := by
    have ProductTendstoZero :=
      NonzeroProbabilityTendstoZero.const_mul (∑ s ∈ S, ‖s‖)
    rw [mul_zero] at ProductTendstoZero
    exact ProductTendstoZero
  exact squeeze_zero ExpectationNonnegative ExpectationLeBound BoundTendstoZero

end

end ECTheoryLib.Probability
