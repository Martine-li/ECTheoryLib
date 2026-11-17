import ECTheoryLib.Probability.Processes.ScalarProcess

/-!
# From finite-state conditional drift to unconditional progress

At each time, distinct potential-level events are disjoint and the finite range
makes them a partition. Null-event integrals vanish; absorption makes the
integral of the decrease on the zero-state event vanish as well.
These finite-partition identities require no Markov property.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Distinct potential-level events at the same time are disjoint. -/
theorem StateEventsPairwiseDisjoint (X : Nat → Ω → ℝ) (t : Nat) (S : Finset ℝ) :
    (↑S : Set ℝ).PairwiseDisjoint (StateEvent X t) := by
  intro s _InS r _InS DifferentStates
  apply Set.disjoint_left.mpr
  intro ω InFirst InSecond
  have FirstValue : X t ω = s := InFirst
  have SecondValue : X t ω = r := InSecond
  exact DifferentStates (FirstValue.symm.trans SecondValue)

omit [MeasurableSpace Ω] in
/-- A finite pointwise range makes the state events cover the sample space. -/
theorem StateEventsUnion (X : Nat → Ω → ℝ) (t : Nat) (S : Finset ℝ)
    (ValuesInS : ∀ ω, X t ω ∈ S) :
    (⋃ s ∈ S, StateEvent X t s) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  apply Set.mem_iUnion.mpr
  refine ⟨X t ω, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨ValuesInS ω, ?_⟩
  change X t ω = X t ω
  rfl

omit [MeasurableSpace Ω] in
/-- The union of the nonzero state events is exactly the nonzero-potential event. -/
theorem NonzeroStateEventsUnion (X : Nat → Ω → ℝ) (t : Nat) (S : Finset ℝ)
    (ValuesInS : ∀ ω, X t ω ∈ S) :
    (⋃ s ∈ S.erase 0, StateEvent X t s) = {ω | X t ω ≠ 0} := by
  classical
  apply Set.ext
  intro ω
  constructor
  · intro InUnion
    obtain ⟨s, InUnionAtState⟩ := Set.mem_iUnion.mp InUnion
    obtain ⟨InErasedSet, InStateEvent⟩ := Set.mem_iUnion.mp InUnionAtState
    have StateNonzero : s ≠ 0 := (Finset.mem_erase.mp InErasedSet).1
    have CurrentValue : X t ω = s := InStateEvent
    change X t ω ≠ 0
    rw [CurrentValue]
    exact StateNonzero
  · intro CurrentNonzero
    apply Set.mem_iUnion.mpr
    refine ⟨X t ω, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.mem_erase.mpr ⟨CurrentNonzero, ValuesInS ω⟩, ?_⟩
    change X t ω = X t ω
    rfl

/-- Integrate over the finite partition into state events: a finite
form of total expectation. -/
theorem FiniteStateIntegralPartition (μ : Measure Ω)
    (X : Nat → Ω → ℝ) (t : Nat) (S : Finset ℝ) (Y : Ω → ℝ)
    (CoordinateMeasurable : Measurable (X t))
    (ValuesInS : ∀ ω, X t ω ∈ S)
    (VariableIntegrable : Integrable Y μ) :
    (∫ ω, Y ω ∂μ) = ∑ s ∈ S, ∫ ω in StateEvent X t s, Y ω ∂μ := by
  have EventsMeasurable : ∀ s ∈ S, MeasurableSet (StateEvent X t s) := by
    intro s _InS
    exact StateEventMeasurable X t s CoordinateMeasurable
  have IntegrableOnEvents : ∀ s ∈ S, IntegrableOn Y (StateEvent X t s) μ := by
    intro s _InS
    exact VariableIntegrable.integrableOn
  have IntegralOfUnion :
      (∫ ω in ⋃ s ∈ S, StateEvent X t s, Y ω ∂μ) =
        ∑ s ∈ S, ∫ ω in StateEvent X t s, Y ω ∂μ := by
    exact integral_biUnion_finset S EventsMeasurable
      (StateEventsPairwiseDisjoint X t S) IntegrableOnEvents
  rw [StateEventsUnion X t S ValuesInS, setIntegral_univ] at IntegralOfUnion
  exact IntegralOfUnion

/-- Absorption makes the integrated one-step decrease on the zero-state event zero. -/
theorem ZeroStateDecreaseIntegral (μ : Measure Ω) (X : Nat → Ω → ℝ) (t : Nat)
    (CoordinateMeasurable : Measurable (X t))
    (ZeroAbsorbing : ZeroIsAbsorbing μ X) :
    (∫ ω in StateEvent X t 0, X t ω - X (t + 1) ω ∂μ) = 0 := by
  have ZeroEventMeasurable : MeasurableSet (StateEvent X t 0) := by
    exact StateEventMeasurable X t 0 CoordinateMeasurable
  have DecreaseZeroOnEvent :
      ∀ᵐ ω ∂μ, ω ∈ StateEvent X t 0 → X t ω - X (t + 1) ω = 0 := by
    filter_upwards [ZeroAbsorbing t] with ω AbsorbingAtSample
    intro InZeroEvent
    have CurrentZero : X t ω = 0 := InZeroEvent
    have NextZero : X (t + 1) ω = 0 := AbsorbingAtSample CurrentZero
    rw [CurrentZero, NextZero, sub_self]
  have RestrictedDecreaseZero :
      (fun ω => X t ω - X (t + 1) ω) =ᵐ[μ.restrict (StateEvent X t 0)] 0 := by
    exact (ae_restrict_iff' ZeroEventMeasurable).mpr DecreaseZeroOnEvent
  exact integral_eq_zero_of_ae RestrictedDecreaseZero

/-- Unconditional expected decrease equals the sum of integrated decreases
on the nonzero state events. -/
theorem FiniteStateExpectedDecrease (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (t : Nat)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X) :
    ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) =
      ∑ s ∈ S.erase 0, ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
  classical
  have CurrentIntegrable : Integrable (X t) μ := by
    exact FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t)
      (Filter.Eventually.of_forall (ValuesInS t))
  have NextIntegrable : Integrable (X (t + 1)) μ := by
    exact FiniteStateIntegrable μ (X (t + 1)) S (CoordinatesMeasurable (t + 1))
      (Filter.Eventually.of_forall (ValuesInS (t + 1)))
  have DecreaseIntegrable : Integrable (fun ω => X t ω - X (t + 1) ω) μ := by
    exact CurrentIntegrable.sub NextIntegrable
  have DecreasePartition :
      (∫ ω, X t ω - X (t + 1) ω ∂μ) =
        ∑ s ∈ S, ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
    exact FiniteStateIntegralPartition μ X t S _ (CoordinatesMeasurable t)
      (ValuesInS t) DecreaseIntegrable
  have DropZeroTerm :
      (∑ s ∈ S.erase 0, ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) =
        ∑ s ∈ S, ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
    exact Finset.sum_erase S (ZeroStateDecreaseIntegral μ X t
      (CoordinatesMeasurable t) ZeroAbsorbing)
  unfold ExpectedValue
  rw [← integral_sub CurrentIntegrable NextIntegrable, DecreasePartition, ← DropZeroTerm]

/-- Nonzero-potential probability is the sum of the nonzero state-event probabilities. -/
theorem FiniteStateNonzeroProbability (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (t : Nat)
    (CoordinateMeasurable : Measurable (X t))
    (ValuesInS : ∀ ω, X t ω ∈ S) :
    (μ {ω | X t ω ≠ 0}).toReal =
      ∑ s ∈ S.erase 0, (μ (StateEvent X t s)).toReal := by
  have EventsMeasurable :
      ∀ s ∈ S.erase 0, MeasurableSet (StateEvent X t s) := by
    intro s _InS
    exact StateEventMeasurable X t s CoordinateMeasurable
  rw [← NonzeroStateEventsUnion X t S ValuesInS]
  rw [measure_biUnion_finset (StateEventsPairwiseDisjoint X t (S.erase 0)) EventsMeasurable]
  exact ENNReal.toReal_sum (fun s _InS => measure_ne_top μ (StateEvent X t s))

/-- Combine conditional drift lower bounds into an unconditional progress
lower bound. This local finite-measure step needs neither nonnegative potential
nor positive Delta, and makes no hitting-time assertion. -/
theorem StateDriftLowerBoundToExpectedDecrease (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (StateDriftLowerBound : ∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta ≤ StateDrift μ X t s)
    (t : Nat) :
    Delta * (μ {ω | X t ω ≠ 0}).toReal ≤
      ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) := by
  classical
  -- Null events need no conditional-drift hypothesis: their probability and integral are zero.
  have StateContributionLowerBound : ∀ s ∈ S.erase 0,
      Delta * (μ (StateEvent X t s)).toReal ≤
        ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
    intro s InErasedSet
    have StateInS : s ∈ S := (Finset.mem_erase.mp InErasedSet).2
    have StateNonzero : s ≠ 0 := (Finset.mem_erase.mp InErasedSet).1
    by_cases EventNull : μ (StateEvent X t s) = 0
    · have RestrictedMeasureZero : μ.restrict (StateEvent X t s) = 0 := by
        exact Measure.restrict_eq_zero.mpr EventNull
      rw [EventNull, ENNReal.toReal_zero, mul_zero, RestrictedMeasureZero, integral_zero_measure]
    · have EventPositive : 0 < μ (StateEvent X t s) := by
        exact bot_lt_iff_ne_bot.mpr EventNull
      have RealProbabilityPositive : 0 < (μ (StateEvent X t s)).toReal := by
        exact ENNReal.toReal_pos EventNull (measure_ne_top μ (StateEvent X t s))
      have ConditionalLowerBound : Delta ≤
          (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) /
            (μ (StateEvent X t s)).toReal := by
        exact StateDriftLowerBound t s StateInS StateNonzero EventPositive
      exact (le_div_iff₀ RealProbabilityPositive).mp ConditionalLowerBound
  rw [FiniteStateNonzeroProbability μ X S t (CoordinatesMeasurable t) (ValuesInS t)]
  rw [Finset.mul_sum]
  rw [FiniteStateExpectedDecrease μ X S t CoordinatesMeasurable ValuesInS ZeroAbsorbing]
  exact Finset.sum_le_sum StateContributionLowerBound

/-- Combine conditional drift upper bounds into an unconditional progress
upper bound, using the same finite partition as the lower-bound direction. -/
theorem StateDriftUpperBoundToExpectedDecrease (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (StateDriftUpperBound : ∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ Delta)
    (t : Nat) :
    ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) ≤
      Delta * (μ {ω | X t ω ≠ 0}).toReal := by
  classical
  have StateContributionUpperBound : ∀ s ∈ S.erase 0,
      (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) ≤
        Delta * (μ (StateEvent X t s)).toReal := by
    intro s InErasedSet
    have StateInS : s ∈ S := (Finset.mem_erase.mp InErasedSet).2
    have StateNonzero : s ≠ 0 := (Finset.mem_erase.mp InErasedSet).1
    by_cases EventNull : μ (StateEvent X t s) = 0
    · have RestrictedMeasureZero : μ.restrict (StateEvent X t s) = 0 := by
        exact Measure.restrict_eq_zero.mpr EventNull
      rw [EventNull, ENNReal.toReal_zero, mul_zero, RestrictedMeasureZero, integral_zero_measure]
    · have EventPositive : 0 < μ (StateEvent X t s) := by
        exact bot_lt_iff_ne_bot.mpr EventNull
      have RealProbabilityPositive : 0 < (μ (StateEvent X t s)).toReal := by
        exact ENNReal.toReal_pos EventNull (measure_ne_top μ (StateEvent X t s))
      have ConditionalUpperBound :
          (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) /
            (μ (StateEvent X t s)).toReal ≤ Delta := by
        exact StateDriftUpperBound t s StateInS StateNonzero EventPositive
      exact (div_le_iff₀ RealProbabilityPositive).mp ConditionalUpperBound
  rw [FiniteStateExpectedDecrease μ X S t CoordinatesMeasurable ValuesInS ZeroAbsorbing]
  rw [FiniteStateNonzeroProbability μ X S t (CoordinatesMeasurable t) (ValuesInS t)]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum StateContributionUpperBound

end

end ECTheoryLib.Tools.Drift
