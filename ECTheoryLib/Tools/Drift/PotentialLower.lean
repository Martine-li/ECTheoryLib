import ECTheoryLib.Tools.Drift.Potential

/-!
# Potential rescaling for runtime lower bounds

The comparison is verified on actual successive samples, so unsupported
state pairs need not satisfy it. Conditioning uses only positive-mass
potential levels and does not require the rescaling to be injective.

The expected-time bound retains infinity. Only in the finite-tail-sum
branch are terminal means proved to vanish, using the existing finite-range
bound and the inclusion of transformed nonzero events in original ones.
The potential must be zero at zero, but may also vanish at other states.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A supported upper bound for the transformed difference transfers a conditional drift ceiling to expected decrease. -/
theorem PotentialExpectedDecreaseUpper (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (h g : ℝ → ℝ) (c : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X) (PositiveC : 0 < c)
    (DriftPositive : ∀ s ∈ S, s ≠ 0 → 0 < h s)
    (PotentialDifference : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      g (X t ω)-g (X (t+1) ω) ≤ c*((X t ω-X (t+1) ω)/h (X t ω)))
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h s)
    (t : Nat) :
    ExpectedValue μ (fun ω => g (X t ω)) - ExpectedValue μ (fun ω => g (X (t+1) ω)) ≤
      c*(μ {ω | X t ω ≠ 0}).toReal := by
  classical
  let D : Ω → ℝ := fun ω => g (X t ω)-g (X (t+1) ω)
  have CurrentIntegrable := FiniteStateCompositionIntegrable μ (X t) S g
    (CoordinatesMeasurable t) (ValuesInS t)
  have NextIntegrable := FiniteStateCompositionIntegrable μ (X (t+1)) S g
    (CoordinatesMeasurable (t+1)) (ValuesInS (t+1))
  have DecreaseIntegrable : Integrable D μ := CurrentIntegrable.sub NextIntegrable
  have ZeroContribution : (∫ ω in StateEvent X t 0, D ω ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    apply (ae_restrict_iff' (StateEventMeasurable X t 0 (CoordinatesMeasurable t))).mpr
    filter_upwards [ZeroAbsorbing t] with ω Absorbing
    intro InZero
    have CurrentZero : X t ω = 0 := InZero
    have NextZero : X (t+1) ω = 0 := Absorbing CurrentZero
    change g (X t ω)-g (X (t+1) ω) = 0
    rw [CurrentZero, NextZero, sub_self]
  have Partition : (∫ ω, D ω ∂μ) =
      ∑ s ∈ S.erase 0, ∫ ω in StateEvent X t s, D ω ∂μ := by
    rw [FiniteStateIntegralPartition μ X t S D (CoordinatesMeasurable t) (ValuesInS t) DecreaseIntegrable]
    exact (Finset.sum_erase S ZeroContribution).symm
  have EachContribution : ∀ s ∈ S.erase 0,
      (∫ ω in StateEvent X t s, D ω ∂μ) ≤ c*(μ (StateEvent X t s)).toReal := by
    intro s InErased
    have InS : s ∈ S := (Finset.mem_erase.mp InErased).2
    have Nonzero : s ≠ 0 := (Finset.mem_erase.mp InErased).1
    by_cases EventNull : μ (StateEvent X t s) = 0
    · rw [EventNull, ENNReal.toReal_zero, Measure.restrict_eq_zero.mpr EventNull,
        integral_zero_measure, mul_zero]
    · have ProbabilityPositive : 0 < (μ (StateEvent X t s)).toReal :=
        ENNReal.toReal_pos EventNull (measure_ne_top μ _)
      have DriftBound : (∫ ω in StateEvent X t s, X t ω-X (t+1) ω ∂μ)/
          (μ (StateEvent X t s)).toReal ≤ h s :=
        StateDriftUpperBound t s InS Nonzero (bot_lt_iff_ne_bot.mpr EventNull)
      have OriginalContribution : (∫ ω in StateEvent X t s, X t ω-X (t+1) ω ∂μ) ≤
          h s*(μ (StateEvent X t s)).toReal := (div_le_iff₀ ProbabilityPositive).mp DriftBound
      have OriginalIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ :=
        (FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t) (ae_of_all _ (ValuesInS t))).sub
          (FiniteStateIntegrable μ (X (t+1)) S (CoordinatesMeasurable (t+1)) (ae_of_all _ (ValuesInS (t+1))))
      have IntegralComparison : (∫ ω in StateEvent X t s, D ω ∂μ) ≤
          ∫ ω in StateEvent X t s, c*((X t ω-X (t+1) ω)/h s) ∂μ := by
        apply integral_mono_ae DecreaseIntegrable.integrableOn
          ((OriginalIntegrable.div_const _).const_mul c).integrableOn
        apply (ae_restrict_iff' (StateEventMeasurable X t s (CoordinatesMeasurable t))).mpr
        filter_upwards [PotentialDifference t] with ω Difference
        intro InEvent
        have CurrentValue : X t ω = s := InEvent
        have CurrentNonzero : X t ω ≠ 0 := by rw [CurrentValue]; exact Nonzero
        have Bound := Difference CurrentNonzero
        rw [CurrentValue] at Bound
        change g (X t ω)-g (X (t+1) ω) ≤ c*((X t ω-X (t+1) ω)/h s)
        rw [CurrentValue]
        exact Bound
      rw [integral_const_mul, integral_div] at IntegralComparison
      have ProbabilityComparison : (∫ ω in StateEvent X t s, X t ω-X (t+1) ω ∂μ)/h s ≤
          (μ (StateEvent X t s)).toReal := by
        apply (div_le_iff₀ (DriftPositive s InS Nonzero)).mpr
        rw [mul_comm]
        exact OriginalContribution
      exact IntegralComparison.trans (mul_le_mul_of_nonneg_left ProbabilityComparison PositiveC.le)
  unfold ExpectedValue
  rw [← integral_sub CurrentIntegrable NextIntegrable, Partition,
    FiniteStateNonzeroProbability μ X S t (CoordinatesMeasurable t) (ValuesInS t), Finset.mul_sum]
  exact Finset.sum_le_sum EachContribution

/-- Potential rescaling gives a runtime lower bound without assuming finite expectation or an injective rescaling. -/
theorem PotentialDriftLowerBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (h g : ℝ → ℝ) (c : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X) (PositiveC : 0 < c)
    (PotentialZero : g 0 = 0) (PotentialNonnegative : ∀ s ∈ S, 0 ≤ g s)
    (DriftPositive : ∀ s ∈ S, s ≠ 0 → 0 < h s)
    (PotentialDifference : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      g (X t ω)-g (X (t+1) ω) ≤ c*((X t ω-X (t+1) ω)/h (X t ω)))
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h s) :
    ENNReal.ofReal (ExpectedValue μ (fun ω => g (X 0 ω))/c) ≤ ExpectedZeroHittingTime μ X := by
  classical
  let Y := fun t ω => g (X t ω)
  have MeasurableY (t : Nat) : Measurable (Y t) :=
    FiniteStateCompositionMeasurable (X t) S g (CoordinatesMeasurable t) (ValuesInS t)
  have ValuesY (t : Nat) (ω : Ω) : Y t ω ∈ S.image g :=
    Finset.mem_image.mpr ⟨X t ω, ValuesInS t ω, rfl⟩
  have NonnegativeY : ∀ s ∈ S.image g, 0 ≤ s := by
    intro s InImage
    obtain ⟨a, InS, rfl⟩ := Finset.mem_image.mp InImage
    exact PotentialNonnegative a InS
  have OneStepDecrease (t : Nat) : ExpectedValue μ (Y t)-ExpectedValue μ (Y (t+1)) ≤
      c*(μ {ω | X t ω ≠ 0}).toReal :=
    PotentialExpectedDecreaseUpper μ X S h g c CoordinatesMeasurable ValuesInS
      ZeroAbsorbing PositiveC DriftPositive PotentialDifference StateDriftUpperBound t
  have TerminalExpectation : (∑' t : Nat, μ {ω | X t ω ≠ 0}) ≠ ⊤ →
      Filter.Tendsto (fun t => ExpectedValue μ (Y t)) Filter.atTop (nhds 0) := by
    intro TailSumFinite
    have TailTendsto : Filter.Tendsto (fun t => μ {ω | X t ω ≠ 0}) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top TailSumFinite
    have RealTailTendsto : Filter.Tendsto (fun t => (μ {ω | X t ω ≠ 0}).toReal) Filter.atTop (nhds 0) := by
      have Converted := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp TailTendsto
      rw [ENNReal.toReal_zero] at Converted
      exact Converted
    have TailComparison (t : Nat) : (μ {ω | Y t ω ≠ 0}).toReal ≤ (μ {ω | X t ω ≠ 0}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      apply measure_mono
      intro ω NonzeroY ZeroX
      apply NonzeroY
      change g (X t ω) = 0
      rw [ZeroX, PotentialZero]
    have RealYTailTendsto : Filter.Tendsto (fun t => (μ {ω | Y t ω ≠ 0}).toReal) Filter.atTop (nhds 0) :=
      squeeze_zero (fun _ => ENNReal.toReal_nonneg) TailComparison RealTailTendsto
    exact FiniteStateExpectedValueTendstoZero μ Y (S.image g) MeasurableY NonnegativeY ValuesY RealYTailTendsto
  rw [ExpectedZeroHittingTimeEqNonzeroSum μ X CoordinatesMeasurable ZeroAbsorbing]
  exact ExpectedDecreaseTailSumLowerBound (fun t => ExpectedValue μ (Y t))
    (fun t => μ {ω | X t ω ≠ 0}) c PositiveC (fun _ => measure_ne_top μ _)
    OneStepDecrease TerminalExpectation

end
end ECTheoryLib.Tools.Drift
