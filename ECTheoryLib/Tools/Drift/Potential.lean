import ECTheoryLib.Tools.Drift.Additive

/-!
# Potential rescaling for finite-state drift processes

The hypotheses concern the original conditional drift, not the drift of a
rescaled process.  A deterministic inequality between two potential values
supplies the rescaled decrease inside each conditioning event.  This avoids
any injectivity requirement on the rescaling function.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An arbitrary function of a measurable finite-valued variable is measurable.
Its restriction to the finite range is a map between discrete measurable spaces. -/
theorem FiniteStateCompositionMeasurable (X : Ω → ℝ) (S : Finset ℝ)
    (g : ℝ → ℝ) (VariableMeasurable : Measurable X)
    (ValuesInS : ∀ ω, X ω ∈ S) : Measurable (fun ω => g (X ω)) := by
  let FiniteVariable : Ω → {s : ℝ // s ∈ S} := fun ω => ⟨X ω, ValuesInS ω⟩
  have FiniteVariableMeasurable : Measurable FiniteVariable := by
    exact VariableMeasurable.subtype_mk
  have RestrictedFunctionMeasurable : Measurable (fun s : {s : ℝ // s ∈ S} => g s) := by
    exact measurable_of_finite _
  exact RestrictedFunctionMeasurable.comp FiniteVariableMeasurable

/-- The rescaling remains integrable because its range is still finite. -/
theorem FiniteStateCompositionIntegrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (S : Finset ℝ) (g : ℝ → ℝ)
    (VariableMeasurable : Measurable X) (ValuesInS : ∀ ω, X ω ∈ S) :
    Integrable (fun ω => g (X ω)) μ := by
  classical
  apply FiniteStateIntegrable μ _ (S.image g)
  · exact FiniteStateCompositionMeasurable X S g VariableMeasurable ValuesInS
  · apply Filter.Eventually.of_forall
    intro ω
    exact Finset.mem_image.mpr ⟨X ω, ValuesInS ω, rfl⟩

/-- A supporting-line inequality for `g`, together with drift at least `h(s)`,
gives a unit expected decrease whenever the original process is nonzero. -/
theorem PotentialExpectedDecrease (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (h g : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (DriftPositive : ∀ s ∈ S, s ≠ 0 → 0 < h s)
    (PotentialDifference : ∀ s ∈ S, s ≠ 0 → ∀ r ∈ S,
      (s - r) / h s ≤ g s - g r)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → h s ≤ StateDrift μ X t s)
    (t : Nat) :
    (μ {ω | X t ω ≠ 0}).toReal ≤
      ExpectedValue μ (fun ω => g (X t ω)) -
        ExpectedValue μ (fun ω => g (X (t + 1) ω)) := by
  classical
  let D : Ω → ℝ := fun ω => g (X t ω) - g (X (t + 1) ω)
  have CurrentIntegrable := FiniteStateCompositionIntegrable μ (X t) S g
    (CoordinatesMeasurable t) (ValuesInS t)
  have NextIntegrable := FiniteStateCompositionIntegrable μ (X (t + 1)) S g
    (CoordinatesMeasurable (t + 1)) (ValuesInS (t + 1))
  have DecreaseIntegrable : Integrable D μ := CurrentIntegrable.sub NextIntegrable
  have ZeroContribution : (∫ ω in StateEvent X t 0, D ω ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    apply (ae_restrict_iff' (StateEventMeasurable X t 0 (CoordinatesMeasurable t))).mpr
    filter_upwards [ZeroAbsorbing t] with ω AbsorbingAtSample
    intro InZeroEvent
    have CurrentZero : X t ω = 0 := InZeroEvent
    have NextZero : X (t + 1) ω = 0 := AbsorbingAtSample CurrentZero
    change g (X t ω) - g (X (t + 1) ω) = 0
    rw [CurrentZero, NextZero, sub_self]
  have Partition : (∫ ω, D ω ∂μ) =
      ∑ s ∈ S.erase 0, ∫ ω in StateEvent X t s, D ω ∂μ := by
    rw [FiniteStateIntegralPartition μ X t S D (CoordinatesMeasurable t)
      (ValuesInS t) DecreaseIntegrable]
    exact (Finset.sum_erase S ZeroContribution).symm
  have EachContribution : ∀ s ∈ S.erase 0,
      (μ (StateEvent X t s)).toReal ≤ ∫ ω in StateEvent X t s, D ω ∂μ := by
    intro s InErasedSet
    have InS : s ∈ S := (Finset.mem_erase.mp InErasedSet).2
    have Nonzero : s ≠ 0 := (Finset.mem_erase.mp InErasedSet).1
    by_cases EventNull : μ (StateEvent X t s) = 0
    · rw [EventNull, ENNReal.toReal_zero, Measure.restrict_eq_zero.mpr EventNull,
        integral_zero_measure]
    · have RealProbabilityPositive : 0 < (μ (StateEvent X t s)).toReal := by
        exact ENNReal.toReal_pos EventNull (measure_ne_top μ _)
      have DriftBound : h s ≤
          (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) /
            (μ (StateEvent X t s)).toReal := by
        exact StateDriftLowerBound t s InS Nonzero (bot_lt_iff_ne_bot.mpr EventNull)
      have OriginalContribution : h s * (μ (StateEvent X t s)).toReal ≤
          ∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ := by
        exact (le_div_iff₀ RealProbabilityPositive).mp DriftBound
      have OriginalIntegrable : Integrable (fun ω => X t ω - X (t + 1) ω) μ := by
        exact (FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t)
          (Filter.Eventually.of_forall (ValuesInS t))).sub
          (FiniteStateIntegrable μ (X (t + 1)) S (CoordinatesMeasurable (t + 1))
            (Filter.Eventually.of_forall (ValuesInS (t + 1))))
      have IntegralComparison :
          (∫ ω in StateEvent X t s, (X t ω - X (t + 1) ω) / h s ∂μ) ≤
            ∫ ω in StateEvent X t s, D ω ∂μ := by
        apply setIntegral_mono_on (OriginalIntegrable.div_const (h s)).integrableOn
          DecreaseIntegrable.integrableOn (StateEventMeasurable X t s (CoordinatesMeasurable t))
        intro ω InEvent
        have CurrentValue : X t ω = s := InEvent
        change (X t ω - X (t + 1) ω) / h s ≤ g (X t ω) - g (X (t + 1) ω)
        rw [CurrentValue]
        exact PotentialDifference s InS Nonzero (X (t + 1) ω) (ValuesInS (t + 1) ω)
      rw [integral_div] at IntegralComparison
      have ProbabilityComparison : (μ (StateEvent X t s)).toReal ≤
          (∫ ω in StateEvent X t s, X t ω - X (t + 1) ω ∂μ) / h s := by
        apply (le_div_iff₀ (DriftPositive s InS Nonzero)).mpr
        rw [mul_comm]
        exact OriginalContribution
      exact ProbabilityComparison.trans IntegralComparison
  unfold ExpectedValue
  rw [← integral_sub CurrentIntegrable NextIntegrable]
  rw [Partition, FiniteStateNonzeroProbability μ X S t (CoordinatesMeasurable t) (ValuesInS t)]
  exact Finset.sum_le_sum EachContribution

/-- Finite-state rescaling theorem. The runtime bound follows from an original
state-drift bound and a deterministic supporting-line inequality for `g`. -/
theorem PotentialDriftUpperBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (h g : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PotentialNonnegative : ∀ s ∈ S, 0 ≤ g s)
    (DriftPositive : ∀ s ∈ S, s ≠ 0 → 0 < h s)
    (PotentialDifference : ∀ s ∈ S, s ≠ 0 → ∀ r ∈ S,
      (s - r) / h s ≤ g s - g r)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → h s ≤ StateDrift μ X t s) :
    ExpectedZeroHittingTime μ X ≤
      ENNReal.ofReal (ExpectedValue μ (fun ω => g (X 0 ω))) := by
  have ExpectationsNonnegative : ∀ t, 0 ≤ ExpectedValue μ (fun ω => g (X t ω)) := by
    intro t
    apply integral_nonneg
    intro ω
    exact PotentialNonnegative (X t ω) (ValuesInS t ω)
  have OneStepDecrease : ∀ t,
      1 * (μ {ω | X t ω ≠ 0}).toReal ≤
        ExpectedValue μ (fun ω => g (X t ω)) -
          ExpectedValue μ (fun ω => g (X (t + 1) ω)) := by
    intro t
    rw [one_mul]
    exact PotentialExpectedDecrease μ X S h g CoordinatesMeasurable ValuesInS
      ZeroAbsorbing DriftPositive PotentialDifference StateDriftLowerBound t
  rw [ExpectedZeroHittingTimeEqNonzeroSum μ X CoordinatesMeasurable ZeroAbsorbing]
  have Bound := ExpectedDecreaseTailSumUpperBound
    (fun t => ExpectedValue μ (fun ω => g (X t ω)))
    (fun t => μ {ω | X t ω ≠ 0}) 1 zero_lt_one ExpectationsNonnegative
    (fun t => measure_ne_top μ _) OneStepDecrease
  rw [div_one] at Bound
  exact Bound

end

end ECTheoryLib.Tools.Drift
