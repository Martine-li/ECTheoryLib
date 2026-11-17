import ECTheoryLib.Probability.Processes.ScalarProcess
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Adapted

/-!
# From filtration-conditioned drift to state-event drift

This is a bridge to the existing StateDrift convention, not a replacement
for Mathlib conditional expectation. The measurable state event belongs to
the filtration because the process is adapted. Mathlib setIntegral_condExp
then transfers the integral bound. Only positive-mass events are divided by.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A conditional drift bound given the filtration implies the bound on each positive-mass state event. -/
theorem StateDriftUpperBoundOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (h : ℝ → ℝ) (t : ℕ)
    (DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ)
    (ConditionalBound : ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ h (X t ω))
    (s : ℝ) (Nonzero : s ≠ 0) (PositiveEvent : 0 < μ (StateEvent X t s)) :
    StateDrift μ X t s ≤ h s := by
  have PastEvent : MeasurableSet[F t] (StateEvent X t s) :=
    measurableSet_eq_fun (ProcessAdapted t) measurable_const
  have AmbientEvent : MeasurableSet (StateEvent X t s) := F.le t _ PastEvent
  have ConditionalIntegral := setIntegral_condExp (F.le t) DecreaseIntegrable PastEvent
  have IntegralBound : (∫ ω in StateEvent X t s, X t ω-X (t+1) ω ∂μ) ≤
      ∫ _ω in StateEvent X t s, h s ∂μ := by
    rw [← ConditionalIntegral]
    apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
    apply (ae_restrict_iff' AmbientEvent).mpr
    filter_upwards [ConditionalBound] with ω Bound
    intro InEvent
    have Current : X t ω = s := InEvent
    have CurrentNonzero : X t ω ≠ 0 := by rw [Current]; exact Nonzero
    have AtCurrent := Bound CurrentNonzero
    rw [Current] at AtCurrent
    exact AtCurrent
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at IntegralBound
  have PositiveReal : 0 < (μ (StateEvent X t s)).toReal :=
    ENNReal.toReal_pos PositiveEvent.ne' (measure_ne_top μ _)
  unfold StateDrift EventConditionalExpectation
  apply (div_le_iff₀ PositiveReal).mpr
  rw [mul_comm]
  exact IntegralBound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- An integrable observable bounded in conditional mean is bounded on every positive-mass current-state event. -/
theorem StateEventExpectationUpperBoundOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (h : ℝ → ℝ) (t : ℕ) (Z : Ω → ℝ)
    (ObservableIntegrable : Integrable Z μ)
    (ConditionalBound : ∀ᵐ ω ∂μ, X t ω ≠ 0 → (μ[Z | F t]) ω ≤ h (X t ω))
    (s : ℝ) (Nonzero : s ≠ 0) (PositiveEvent : 0 < μ (StateEvent X t s)) :
    EventConditionalExpectation μ Z (StateEvent X t s) ≤ h s := by
  have PastEvent : MeasurableSet[F t] (StateEvent X t s) :=
    measurableSet_eq_fun (ProcessAdapted t) measurable_const
  have AmbientEvent : MeasurableSet (StateEvent X t s) := F.le t _ PastEvent
  have ConditionalIntegral := setIntegral_condExp (F.le t) ObservableIntegrable PastEvent
  have IntegralBound : (∫ ω in StateEvent X t s, Z ω ∂μ) ≤
      ∫ _ω in StateEvent X t s, h s ∂μ := by
    rw [← ConditionalIntegral]
    apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
    apply (ae_restrict_iff' AmbientEvent).mpr
    filter_upwards [ConditionalBound] with ω Bound
    intro InEvent
    have Current : X t ω=s := InEvent
    have CurrentNonzero : X t ω ≠ 0 := by rw [Current]; exact Nonzero
    have AtCurrent := Bound CurrentNonzero
    rw [Current] at AtCurrent
    exact AtCurrent
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at IntegralBound
  have PositiveReal : 0 < (μ (StateEvent X t s)).toReal :=
    ENNReal.toReal_pos PositiveEvent.ne' (measure_ne_top μ _)
  unfold EventConditionalExpectation
  apply (div_le_iff₀ PositiveReal).mpr
  rw [mul_comm]
  exact IntegralBound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditional expectation on an arbitrary current-state region transfers to
positive state events. The region need not exclude the real number zero. -/
theorem StateEventExpectationUpperBoundOfCondExpOn (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (Region : ℝ → Prop) (h : ℝ → ℝ) (t : ℕ) (Z : Ω → ℝ)
    (ObservableIntegrable : Integrable Z μ)
    (ConditionalBound : ∀ᵐ ω ∂μ, Region (X t ω) → (μ[Z | F t]) ω ≤ h (X t ω))
    (s : ℝ) (InRegion : Region s) (PositiveEvent : 0 < μ (StateEvent X t s)) :
    EventConditionalExpectation μ Z (StateEvent X t s) ≤ h s := by
  have PastEvent : MeasurableSet[F t] (StateEvent X t s) :=
    measurableSet_eq_fun (ProcessAdapted t) measurable_const
  have AmbientEvent : MeasurableSet (StateEvent X t s) := F.le t _ PastEvent
  have ConditionalIntegral := setIntegral_condExp (F.le t) ObservableIntegrable PastEvent
  have IntegralBound : (∫ ω in StateEvent X t s, Z ω ∂μ) ≤
      ∫ _ω in StateEvent X t s, h s ∂μ := by
    rw [← ConditionalIntegral]
    apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
    apply (ae_restrict_iff' AmbientEvent).mpr
    filter_upwards [ConditionalBound] with ω Bound
    intro InEvent
    have Current : X t ω=s := InEvent
    have AtCurrent := Bound (by rw [Current]; exact InRegion)
    rw [Current] at AtCurrent
    exact AtCurrent
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at IntegralBound
  have PositiveReal : 0 < (μ (StateEvent X t s)).toReal :=
    ENNReal.toReal_pos PositiveEvent.ne' (measure_ne_top μ _)
  unfold EventConditionalExpectation
  apply (div_le_iff₀ PositiveReal).mpr
  rw [mul_comm]
  exact IntegralBound

end
end ECTheoryLib.Probability
