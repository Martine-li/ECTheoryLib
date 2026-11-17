import ECTheoryLib.Tools.Drift.MultiplicativeTail
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Multiplicative tails conditional on survival and current state

The original finite-range process may leave zero. Drift is conditioned on
both strict survival and the current level; no full-history bound is assumed.
The existing absorbing theorem supplies the unchanged natural-ceiling bound.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Theorem 2.4.5's ceiling conclusion under survival-and-level conditional
drift. This is an explicit corrected conditioning premise, not the invalid
raw-level-only nonabsorbing interpretation of the source statement. -/
theorem MultiplicativeDriftUpperTailOfSurvivingStateDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin Delta s0 : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S) (PositiveDelta : 0 < Delta)
    (SurvivingStateDrift : ∀ (t : ℕ) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      Delta * s ≤ EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s})
    (InitialFixed : ∀ᵐ ω ∂μ, X 0 ω = s0) (InitialPositive : 0 < s0)
    (r : ℝ) (NonnegativeR : 0 ≤ r) :
    μ {ω | (⌈(r + Real.log (s0 / smin)) / Delta⌉₊ : WithTop ℕ) <
      ZeroHittingTime X ω} ≤ ENNReal.ofReal (Real.exp (-r)) := by
  have Pointwise : ∀ j ω, 0 ≤ X j ω := by
    intro j ω
    rcases StateLowerBound _ (ValuesInS j ω) with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  let Y := StopAtFirstHit (fun x : ℝ => x ≤ 0) X
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro j
    change Measurable (X j)
    exact CoordinatesMeasurable j
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) ValuesInS
  have Initial : ∀ᵐ ω ∂μ, Y 0 ω = s0 := by
    simpa only [Y, StopAtFirstHitInitial] using InitialFixed
  have StoppedDrift : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent Y t s) → Delta * s ≤ StateDrift μ Y t s := by
    intro t s InS Nonzero Positive
    have Event : StateEvent Y t s =
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} :=
      StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero
    rw [Event] at Positive
    have DriftIdentity := StoppedStateDriftEqSurvivingEventExpectation μ X
      CoordinatesMeasurable Pointwise t s Nonzero
    change StateDrift μ Y t s = _ at DriftIdentity
    rw [DriftIdentity]
    exact SurvivingStateDrift t s InS Nonzero Positive
  have Bound := MultiplicativeDriftUpperTail μ Y S smin Delta s0
    (fun _ => AdaptedY.measurable) ZeroInS MinimumPositive StateLowerBound YValues
    (StopAtNonpositiveZeroAbsorbing μ X Pointwise) PositiveDelta StoppedDrift
    Initial InitialPositive r NonnegativeR
  have Times : ZeroHittingTime Y = ZeroHittingTime X :=
    funext (StopAtNonpositiveZeroTime X Pointwise)
  rwa [Times] at Bound

end
end ECTheoryLib.Tools.Drift
