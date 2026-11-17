import ECTheoryLib.Tools.Drift.MultiplicativeTail
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Nonabsorbing multiplicative upper tails with full-history drift

Stopping preserves the required conditional decrease because conditioning
is on the filtration. The finite nonnegative potential range is retained.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Complete-history multiplicative drift gives a first-hitting tail even
when the original process can leave zero. Finite potential range is retained. -/
theorem MultiplicativeDriftTailAtTimeNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin Delta : ℝ)
    (MinimumPositive : 0<smin) (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s)
    (Values : ∀ t ω, X t ω∈S)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      Delta*X t ω≤(μ[fun u => X t u-X (t+1) u | F t]) ω) (t : ℕ) :
    μ {ω | (t : WithTop ℕ)<ZeroHittingTime X ω} ≤
      ENNReal.ofReal (Real.exp (-Delta*(t : ℝ))*ExpectedValue μ (X 0)/smin) := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ j ω, 0≤X j ω := fun j ω => Nonnegative _ (Values j ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := MultiplicativeDriftTailAtTime μ Y S smin Delta (fun _ => AdaptedY.measurable)
    MinimumPositive StateLowerBound YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise) (by
      intro j s _ Nonzero Positive
      exact StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun s => Delta*s) Drift j s Nonzero Positive) t
  have Times : ZeroHittingTime Y=ZeroHittingTime X := funext (StopAtNonpositiveZeroTime X Pointwise)
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times,Initial] at Bound

/-- The natural-ceiling upper tail with a fixed positive initial value.
The new nonabsorbing interface deliberately uses full-history conditioning. -/
theorem MultiplicativeDriftUpperTailNonabsorbing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin Delta s0 : ℝ)
    (ZeroInS : 0∈S) (MinimumPositive : 0<smin)
    (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ t ω, X t ω∈S)
    (PositiveDelta : 0<Delta)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      Delta*X t ω≤(μ[fun u => X t u-X (t+1) u | F t]) ω)
    (InitialFixed : ∀ᵐ ω ∂μ, X 0 ω=s0) (InitialPositive : 0<s0)
    (r : ℝ) (NonnegativeR : 0≤r) :
    μ {ω | (⌈(r+Real.log (s0/smin))/Delta⌉₊ : WithTop ℕ)<ZeroHittingTime X ω} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ j ω, 0≤X j ω := fun j ω => Nonnegative _ (Values j ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Initial : ∀ᵐ ω ∂μ, Y 0 ω=s0 := by simpa only [Y,StopAtFirstHitInitial] using InitialFixed
  have Bound := MultiplicativeDriftUpperTail μ Y S smin Delta s0 (fun _ => AdaptedY.measurable)
    ZeroInS MinimumPositive StateLowerBound YValues (StopAtNonpositiveZeroAbsorbing μ X Pointwise)
    PositiveDelta (by
      intro j s _ Nonzero Positive
      exact StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun s => Delta*s) Drift j s Nonzero Positive) Initial InitialPositive r NonnegativeR
  have Times : ZeroHittingTime Y=ZeroHittingTime X := funext (StopAtNonpositiveZeroTime X Pointwise)
  rwa [Times] at Bound

end
end ECTheoryLib.Tools.Drift
