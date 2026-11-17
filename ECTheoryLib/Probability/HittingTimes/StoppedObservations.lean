import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Integrable two-state observations before the first hit

Transfer complete-history bounds to positive stopped-state events by
past-measurable set integrals. No finite potential range is required.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A history-conditioned bound for an integrable two-state observation
transfers to a positive stopped-state event. No finite range is needed. -/
theorem StoppedStateObservationUpperBoundOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (Nonnegative : ∀ t ω, 0≤X t ω)
    (f : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (t : ℕ)
    (ObservationIntegrable : Integrable (fun ω => f (X t ω) (X (t+1) ω)) μ)
    (Bound : ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => f (X t u) (X (t+1) u) | F t]) ω≤h (X t ω))
    (s : ℝ) (Nonzero : s≠0)
    (Positive : 0<μ (StateEvent (StopAtFirstHit (fun s : ℝ => s≤0) X) t s)) :
    EventConditionalExpectation μ
      (fun ω => f (StopAtFirstHit (fun s : ℝ => s≤0) X t ω)
        (StopAtFirstHit (fun s : ℝ => s≤0) X (t+1) ω))
      (StateEvent (StopAtFirstHit (fun s : ℝ => s≤0) X) t s)≤h s := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have EqualOn : ∀ ω, Y t ω≠0 → Y t ω=X t ω ∧ Y (t+1) ω=X (t+1) ω := by
    intro ω Active
    have Above : 0<Y t ω := lt_of_le_of_ne
      (StopAtNonpositiveNonnegative X Nonnegative t ω) (Ne.symm Active)
    exact StopAtFirstHitStepBefore _ X t ω (not_le_of_gt Above)
  have RawBound := StateEventExpectationUpperBoundOfCondExp μ Y F AdaptedY h t
    (fun ω => f (X t ω) (X (t+1) ω)) ObservationIntegrable (by
      filter_upwards [Bound] with ω Bound
      intro Active
      have Equal := EqualOn ω Active
      rw [Equal.1]
      apply Bound
      rwa [← Equal.1]) s Nonzero Positive
  change EventConditionalExpectation μ (fun ω => f (Y t ω) (Y (t+1) ω)) (StateEvent Y t s)≤h s
  unfold EventConditionalExpectation at RawBound ⊢
  have Integrals : (∫ ω in StateEvent Y t s, f (Y t ω) (Y (t+1) ω) ∂μ)=
      ∫ ω in StateEvent Y t s, f (X t ω) (X (t+1) ω) ∂μ := by
    apply integral_congr_ae
    apply (ae_restrict_iff' (StateEventMeasurable Y t s AdaptedY.measurable)).mpr
    apply ae_of_all
    intro ω InEvent
    have Current : Y t ω=s := InEvent
    have Equal := EqualOn ω (by rwa [Current])
    change f (Y t ω) (Y (t+1) ω)=f (X t ω) (X (t+1) ω)
    rw [Equal.1,Equal.2]
  rwa [Integrals]

end
end ECTheoryLib.Probability
