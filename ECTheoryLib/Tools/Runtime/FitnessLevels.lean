import ECTheoryLib.Probability.HittingTimes.LevelHittingTime
import ECTheoryLib.Probability.HittingTimes.GeometricStages

/-!
# Fitness-level runtime comparison from stage hazards

Nested entry times telescope to the actual final hitting time. This entry
combines that identity with the conditional geometric stage-sum theorem.
The input is a success floor after conditioning on complete stage histories
and survival. Deriving that input from the original algorithm-history premise
of Doerr Theorem 1.8.6 remains a separate obligation; this is a conditional API.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

open scoped unitInterval

/-- Conditional application: stage hazards must be proved from the concrete process. -/
theorem LevelHittingTimeGeometricBoundOfStageHazard {State : Type*} [MeasurableSpace State]
    (P : Measure (ℕ → State)) [IsProbabilityMeasure P] (Goals : ℕ → State → Prop)
    (GoalMeasurable : ∀ i, MeasurableSet {x | Goals i x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Hazard : ∀ (i : Fin n) (h : Fin i → WithTop ℕ),
      P (ExtendedNatPrefix (LevelDuration Goals) i ⁻¹' {h}) ≠ 0 →
      ∀ s : ℕ, (P[|ExtendedNatPrefix (LevelDuration Goals) i ⁻¹' {h}])
        {Path | (s : WithTop ℕ) < LevelDuration Goals i Path} ≠ 0 →
        (p i : ℝ) ≤ ((P[|ExtendedNatPrefix (LevelDuration Goals) i ⁻¹' {h}])[|{Path | (s : WithTop ℕ) < LevelDuration Goals i Path}]).real
          {Path | LevelDuration Goals i Path ≤ ((s+1 : ℕ) : WithTop ℕ)}) :
    StochasticDominated (P.map (FirstHittingTime (Goals n)))
      ((Measure.pi (fun i : Fin n => geometricMeasure (p i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  have MeasurableDurations (i : ℕ) : Measurable (LevelDuration Goals i) :=
    LevelDurationMeasurable Goals GoalMeasurable (fun t (Path : ℕ → State) => Path t) measurable_pi_apply i
  have Bound := GeometricStageSum P (LevelDuration Goals) MeasurableDurations n p Positive Hazard
  have RuntimeIdentity : (fun Path => ∑ i ∈ Finset.range n, LevelDuration Goals i Path) =
      FirstHittingTime (Goals n) := by
    funext Path
    exact LevelDurationSum Goals Nested Initially Path n
  rw [RuntimeIdentity] at Bound
  exact Bound



end
end ECTheoryLib.Tools.Runtime
