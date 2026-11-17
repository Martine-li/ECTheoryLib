import ECTheoryLib.Probability.HittingTimes.LevelHistory
import ECTheoryLib.Probability.Processes.PastEventTransition

/-!
# Fitness-level domination from the original process history

Doerr Theorem 1.8.6 is expressed using nested upper-level goals G0, ..., Gn,
with G0 containing every state. Level i is active exactly when its entry time
has occurred and the next entry time has not. The success premise holds on
every event measurable from the past and contained in that active level:
P(A and next point in G(i+1)) >= p(i) P(A). This integrated formulation handles
zero-probability histories without defining conditional probabilities there.

The general process need not be Markov, elitist, finite-state, or have
independent stage durations. The comparison variables, on an explicit product
space, ARE independent. Geometric waits start at one; initial successes and
skipped levels have duration zero. Infinite runtime is retained until the bound
is proved. A second interface verifies the premise for actual countable-state
transition kernels with nested absorbing goals. Iterations exclude initialization.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Fitness-level domination from past-measurable survival contraction; the process need not be Markov. -/
theorem FitnessLevelsOfPastEventProgress {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Progress : ∀ (i : Fin n) t (A : Set Ω), MeasurableSet[F t] A →
      (∀ ω ∈ A, FirstHittingTime (Goals i) (fun j => X j ω) ≤ (t : WithTop ℕ) ∧
        (t : WithTop ℕ) < FirstHittingTime (Goals (i+1)) (fun j => X j ω)) →
      P.real (A ∩ {ω | ((t+1 : ℕ) : WithTop ℕ) < FirstHittingTime (Goals (i+1)) (fun j => X j ω)}) ≤
        (1-(p i : ℝ))*P.real A) :
    StochasticDominated (P.map (fun ω => FirstHittingTime (Goals n) (fun t => X t ω)))
      ((Measure.pi (fun i : Fin n => geometricMeasure (p i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  let D := fun i ω => LevelDuration Goals i (fun t => X t ω)
  have MeasurableD (i : ℕ) : Measurable (D i) :=
    LevelDurationMeasurable Goals GoalMeasurable X (fun _ => AdaptedX.measurable) i
  have Bound := GeometricStageSum P D MeasurableD n p Positive (by
    intro i h NonzeroHistory s NonzeroSurvival
    have ConditionalProbability : IsProbabilityMeasure P[|ExtendedNatPrefix D i ⁻¹' {h}] :=
      cond_isProbabilityMeasure NonzeroHistory
    apply WaitingHazardOfSurvivalStep _ (D i) (MeasurableD i) (p i) s NonzeroSurvival
    exact StageHistorySurvivalStep P F X AdaptedX Goals GoalMeasurable Nested Initially i (p i)
      (Progress i) h s)
  have Runtime : (fun ω => ∑ i ∈ Finset.range n, D i ω) =
      (fun ω => FirstHittingTime (Goals n) (fun t => X t ω)) := by
    funext ω
    exact LevelDurationSum Goals Nested Initially (fun t => X t ω) n
  rw [Runtime] at Bound
  exact Bound

/-- Doerr Theorem 1.8.6: a success floor on every past event implies domination by independent geometric waits. -/
theorem FitnessLevelsOfPastEventSuccess {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Success : ∀ (i : Fin n) t (A : Set Ω), MeasurableSet[F t] A →
      (∀ ω ∈ A, FirstHittingTime (Goals i) (fun j => X j ω) ≤ (t : WithTop ℕ) ∧
        (t : WithTop ℕ) < FirstHittingTime (Goals (i+1)) (fun j => X j ω)) →
      (p i : ℝ)*P.real A ≤ P.real (A ∩ {ω | Goals (i+1) (X (t+1) ω)})) :
    StochasticDominated (P.map (fun ω => FirstHittingTime (Goals n) (fun t => X t ω)))
      ((Measure.pi (fun i : Fin n => geometricMeasure (p i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  apply FitnessLevelsOfPastEventProgress P F X AdaptedX Goals GoalMeasurable Nested Initially n p Positive
  intro i t A PastA InLevel
  have SuccessBound := Success i t A PastA InLevel
  have NextGoalMeasurable : MeasurableSet {ω | Goals (i+1) (X (t+1) ω)} :=
    AdaptedX.measurable (GoalMeasurable (i+1))
  have Partition := measureReal_inter_add_sdiff (μ := P) (s := A) NextGoalMeasurable
  calc
    _ ≤ P.real (A \ {ω | Goals (i+1) (X (t+1) ω)}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω Member
      refine ⟨Member.1, ?_⟩
      intro AtGoal
      have ReachedByNext := (FirstHittingTimeLeIff (Goals (i+1)) (fun j => X j ω) (t+1)).mpr
        ⟨t+1, le_rfl, AtGoal⟩
      exact (not_le_of_gt Member.2) ReachedByNext
    _ ≤ _ := by linarith

/-- A countable-state kernel client: nested absorbing goals and local progress verify the full history premise. -/
theorem PathFitnessLevelsGeometricBound {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goals : ℕ → State → Prop) (Nested : ∀ i x, Goals (i+1) x → Goals i x)
    (Initially : ∀ x, Goals 0 x) (n : ℕ) (p : Fin n → I) (Positive : ∀ i, 0 < (p i : ℝ))
    (Absorption : ∀ i x, ∀ᵐ y ∂(Step x).toMeasure, Goals i x → Goals i y)
    (Success : ∀ (i : Fin n) x, Goals i x → ¬Goals (i+1) x →
      (p i : ℝ) ≤ (Step x).toMeasure.real {y | Goals (i+1) y}) :
    StochasticDominated ((PathMeasure Step Initial).map (FirstHittingTime (Goals n)))
      ((Measure.pi (fun i : Fin n => geometricMeasure (p i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  have MeasurableGoals (i : ℕ) : MeasurableSet {x | Goals i x} := (Set.to_countable _).measurableSet
  apply FitnessLevelsOfPastEventProgress (PathMeasure Step Initial) Filtration.piLE
    (fun t Path => Path t) PathCoordinatesAdapted Goals MeasurableGoals Nested Initially n p Positive
  intro i t A PastA InLevel
  have LocalBound : ∀ᵐ Path ∂PathMeasure Step Initial,
      Path ∈ A → (Step (Path t)).toMeasure.real {y | ¬Goals (i+1) y} ≤ 1-(p i : ℝ) := by
    have Preserved := ae_all_iff.mpr (fun s => PathMeasureFollowsTransition Step Initial
      (fun x y => Goals i x → Goals i y) (Absorption i) s)
    filter_upwards [Preserved] with Path Preserves InA
    obtain ⟨ReachedEarlier, NotReachedLater⟩ := InLevel Path InA
    obtain ⟨s, Before, Reached⟩ := (FirstHittingTimeLeIff (Goals i) Path t).mp ReachedEarlier
    have AtEarlier : Goals i (Path t) := Nat.le_induction
      (P := fun u _ => Goals i (Path u)) Reached (fun u _ AtGoal => Preserves u AtGoal) t Before
    have NotLater : ¬Goals (i+1) (Path t) := by
      intro AtGoal
      have ReachedByNow := (FirstHittingTimeLeIff (Goals (i+1)) Path t).mpr ⟨t, le_rfl, AtGoal⟩
      exact (not_le_of_gt NotReachedLater) ReachedByNow
    have SuccessBound := Success i (Path t) AtEarlier NotLater
    have Complement : {y | ¬Goals (i+1) y} = {y | Goals (i+1) y}ᶜ := rfl
    rw [Complement, probReal_compl_eq_one_sub (MeasurableGoals (i+1))]
    exact sub_le_sub_left SuccessBound 1
  have StateBound := PathPastEventTransitionBound Step Initial t A PastA {y | ¬Goals (i+1) y}
    (1-(p i : ℝ)) (sub_nonneg.mpr (p i).2.2) LocalBound
  calc
    _ ≤ (PathMeasure Step Initial).real (A ∩ {Path | ¬Goals (i+1) (Path (t+1))}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Path Member
      refine ⟨Member.1, ?_⟩
      intro AtGoal
      have ReachedByNext := (FirstHittingTimeLeIff (Goals (i+1)) Path (t+1)).mpr
        ⟨t+1, le_rfl, AtGoal⟩
      exact (not_le_of_gt Member.2) ReachedByNext
    _ ≤ _ := StateBound

end
end ECTheoryLib.Tools.Runtime
