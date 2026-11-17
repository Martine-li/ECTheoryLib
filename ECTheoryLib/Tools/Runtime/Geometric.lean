import ECTheoryLib.Probability.HittingTimes.GeometricHazard
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Geometric waiting bounds for actual trajectories

Local transition probabilities are transferred to the path law through the
existing transition-integral identity. The valid region may be a strict subset
of the finite state space. Goal absorption and preservation of this region are
explicit obligations; no termination or finite-mean assumption is used.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

private theorem GoalComplementIntegral {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (P : Measure State) (Goal : State -> Prop) [DecidablePred Goal] :
    (∫ x, (if Goal x then (0 : Real) else 1) ∂P) = P.real {x | ¬Goal x} := by
  classical
  have Integrands : (fun x => if Goal x then (0 : Real) else 1) =
      {x | ¬Goal x}.indicator (fun _ => (1 : Real)) := by
    funext x
    by_cases AtGoal : Goal x
    . simp only [Set.indicator_apply, Set.mem_ofPred_eq, AtGoal, not_true_eq_false, if_false, if_true]
    . simp only [Set.indicator_apply, Set.mem_ofPred_eq, AtGoal, not_false_eq_true, if_true, if_false]
  rw [Integrands]
  exact integral_indicator_one (Set.to_countable _).measurableSet

private theorem PathGoalTail {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goal : State -> Prop)
    (Absorption : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x -> Goal y) (t : Nat) :
    (PathMeasure Step Initial) {Path | (t : WithTop Nat) < FirstHittingTime Goal Path} =
      (PathMeasure Step Initial) {Path | ¬Goal (Path t)} := by
  have AllSteps := ae_all_iff.mpr (fun s => PathMeasureFollowsTransition Step Initial
    (fun x y => Goal x -> Goal y) Absorption s)
  apply measure_congr
  filter_upwards [AllSteps] with Path Preserved
  apply propext
  change (t : WithTop Nat) < FirstHittingTime Goal Path ↔ ¬Goal (Path t)
  rw [← not_le]
  apply not_congr
  rw [FirstHittingTimeLeIff]
  constructor
  . rintro ⟨s, Before, Reached⟩
    exact Nat.le_induction (P := fun u _ => Goal (Path u)) Reached
      (fun u _Between AtGoal => Preserved u AtGoal) t Before
  . intro Reached
    exact ⟨t, le_rfl, Reached⟩

/-- An absorbing goal and a local success bound yield survival contraction on the actual path law. -/
theorem PathGoalSurvivalStep {State : Type*} [MeasurableSpace State] [Fintype State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goal Valid : State -> Prop) [DecidablePred Goal] (p : I)
    (ValidPaths : ∀ t, ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (Absorption : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x -> Goal y)
    (Success : ∀ x, Valid x -> ¬Goal x -> (p : Real) ≤ (Step x).toMeasure.real {y | Goal y})
    (t : Nat) :
    (PathMeasure Step Initial).real {Path | ((t+1 : Nat) : WithTop Nat) < FirstHittingTime Goal Path} ≤
      (1-(p : Real)) * (PathMeasure Step Initial).real {Path | (t : WithTop Nat) < FirstHittingTime Goal Path} := by
  let V : State -> Real := fun x => if Goal x then 0 else 1
  have LocalMean (x : State) (IsValid : Valid x) :
      (∫ y, V y ∂(Step x).toMeasure) ≤ (1-(p : Real))*V x := by
    by_cases AtGoal : Goal x
    . have ZeroAE : V =ᵐ[(Step x).toMeasure] (fun _ => (0 : Real)) := by
        filter_upwards [Absorption x] with y Preserved
        exact if_pos (Preserved AtGoal)
      rw [integral_congr_ae ZeroAE, integral_zero]
      simp only [V, if_pos AtGoal, mul_zero, le_refl]
    . change (∫ y, (if Goal y then (0 : Real) else 1) ∂(Step x).toMeasure) ≤ _
      rw [GoalComplementIntegral]
      have Complement : {y | ¬Goal y} = {y | Goal y}ᶜ := rfl
      rw [Complement, probReal_compl_eq_one_sub (Set.to_countable _).measurableSet]
      simp only [V, if_neg AtGoal, mul_one]
      exact sub_le_sub_left (Success x IsValid AtGoal) 1
  have MeanRecurrence :
      (∫ Path, V (Path (t+1)) ∂PathMeasure Step Initial) ≤
        (1-(p : Real)) * (∫ Path, V (Path t) ∂PathMeasure Step Initial) := by
    rw [PathMeasureTransitionIntegral Step Initial t (fun _ y => V y), ← integral_const_mul]
    apply integral_mono_ae
      (PathMeasureCoordinateIntegrable Step Initial (fun x => ∫ y, V y ∂(Step x).toMeasure) t)
      ((PathMeasureCoordinateIntegrable Step Initial V t).const_mul _)
    filter_upwards [ValidPaths t] with Path IsValid
    exact LocalMean (Path t) IsValid
  have MeanAsProbability (s : Nat) :
      (∫ Path, V (Path s) ∂PathMeasure Step Initial) =
        (PathMeasure Step Initial).real {Path | ¬Goal (Path s)} := by
    have Integrands : (fun Path : Nat -> State => V (Path s)) =
        {Path | ¬Goal (Path s)}.indicator (fun _ => (1 : Real)) := by
      funext Path
      by_cases AtGoal : Goal (Path s)
      . simp only [V, Set.indicator_apply, Set.mem_ofPred_eq, AtGoal, not_true_eq_false, if_false, if_true]
      . simp only [V, Set.indicator_apply, Set.mem_ofPred_eq, AtGoal, not_false_eq_true, if_true, if_false]
    rw [Integrands]
    have Coordinate : Measurable (fun Path : Nat → State => Path s) := measurable_pi_apply s
    exact integral_indicator_one (Coordinate (Set.to_countable {x | ¬Goal x}).measurableSet)
  rw [MeanAsProbability (t+1), MeanAsProbability t] at MeanRecurrence
  change ((PathMeasure Step Initial) _).toReal ≤ _
  rw [PathGoalTail Step Initial Goal Absorption (t+1)]
  change _ ≤ (1-(p : Real))*((PathMeasure Step Initial) _).toReal
  rw [PathGoalTail Step Initial Goal Absorption t]
  exact MeanRecurrence


/-- A finite-state transition model inherits the geometric waiting bound after its invariant is verified. -/
theorem PathWaitingGeometricDomination {State : Type*} [MeasurableSpace State] [Fintype State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goal Valid : State -> Prop) [DecidablePred Goal] (p : I) (Positive : 0 < (p : Real))
    (ValidPaths : ∀ t, ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (Absorption : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x -> Goal y)
    (Success : ∀ x, Valid x -> ¬Goal x -> (p : Real) ≤ (Step x).toMeasure.real {y | Goal y}) :
    StochasticDominated ((PathMeasure Step Initial).map (FirstHittingTime Goal))
      ((geometricMeasure p).map (fun j : Nat => ((j+1 : Nat) : WithTop Nat))) := by
  apply WaitingGeometricDomination (PathMeasure Step Initial) (FirstHittingTime Goal)
    (FirstHittingTimeMeasurable Goal) p Positive
  intro t Nonzero
  apply WaitingHazardOfSurvivalStep _ _ (FirstHittingTimeMeasurable Goal) p t Nonzero
  exact PathGoalSurvivalStep Step Initial Goal Valid p ValidPaths Absorption Success t

/-- The actual first-hitting-time expectation is at most the reciprocal success probability. -/
theorem PathWaitingExpectedRuntime {State : Type*} [MeasurableSpace State] [Fintype State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goal Valid : State -> Prop) [DecidablePred Goal] (p : I) (Positive : 0 < (p : Real))
    (ValidPaths : ∀ t, ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (Absorption : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x -> Goal y)
    (Success : ∀ x, Valid x -> ¬Goal x -> (p : Real) ≤ (Step x).toMeasure.real {y | Goal y}) :
    ExpectedHittingTime Step Goal Initial ≤ ENNReal.ofReal (1/(p : Real)) := by
  apply WaitingExpectationBound (PathMeasure Step Initial) (FirstHittingTime Goal)
    (FirstHittingTimeMeasurable Goal) p Positive
  intro t Nonzero
  apply WaitingHazardOfSurvivalStep _ _ (FirstHittingTimeMeasurable Goal) p t Nonzero
  exact PathGoalSurvivalStep Step Initial Goal Valid p ValidPaths Absorption Success t


/-- An explicit tail bound, including the initial time and a zero success parameter. -/
theorem PathWaitingSurvivalBound {State : Type*} [MeasurableSpace State] [Fintype State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (Goal Valid : State → Prop) [DecidablePred Goal] (p : I)
    (ValidPaths : ∀ t, ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (Absorption : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x → Goal y)
    (Success : ∀ x, Valid x → ¬Goal x → (p : ℝ) ≤ (Step x).toMeasure.real {y | Goal y})
    (t : ℕ) :
    (PathMeasure Step Initial).real {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path} ≤
      (1-(p : ℝ))^t := by
  apply WaitingSurvivalBound (PathMeasure Step Initial) (FirstHittingTime Goal)
    (FirstHittingTimeMeasurable Goal) p _ t
  intro s Nonzero
  apply WaitingHazardOfSurvivalStep _ _ (FirstHittingTimeMeasurable Goal) p s Nonzero
  exact PathGoalSurvivalStep Step Initial Goal Valid p ValidPaths Absorption Success s

end
end ECTheoryLib.Tools.Runtime
