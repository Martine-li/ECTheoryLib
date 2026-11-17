import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative
import ECTheoryLib.Analysis.RandomSearch.RuntimeBounds

/-!
# Failure potential on actual random-search paths

Integrability, complete-history and surviving-level drift, initialization
and first-hit identity are shared by expectation and tail analyses.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem PathPotentialIntegrable (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal] (t : ℕ) :
    Integrable (fun Path => Potential Goal (Path t)) (PathMeasure (IndependentRandomSearchStep Samples) Initial) :=
  FiniteStateIntegrable _ _ {0,1} (CountablePathPotentialAdapted (Potential Goal)).measurable
    (ae_of_all _ (fun Path => PotentialValues Goal (Path t)))

theorem PathConditionalSuccessDrift (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal] (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (IndependentRandomSearchStep Samples) Initial, ¬Goal (Path t) →
      ((PathMeasure (IndependentRandomSearchStep Samples) Initial)[fun Path => Potential Goal (Path t)-Potential Goal (Path (t+1)) |
          Filtration.piLE (X := fun _ : ℕ => State) t]) Path = Samples.toMeasure.real {y | Goal y} := by
  have Conditional := PathMeasureStateConditionalExpectationOfIntegrable (IndependentRandomSearchStep Samples) Initial t
    (fun x y => Potential Goal x-Potential Goal y)
    ((PathPotentialIntegrable Samples Initial Goal t).sub (PathPotentialIntegrable Samples Initial Goal (t+1)))
  filter_upwards [Conditional] with Path Equal
  intro Away
  rw [Equal,OneStepDrift Samples Goal (Path t) Away]

theorem InitialFailurePotential (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState) :
    ∀ᵐ Path ∂PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState), Potential Goal (Path 0)=1 := by
  have Mapped : ∀ᵐ x ∂(PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)).map
      (fun Path : ℕ → State => Path 0), x=InitialState := by
    rw [PathMeasureInitial,PMF.toMeasure_pure]
    exact ae_eq_dirac (fun x : State => x)
  have Initial := ae_of_ae_map (measurable_pi_apply 0).aemeasurable Mapped
  filter_upwards [Initial] with Path Equal
  simp [Equal,Potential,Away]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
theorem FailurePotentialHittingTime (Goal : State → Prop) [DecidablePred Goal] (Path : ℕ → State) :
    ZeroHittingTime (fun j Path => Potential Goal (Path j)) Path=FirstHittingTime Goal Path := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  have Left := FirstHittingTimeLeIff (fun s : ℝ => s=0) (fun j => Potential Goal (Path j)) t
  have Right := FirstHittingTimeLeIff Goal Path t
  refine Left.trans (Iff.trans ?_ Right.symm)
  simp [Potential]

end
end ECTheoryLib.Analysis.RandomSearch

namespace ECTheoryLib.Analysis.RandomSearch

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift

noncomputable section

variable {State : Type*} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- The actual random-search law satisfies surviving-level drift with its true
one-step success mass. No successful initialization, positive success mass,
absorbing target, or supplied abstract history law is required for this bridge. -/
theorem PathSurvivingSuccessDrift (Samples Initial : PMF State)
    (Goal : State → Prop) [DecidablePred Goal] (t : ℕ) (s : ℝ)
    (Nonzero : s ≠ 0)
    (Positive : 0 < (PathMeasure (IndependentRandomSearchStep Samples) Initial)
      {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧
        Potential Goal (Path t) = s}) :
    Samples.toMeasure.real {y | Goal y} * s ≤
      EventConditionalExpectation (PathMeasure (IndependentRandomSearchStep Samples) Initial)
        (fun Path => Potential Goal (Path t) - Potential Goal (Path (t + 1)))
        {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧
          Potential Goal (Path t) = s} := by
  let μ := PathMeasure (IndependentRandomSearchStep Samples) Initial
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => State)
  have AdaptedX : Adapted F X := CountablePathPotentialAdapted (Potential Goal)
  have NonnegativeRange : ∀ u ∈ ({0, 1} : Finset ℝ), 0 ≤ u := by
    intro u Member
    simp only [Finset.mem_insert, Finset.mem_singleton] at Member
    rcases Member with rfl | rfl <;> norm_num
  have Values : ∀ j Path, X j Path ∈ ({0, 1} : Finset ℝ) :=
    fun j Path => PotentialValues Goal (Path j)
  have Pointwise : ∀ j Path, 0 ≤ X j Path :=
    fun j Path => NonnegativeRange _ (Values j Path)
  have Times : ZeroHittingTime X = FirstHittingTime Goal :=
    funext (FailurePotentialHittingTime Goal)
  have Event : StateEvent (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s =
      {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧
        Potential Goal (Path t) = s} := by
    rw [StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero, Times]
  have PositiveStopped :
      0 < μ (StateEvent (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s) := by
    rw [Event]
    exact Positive
  have Bound := StoppedStateDriftLowerBoundOfCondExp μ X F AdaptedX {0, 1}
    NonnegativeRange Values (fun u => Samples.toMeasure.real {y | Goal y} * u) (by
      intro j
      filter_upwards [PathConditionalSuccessDrift Samples Initial Goal j] with Path Conditional
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        exact Active (by simp [X, Potential, Reached])
      rw [Conditional NotGoal]
      simp [X, Potential, NotGoal]) t s Nonzero PositiveStopped
  rw [StoppedStateDriftEqSurvivingEventExpectation μ X
    (fun _ => AdaptedX.measurable) Pointwise t s Nonzero, Times] at Bound
  exact Bound

end

end ECTheoryLib.Analysis.RandomSearch

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Exact mean on the actual surviving-level event, for arbitrary initialization
and success mass including zero. No runtime formula or absorption is assumed. -/
theorem PathSurvivingSuccessDriftExact (Samples Initial : PMF State)
    (Goal : State → Prop) [DecidablePred Goal] (t : ℕ) (s : ℝ)
    (Nonzero : s ≠ 0)
    (Positive : 0 < (PathMeasure (IndependentRandomSearchStep Samples) Initial)
      {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧ Potential Goal (Path t) = s}) :
    EventConditionalExpectation (PathMeasure (IndependentRandomSearchStep Samples) Initial)
      (fun Path => Potential Goal (Path t) - Potential Goal (Path (t + 1)))
      {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧ Potential Goal (Path t) = s} =
        Samples.toMeasure.real {y | Goal y} * s := by
  let μ := PathMeasure (IndependentRandomSearchStep Samples) Initial
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => State)
  have AdaptedX : Adapted F X := CountablePathPotentialAdapted (Potential Goal)
  have NonnegativeRange : ∀ u ∈ ({0, 1} : Finset ℝ), 0 ≤ u := by
    intro u Member
    simp only [Finset.mem_insert, Finset.mem_singleton] at Member
    rcases Member with rfl | rfl <;> norm_num
  have Values : ∀ j Path, X j Path ∈ ({0, 1} : Finset ℝ) :=
    fun j Path => PotentialValues Goal (Path j)
  have Pointwise : ∀ j Path, 0 ≤ X j Path := fun j Path => NonnegativeRange _ (Values j Path)
  have Times : ZeroHittingTime X = FirstHittingTime Goal := funext (FailurePotentialHittingTime Goal)
  have Event : StateEvent (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s =
      {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path ∧ Potential Goal (Path t) = s} := by
    rw [StoppedNonzeroStateEventEqSurviving X Pointwise t s Nonzero, Times]
  have PositiveStopped : 0 < μ (StateEvent (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s) := by
    rw [Event]
    exact Positive
  have Upper := StoppedStateDriftUpperBoundOfCondExp μ X F AdaptedX {0, 1}
    NonnegativeRange Values (fun u => Samples.toMeasure.real {y | Goal y} * u) (by
      intro j
      filter_upwards [PathConditionalSuccessDrift Samples Initial Goal j] with Path Conditional
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        exact Active (by simp [X, Potential, Reached])
      rw [Conditional NotGoal]
      simp [X, Potential, NotGoal]) t s Nonzero PositiveStopped
  rw [StoppedStateDriftEqSurvivingEventExpectation μ X
    (fun _ => AdaptedX.measurable) Pointwise t s Nonzero, Times] at Upper
  exact le_antisymm Upper (PathSurvivingSuccessDrift Samples Initial Goal t s Nonzero Positive)

end
end ECTheoryLib.Analysis.RandomSearch
