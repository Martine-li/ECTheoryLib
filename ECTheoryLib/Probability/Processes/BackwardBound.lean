import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Probability.Processes.PathDrift

/-!
# Backward bounds for actual finite-state trajectories

Local backward inequalities telescope through the existing Markov path
measure. Goal absorption is proved separately before replacing a
first-hitting event by current-state goal membership.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Local backward inequalities telescope through the actual kernel law.
Finite state supplies the integrability obligations. -/
theorem PathMeasureBackwardIntegralBound (Step : Transition State) (Initial : PMF State)
    (f : ℕ → State → ℝ)
    (Local : ∀ r x, (∫ y, f r y ∂(Step x).toMeasure)≤f (r+1) x)
    (r t : ℕ) :
    (∫ Path, f r (Path t) ∂PathMeasure Step Initial)≤
      ∫ x, f (r+t) x ∂Initial.toMeasure := by
  induction t generalizing r with
  | zero =>
    rw [PathMeasureInitialIntegral]
    exact le_rfl
  | succ t Before =>
    rw [PathMeasureTransitionIntegral Step Initial t (fun _ y => f r y)]
    apply (integral_mono
      (PathMeasureCoordinateIntegrable Step Initial (fun x => ∫ y, f r y ∂(Step x).toMeasure) t)
      (PathMeasureCoordinateIntegrable Step Initial (f (r+1)) t)
      (fun Path => Local r (Path t))).trans
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Before (r+1)

/-- Absorbing goal membership identifies first-hit and current-state events. -/
theorem PathMeasureAbsorbingGoalIffHit (Step : Transition State) (Initial : PMF State)
    (Goal : State → Prop)
    (Absorbing : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x → Goal y) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure Step Initial, FirstHittingTime Goal Path≤(t : WithTop ℕ) ↔ Goal (Path t) := by
  have Follows : ∀ᵐ Path ∂PathMeasure Step Initial, ∀ j, Goal (Path j) → Goal (Path (j+1)) :=
    ae_all_iff.mpr (fun j => PathMeasureFollowsTransition Step Initial
      (fun x y => Goal x → Goal y) Absorbing j)
  filter_upwards [Follows] with Path Preserves
  rw [FirstHittingTimeLeIff]
  constructor
  · rintro ⟨j,Before,Reached⟩
    induction t,Before using Nat.le_induction with
    | base => exact Reached
    | succ t _ Previous => exact Preserves t Previous
  · exact fun Reached => ⟨t,le_rfl,Reached⟩

/-- A backward family with the goal indicator at horizon zero gives an
actual first-hitting lower-tail bound, not a bound on a surrogate chain. -/
theorem FirstHittingProbabilityOfBackwardBound (Step : Transition State) (Initial : PMF State)
    (Goal : State → Prop)
    (Absorbing : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Goal x → Goal y)
    (f : ℕ → State → ℝ)
    (Terminal : f 0={x | Goal x}.indicator (fun _ => (1 : ℝ)))
    (Local : ∀ r x, (∫ y, f r y ∂(Step x).toMeasure)≤f (r+1) x) (t : ℕ) :
    (PathMeasure Step Initial).real {Path | FirstHittingTime Goal Path≤(t : WithTop ℕ)}≤
      ∫ x, f t x ∂Initial.toMeasure := by
  have Bound := PathMeasureBackwardIntegralBound Step Initial f Local 0 t
  rw [Nat.zero_add,Terminal] at Bound
  have Events : {Path | FirstHittingTime Goal Path≤(t : WithTop ℕ)}=ᵐ[PathMeasure Step Initial]
      {Path | Goal (Path t)} := by
    filter_upwards [PathMeasureAbsorbingGoalIffHit Step Initial Goal Absorbing t] with Path Equal
    exact propext Equal
  have Indicator : (fun Path : ℕ → State => {x | Goal x}.indicator (fun _ => (1 : ℝ)) (Path t))=
      {Path | Goal (Path t)}.indicator (fun _ => (1 : ℝ)) := by
    funext Path
    rfl
  have EventMeasurable : MeasurableSet {Path : ℕ → State | Goal (Path t)} :=
    (Set.to_countable {x | Goal x}).measurableSet.preimage (measurable_pi_apply t)
  rw [Indicator,integral_indicator_const _ EventMeasurable,smul_eq_mul,mul_one] at Bound
  unfold Measure.real at Bound ⊢
  rwa [measure_congr Events]

end
end ECTheoryLib.Probability
