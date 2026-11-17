import ECTheoryLib.Probability.Processes.BoundedPathDrift
import ECTheoryLib.Probability.Processes.PathInvariant

/-!
# Local drift inequalities and goal semantics on actual paths

The finite-state local inequality entry delegates to the bounded countable-state
bridge. A legal-state drift floor survives averaging on a positive-probability
potential level; the potential need not determine the exact drift or itself be
a Markov chain. Zero absorption and equality of goal/potential hitting times only
require countable full states. Legality and absorption use almost-sure conditions;
the finite-range convention belongs to the scalar drift theorem and is unchanged.
-/
namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section

variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

section FiniteState
variable [Fintype State]

/-- Any real function of a finite-state coordinate is integrable on paths. -/
theorem PathMeasureCoordinateIntegrable (Step : Transition State) (Initial : PMF State)
    (f : State → ℝ) (t : Nat) :
    Integrable (fun Path : Nat → State => f (Path t)) (PathMeasure Step Initial) := by
  classical
  apply FiniteStateIntegrable (PathMeasure Step Initial) _ (Finset.univ.image f)
  · exact (measurable_of_finite f).comp (measurable_pi_apply t)
  · apply ae_of_all
    intro Path
    exact Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩

/-- A lower bound valid on legal nonzero states survives averaging over a potential
level. Only the conditioning event's positive probability is required. -/
theorem PathMeasureStateDriftLowerBound (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (d : ℝ → ℝ) (Valid : State → Prop)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      d (V x) ≤ ∫ y, V x - V y ∂(Step x).toMeasure)
    (t : Nat) (s : ℝ) (Nonzero : s ≠ 0)
    (ValidAtTime : ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (EventPositive : 0 < (PathMeasure Step Initial)
      (StateEvent (fun t Path => V (Path t)) t s)) :
    d s ≤ StateDrift (PathMeasure Step Initial) (fun t Path => V (Path t)) t s := by
  classical
  exact PathMeasureStateDriftLowerBoundOfBounded Step Initial V d Valid
    (Finset.univ.sum (fun x : State => norm (V x)))
    (fun x => Finset.single_le_sum (fun y _ => norm_nonneg (V y)) (Finset.mem_univ x))
    LocalDrift t s Nonzero ValidAtTime EventPositive

end FiniteState

/-- Zero absorption is inherited from a supported transition property, including
countably infinite representations such as lists of finite search points. -/
theorem PathMeasureZeroIsAbsorbing (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Valid : State → Prop)
    (ValidOnPaths : ∀ t, ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure,
      Valid x → V x = 0 → V y = 0) :
    ZeroIsAbsorbing (PathMeasure Step Initial) (fun t Path => V (Path t)) := by
  intro t
  have Follows := PathMeasureFollowsTransition Step Initial
    (fun x y => Valid x → V x = 0 → V y = 0) PreservesZero t
  filter_upwards [ValidOnPaths t, Follows] with Path IsValid IsPreserved
  exact IsPreserved IsValid

/-- A potential characterizing the goal gives exactly the same first hitting time. -/
theorem ExpectedHittingTimeEqExpectedZero (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal : State → Prop)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x) :
    ExpectedHittingTime Step Goal Initial =
      ExpectedZeroHittingTime (PathMeasure Step Initial) (fun t Path => V (Path t)) := by
  have HittingEquality : ∀ Path : Nat → State,
      ZeroHittingTime (fun t Path => V (Path t)) Path = FirstHittingTime Goal Path := by
    intro Path
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [Set.mem_ofPred_eq]
    simp_rw [ZeroIffGoal]
    have SameExistence : (∃ j, 0 ≤ j ∧ V (Path j) = 0) ↔
        (∃ j, 0 ≤ j ∧ Goal (Path j)) := by
      constructor
      · rintro ⟨j, Nonnegative, Zero⟩
        exact ⟨j, Nonnegative, (ZeroIffGoal (Path j)).mp Zero⟩
      · rintro ⟨j, Nonnegative, Reached⟩
        exact ⟨j, Nonnegative, (ZeroIffGoal (Path j)).mpr Reached⟩
    by_cases Reached : ∃ j, 0 ≤ j ∧ Goal (Path j)
    · rw [if_pos (SameExistence.mpr Reached), if_pos Reached]
    · have NotZero : ¬ ∃ j, 0 ≤ j ∧ V (Path j) = 0 := by
        intro ZeroReached
        exact Reached (SameExistence.mp ZeroReached)
      rw [if_neg NotZero, if_neg Reached]
  unfold ExpectedHittingTime ExpectedZeroHittingTime
  apply lintegral_congr
  intro Path
  rw [HittingEquality]
  rfl

end
end ECTheoryLib.Probability
