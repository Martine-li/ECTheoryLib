import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.Processes.ScalarProcess
import ECTheoryLib.Probability.HittingTimes.Expectation

/-!
# Initial-state semantics and exact finite-state drift

Initialization may be any PMF. An exact local drift depending only on the potential
value is lifted to drift conditioned on a potential-level event. Finite state
provides integrability for that exact drift rule. Initial means and initially
successful hitting times only require countable states with measurable singletons.
No positive drift, absorption, or finite
expected runtime is assumed; no concrete runtime bound is asserted here.
-/

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- A fixed initially successful state has hitting time zero almost surely;
absorption after success is unnecessary for this first-hit statement. -/
theorem FirstHittingTimeOfPureTarget (Step : Transition State) (Goal : State → Prop)
    (InitialState : State) (InitialTarget : Goal InitialState) :
    ∀ᵐ Path ∂PathMeasure Step (PMF.pure InitialState), FirstHittingTime Goal Path = 0 := by
  filter_upwards [PathMeasureInitialPure Step InitialState] with Path InitialFixed
  apply (FirstHittingTimeEqZeroIff Goal Path).mpr
  rw [InitialFixed]
  exact InitialTarget

/-- An initially successful fixed state has zero extended expected hitting time. -/
theorem ExpectedHittingTimeOfPureTarget (Step : Transition State) (Goal : State → Prop)
    (InitialState : State) (InitialTarget : Goal InitialState) :
    ExpectedHittingTime Step Goal (PMF.pure InitialState) = 0 := by
  have ValueZero : ∀ᵐ Path ∂PathMeasure Step (PMF.pure InitialState),
      FirstHittingTimeValue Goal Path = 0 := by
    filter_upwards [FirstHittingTimeOfPureTarget Step Goal InitialState InitialTarget]
      with Path TimeZero
    unfold FirstHittingTimeValue
    rw [TimeZero]
    exact ENat.toENNReal_zero
  unfold ExpectedHittingTime
  calc
    (∫⁻ Path, FirstHittingTimeValue Goal Path ∂PathMeasure Step (PMF.pure InitialState)) =
        ∫⁻ _Path, (0 : ENNReal) ∂PathMeasure Step (PMF.pure InitialState) := by
      exact lintegral_congr_ae ValueZero
    _ = 0 := by
      exact lintegral_zero

/-- For a pure initial law, the initial expectation is the function's value at that state. -/
theorem PathMeasurePureInitialIntegral (Step : Transition State) (x : State)
    (f : State → ℝ) :
    (∫ Path, f (Path 0) ∂PathMeasure Step (PMF.pure x)) = f x := by
  rw [PathMeasureInitialIntegral Step (PMF.pure x) f]
  rw [PMF.toMeasure_pure, integral_dirac]

/-- Exact local drift `d (V x)` yields conditional drift `d s` on the event
`V(X_t)=s`. The event must have positive probability; no runtime conclusion is a premise. -/
theorem PathMeasureStateDrift [Fintype State] (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (d : ℝ → ℝ)
    (LocalDrift : ∀ x, (∫ y, V x - V y ∂(Step x).toMeasure) = d (V x))
    (t : Nat) (s : ℝ)
    (EventPositive : 0 < (PathMeasure Step Initial)
      (StateEvent (fun t Path => V (Path t)) t s)) :
    StateDrift (PathMeasure Step Initial) (fun t Path => V (Path t)) t s = d s := by
  classical
  let μ := PathMeasure Step Initial
  let X : Nat → (Nat → State) → ℝ := fun t Path => V (Path t)
  let Event := StateEvent X t s
  have EventMeasurable : MeasurableSet Event := by
    apply StateEventMeasurable
    exact (measurable_of_finite V).comp (measurable_pi_apply t)
  let EventDecrease : State → State → ℝ :=
    fun x y => if V x = s then V x - V y else 0
  have Numerator :
      (∫ Path in Event, X t Path - X (t + 1) Path ∂μ) =
        (μ Event).toReal * d s := by
    rw [← integral_indicator EventMeasurable]
    change (∫ Path, EventDecrease (Path t) (Path (t + 1)) ∂μ) = _
    have TransitionIntegral :
        (∫ Path, EventDecrease (Path t) (Path (t + 1)) ∂μ) =
          ∫ Path, (∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure) ∂μ := by
      exact PathMeasureTransitionIntegral Step Initial t EventDecrease
    rw [TransitionIntegral]
    have ConditionalAverage : ∀ x : State,
        (∫ y, EventDecrease x y ∂(Step x).toMeasure) =
          if V x = s then d s else 0 := by
      intro x
      unfold EventDecrease
      by_cases CurrentPotential : V x = s
      · simp only [if_pos CurrentPotential]
        rw [LocalDrift x, CurrentPotential]
      · simp only [if_neg CurrentPotential, integral_zero]
    have AverageAsIndicator :
        (fun Path : Nat → State =>
          ∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure) =
            Event.indicator (fun _ => d s) := by
      funext Path
      rw [ConditionalAverage]
      rfl
    rw [AverageAsIndicator, integral_indicator_const _ EventMeasurable]
    rfl
  change (∫ Path in Event, X t Path - X (t + 1) Path ∂μ) / (μ Event).toReal = _
  rw [Numerator]
  have EventRealNonzero : (μ Event).toReal ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.toReal_pos EventPositive.ne' (measure_ne_top μ Event)
  exact mul_div_cancel_left₀ (d s) EventRealNonzero

end
end ECTheoryLib.Probability
