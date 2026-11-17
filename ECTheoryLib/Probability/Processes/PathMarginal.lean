import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.PMF.FinitePMF

/-!
# Marginal laws of finite-state trajectories

The existing Mathlib-backed trajectory construction and the iterated PMF
transition Evolve describe the same state distribution at every natural time.
The proof reuses one-step total expectation, PMF bind integration, and Mathlib
measure extensionality. The initial law is arbitrary. Finite state makes all
real observables integrable; no runtime or absorbing-target premise is needed.

This is a marginal identity for the existing joint path law. It does not
construct a joint law from marginals or assert that a projected potential
process is Markov. Current-state events require a separate absorption argument
if they are to be identified with first-hitting events.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Expectations at any trajectory coordinate equal the iterated finite-step law. -/
theorem PathMeasureMarginalIntegral (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : State → ℝ) :
    (∫ Path, f (Path t) ∂PathMeasure Step Initial) =
      ∫ x, f x ∂(Evolve Step Initial t).toMeasure := by
  induction t generalizing f with
  | zero => exact PathMeasureInitialIntegral Step Initial f
  | succ t Before =>
    rw [PathMeasureTransitionIntegral Step Initial t (fun _ y => f y)]
    rw [Before (fun x => ∫ y, f y ∂(Step x).toMeasure)]
    rw [Evolve, PMFIntegralBind, PMF.integral_eq_sum]
    rfl

/-- The full trajectory and iterated transition PMF have the same time-t marginal law. -/
theorem PathMeasureMarginal (Step : Transition State) (Initial : PMF State) (t : ℕ) :
    (PathMeasure Step Initial).map (fun Path => Path t) = (Evolve Step Initial t).toMeasure := by
  have IntegralEq (f : State → ℝ) :
      (∫ x, f x ∂(PathMeasure Step Initial).map (fun Path => Path t)) =
        ∫ x, f x ∂(Evolve Step Initial t).toMeasure := by
    rw [integral_map_of_stronglyMeasurable (measurable_pi_apply t)
      (measurable_of_finite f).stronglyMeasurable]
    exact PathMeasureMarginalIntegral Step Initial t f
  apply Measure.ext_of_measureReal_singleton
  intro x
  have Equality := IntegralEq (({x} : Set State).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const _ (measurableSet_singleton _),
    integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at Equality
  exact Equality

/-- Any current-state event can be checked in the finite-step PMF. -/
theorem PathMeasureCoordinateEvent (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (A : Set State) :
    (PathMeasure Step Initial) {Path | Path t ∈ A} = (Evolve Step Initial t).toMeasure A := by
  have Equal := congrArg (fun μ : Measure State => μ A) (PathMeasureMarginal Step Initial t)
  rw [Measure.map_apply (measurable_pi_apply t) (Set.to_countable _).measurableSet] at Equal
  exact Equal

end
end ECTheoryLib.Probability
