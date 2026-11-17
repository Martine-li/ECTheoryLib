import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.HittingTimes.HittingTime
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# One-step progress and expected first hitting times

Potential differences are real-valued and may be negative. Runtime is integrated
in `ENNReal`, preserving both nontermination and divergent expected time. Time
zero is initialization, and the unit is transitions. `ExpectedDecreaseEqIntegral`
connects the finite-sum local API with mathlib's integral representation.
-/

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

/-- Embed the first hitting time into the extended nonnegative reals, preserving infinity. -/
def FirstHittingTimeValue {State : Type*} (Goal : State → Prop)
    (Path : Nat → State) : ENNReal :=
  ENat.toENNReal (FirstHittingTime Goal Path)

section Measurability

variable {State : Type*} [MeasurableSpace State] [Countable State]
  [MeasurableSingletonClass State]

/-- The first hitting time is measurable on a countable discrete state space. -/
theorem FirstHittingTimeMeasurable (Goal : State → Prop) :
    Measurable (FirstHittingTime Goal) := by
  have GoalMeasurable : MeasurableSet {x : State | Goal x} := by
    exact (Set.to_countable _).measurableSet
  exact FirstHittingTimeProcessMeasurable Goal
    (fun t (Path : Nat → State) => Path t) GoalMeasurable measurable_pi_apply

/-- The extended-valued hitting-time function is measurable for nonnegative integration. -/
theorem FirstHittingTimeValueMeasurable (Goal : State → Prop) :
    Measurable (FirstHittingTimeValue Goal) := by
  have ConversionMeasurable :
      Measurable (fun t : WithTop Nat => ENat.toENNReal t) := by
    exact measurable_of_countable _
  unfold FirstHittingTimeValue
  exact ConversionMeasurable.comp (FirstHittingTimeMeasurable Goal)

/-- Integrate the first hitting time under the actual path law. Finiteness is not assumed. -/
def ExpectedHittingTime (Step : Transition State) (Goal : State → Prop)
    (Initial : PMF State) : ENNReal :=
  ∫⁻ Path, FirstHittingTimeValue Goal Path ∂PathMeasure Step Initial

end Measurability

/-- Expected signed potential decrease from a fixed current state.
Each PMF point mass is finite, so its real conversion is valid. Negative progress is allowed. -/
def ExpectedDecrease {State : Type*} [Fintype State]
    (Step : Transition State) (Potential : State → ℝ) (x : State) : ℝ :=
  ∑ y : State, (Step x y).toReal * (Potential x - Potential y)

/-- The finite-sum progress API equals the PMF-measure integral.
This bridge uses `PMF.integral_eq_sum` and permits either representation in applications. -/
theorem ExpectedDecreaseEqIntegral {State : Type*} [Fintype State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (Step : Transition State) (Potential : State → ℝ) (x : State) :
    ExpectedDecrease Step Potential x =
      ∫ y, Potential x - Potential y ∂(Step x).toMeasure := by
  rw [PMF.integral_eq_sum]
  unfold ExpectedDecrease
  apply Finset.sum_congr rfl
  intro y _InStateSpace
  exact (smul_eq_mul (Step x y).toReal (Potential x - Potential y)).symm

end

end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Markov's inequality applied to the extended first-hit time, retaining infinity. -/
theorem FirstHittingTimeTailOfExpected (Step : Transition State) (Initial : PMF State)
    (Goal : State → Prop) (t : ℕ) (Positive : 0<t) :
    (PathMeasure Step Initial) {Path | (t : WithTop ℕ)<FirstHittingTime Goal Path} ≤
      ExpectedHittingTime Step Goal Initial/(t : ENNReal) := by
  have Markov := meas_ge_le_lintegral_div
    (μ := PathMeasure Step Initial) (FirstHittingTimeValueMeasurable Goal).aemeasurable
    (ε := (t : ENNReal)) (by exact_mod_cast Positive.ne') (by simp)
  apply le_trans (measure_mono ?_) Markov
  intro Path Late
  change ENat.toENNReal (t : WithTop ℕ)≤ENat.toENNReal (FirstHittingTime Goal Path)
  exact ENat.toENNReal_mono Late.le

end
end ECTheoryLib.Probability
