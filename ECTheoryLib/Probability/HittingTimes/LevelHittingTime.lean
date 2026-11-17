import ECTheoryLib.Probability.HittingTimes.HittingTime
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Entry times and stage durations for nested goals

Time zero is initialization. Durations use Mathlib extended-natural truncated
subtraction, so infinity minus infinity is zero. The first infinite stage is
retained in the total sum; no infinite runtime is converted to a real zero.
The telescoping proof uses add_tsub_cancel_of_le; the more general Mathlib
Finset.sum_range_tsub requires cancellation unavailable at infinity.

Goal sets are nested, but trajectories need not be monotone or absorbing.
Measurability holds for general measurable state spaces and processes.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section


/-- Reaching a smaller goal set cannot occur before reaching the containing set. -/
theorem FirstHittingTimeOfNestedGoals {State : Type*} (Earlier Later : State → Prop)
    (Nested : ∀ x, Later x → Earlier x) (Path : ℕ → State) :
    FirstHittingTime Earlier Path ≤ FirstHittingTime Later Path := by
  cases Value : FirstHittingTime Later Path using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
      change FirstHittingTime Earlier Path ≤ (t : WithTop ℕ)
      have LaterByTime : FirstHittingTime Later Path ≤ (t : WithTop ℕ) := by
        rw [Value]
        exact le_rfl
      obtain ⟨s, Before, Reached⟩ := (FirstHittingTimeLeIff Later Path t).mp LaterByTime
      apply (FirstHittingTimeLeIff Earlier Path t).mpr
      exact ⟨s, Before, Nested (Path s) Reached⟩

/-- Successive entry-time difference in extended naturals; skipped and unreachable later stages have duration zero. -/
def LevelDuration {State : Type*} (Goals : ℕ → State → Prop) (i : ℕ)
    (Path : ℕ → State) : WithTop ℕ :=
  FirstHittingTime (Goals (i+1)) Path - FirstHittingTime (Goals i) Path

/-- Entry times into nested goal sets are nondecreasing even if the trajectory can leave those sets. -/
theorem LevelEntryMonotone {State : Type*} (Goals : ℕ → State → Prop)
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Path : ℕ → State) :
    Monotone (fun i => FirstHittingTime (Goals i) Path) := by
  apply monotone_nat_of_le_succ
  intro i
  exact FirstHittingTimeOfNestedGoals (Goals i) (Goals (i+1)) (Nested i) Path

/-- The durations telescope to the final first-hitting time, with no termination assumption. -/
theorem LevelDurationSum {State : Type*} (Goals : ℕ → State → Prop)
    (Nested : ∀ i x, Goals (i+1) x → Goals i x)
    (Initially : ∀ x, Goals 0 x) (Path : ℕ → State) (n : ℕ) :
    (∑ i ∈ Finset.range n, LevelDuration Goals i Path) = FirstHittingTime (Goals n) Path := by
  have InitialTime : FirstHittingTime (Goals 0) Path = 0 :=
    (FirstHittingTimeEqZeroIff _ _).mpr (Initially (Path 0))
  induction n with
  | zero => rw [Finset.range_zero, Finset.sum_empty, InitialTime]
  | succ n InductionHypothesis =>
      rw [Finset.sum_range_succ, InductionHypothesis]
      unfold LevelDuration
      exact add_tsub_cancel_of_le (LevelEntryMonotone Goals Nested Path (Nat.le_succ n))

/-- Stage durations are measurable for any measurable process and measurable goal sets. -/
theorem LevelDurationMeasurable {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ i, MeasurableSet {x | Goals i x})
    (X : ℕ → Ω → State) (MeasurableX : ∀ t, Measurable (X t)) (i : ℕ) :
    Measurable (fun ω => LevelDuration Goals i (fun t => X t ω)) := by
  have First := FirstHittingTimeProcessMeasurable (Goals i) X (GoalMeasurable i) MeasurableX
  have Next := FirstHittingTimeProcessMeasurable (Goals (i+1)) X (GoalMeasurable (i+1)) MeasurableX
  exact (measurable_of_countable (fun p : WithTop ℕ × WithTop ℕ => p.1-p.2)).comp (Next.prodMk First)

/-- The formal duration after an infinite entry is zero by extended subtraction.
For nested goals, the earlier infinite stage remains in the total sum. -/
theorem LevelDurationAfterInfiniteEntry {State : Type*} (Goals : ℕ → State → Prop)
    (i : ℕ) (Path : ℕ → State) (NeverEntered : FirstHittingTime (Goals i) Path = ⊤) :
    LevelDuration Goals i Path = 0 := by
  unfold LevelDuration
  rw [NeverEntered, WithTop.sub_top]
  rfl

theorem LevelDurationOfSkippedLevel {State : Type*} (Goals : ℕ → State → Prop)
    (i : ℕ) (Path : ℕ → State)
    (SameEntry : FirstHittingTime (Goals (i+1)) Path = FirstHittingTime (Goals i) Path) :
    LevelDuration Goals i Path = 0 := by
  unfold LevelDuration
  rw [SameEntry, tsub_self]

/-- The first entry time plus the subsequent duration equals the total time, including infinite times. -/
theorem NestedGoalTimeDecomposition {State : Type*} (Earlier Later : State → Prop)
    (Nested : ∀ x, Later x → Earlier x) (Path : ℕ → State) :
    FirstHittingTime Earlier Path + (FirstHittingTime Later Path - FirstHittingTime Earlier Path) =
      FirstHittingTime Later Path := by
  exact add_tsub_cancel_of_le (FirstHittingTimeOfNestedGoals Earlier Later Nested Path)

/-- The two-phase expectation identity in ENNReal, with no integrability or finite-time assumption. -/
theorem NestedGoalExpectedTimeDecomposition {State : Type*} [MeasurableSpace State]
    (P : Measure (ℕ → State)) (Earlier Later : State → Prop)
    (EarlierMeasurable : MeasurableSet {x | Earlier x})
    (LaterMeasurable : MeasurableSet {x | Later x})
    (Nested : ∀ x, Later x → Earlier x) :
    (∫⁻ Path, ENat.toENNReal (FirstHittingTime Later Path) ∂P) =
      (∫⁻ Path, ENat.toENNReal (FirstHittingTime Earlier Path) ∂P) +
      ∫⁻ Path, ENat.toENNReal (FirstHittingTime Later Path - FirstHittingTime Earlier Path) ∂P := by
  have EarlierTimeMeasurable : Measurable (FirstHittingTime Earlier) :=
    FirstHittingTimeProcessMeasurable Earlier (fun t (Path : ℕ → State) => Path t)
      EarlierMeasurable measurable_pi_apply
  have LaterTimeMeasurable : Measurable (FirstHittingTime Later) :=
    FirstHittingTimeProcessMeasurable Later (fun t (Path : ℕ → State) => Path t)
      LaterMeasurable measurable_pi_apply
  have RemainingMeasurable : Measurable (fun Path => FirstHittingTime Later Path - FirstHittingTime Earlier Path) :=
    (measurable_of_countable (fun p : WithTop ℕ × WithTop ℕ => p.1-p.2)).comp
      (LaterTimeMeasurable.prodMk EarlierTimeMeasurable)
  have EmbedMeasurable : Measurable (fun t : WithTop ℕ => ENat.toENNReal t) := measurable_of_countable _
  have EmbedAdd (a b : WithTop ℕ) : ENat.toENNReal (a+b) = ENat.toENNReal a + ENat.toENNReal b := by
    exact ENat.toENNReal_add a b
  have Pointwise (Path : ℕ → State) : ENat.toENNReal (FirstHittingTime Later Path) =
      ENat.toENNReal (FirstHittingTime Earlier Path) +
        ENat.toENNReal (FirstHittingTime Later Path - FirstHittingTime Earlier Path) := by
    rw [← EmbedAdd]
    congr 1
    exact (NestedGoalTimeDecomposition Earlier Later Nested Path).symm
  simp_rw [Pointwise]
  exact lintegral_add_right _ (EmbedMeasurable.comp RemainingMeasurable)

end
end ECTheoryLib.Probability
