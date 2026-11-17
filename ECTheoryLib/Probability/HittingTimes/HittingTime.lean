import Mathlib.Probability.Process.HittingTime

/-!
# First hitting times on trajectories

The definitions reuse mathlib's `hittingAfter`. Initialization is time zero; a
trajectory that never reaches the goal has hitting time infinity. Event
characterizations and measurability do not assume termination or finite expected
time. They are later instantiated with actual algorithm path measures.
-/

namespace ECTheoryLib.Probability

open MeasureTheory

/-- The first time the trajectory satisfies `Goal`, or infinity if it never does. -/
noncomputable def FirstHittingTime {State : Type*} (Goal : State → Prop)
    (Path : Nat → State) : WithTop Nat :=
  
  
  hittingAfter (fun t Trajectory => Trajectory t) {x | Goal x} 0 Path

/-- The first hit of a measurable goal by a measurable process is measurable.
This uses mathlib's stopping-time API and needs neither countable state, Markov
structure, nor finite expected runtime. -/
theorem FirstHittingTimeProcessMeasurable {Ω State : Type*}
    [MeasurableSpace Ω] [MeasurableSpace State]
    (Goal : State → Prop) (X : Nat → Ω → State)
    (GoalMeasurable : MeasurableSet {x | Goal x})
    (CoordinatesMeasurable : ∀ t, Measurable (X t)) :
    Measurable (fun ω => FirstHittingTime Goal (fun t => X t ω)) := by
  have ProcessAdapted :
      Adapted (⊤ : Filtration Nat (inferInstance : MeasurableSpace Ω)) X := by
    intro t
    change Measurable (X t)
    exact CoordinatesMeasurable t
  have HittingIsStoppingTime :
      IsStoppingTime (⊤ : Filtration Nat (inferInstance : MeasurableSpace Ω))
        (fun ω => FirstHittingTime Goal (fun t => X t ω)) := by
    unfold FirstHittingTime
    exact ProcessAdapted.isStoppingTime_hittingAfter GoalMeasurable
  exact HittingIsStoppingTime.measurable'

/-- Hitting by time `t` is equivalent to satisfying the goal at some time `s ≤ t`. -/
theorem FirstHittingTimeLeIff {State : Type*} (Goal : State → Prop)
    (Path : Nat → State) (t : Nat) :
    FirstHittingTime Goal Path ≤ (t : WithTop Nat) ↔ ∃ s ≤ t, Goal (Path s) := by
  -- The interval includes time zero, which preserves initially successful runs.
  have LibraryCriterion :
      FirstHittingTime Goal Path ≤ (t : WithTop Nat) ↔
        ∃ s ∈ Set.Icc 0 t, Goal (Path s) := by
    unfold FirstHittingTime
    exact hittingAfter_le_iff
      (u := fun k (Trajectory : Nat → State) => Trajectory k)
      (s := {x | Goal x}) (n := 0) (i := t) (ω := Path)
  constructor
  · intro HitByTime
    obtain ⟨s, InInterval, Reached⟩ := LibraryCriterion.mp HitByTime
    have BeforeTime : s ≤ t := by
      exact InInterval.2
    exact ⟨s, BeforeTime, Reached⟩
  · intro SomeHit
    obtain ⟨s, BeforeTime, Reached⟩ := SomeHit
    have InInterval : s ∈ Set.Icc 0 t := by
      constructor
      · exact Nat.zero_le s
      · exact BeforeTime
    apply LibraryCriterion.mpr
    exact ⟨s, InInterval, Reached⟩

/-- Infinite hitting time is equivalent to failing the goal at every natural time. -/
theorem FirstHittingTimeEqTopIff {State : Type*} (Goal : State → Prop)
    (Path : Nat → State) :
    FirstHittingTime Goal Path = ⊤ ↔ ∀ t, ¬ Goal (Path t) := by
  have LibraryCriterion :
      FirstHittingTime Goal Path = ⊤ ↔ ∀ t, 0 ≤ t → ¬ Goal (Path t) := by
    unfold FirstHittingTime
    exact hittingAfter_eq_top_iff
  constructor
  · intro InfiniteTime
    have NoHitFromZero : ∀ t, 0 ≤ t → ¬ Goal (Path t) := by
      exact LibraryCriterion.mp InfiniteTime
    intro t
    exact NoHitFromZero t (Nat.zero_le t)
  · intro NeverHit
    apply LibraryCriterion.mpr
    intro t _AfterZero
    exact NeverHit t

/-- Hitting time is zero exactly when the initial state already satisfies the goal. -/
theorem FirstHittingTimeEqZeroIff {State : Type*} (Goal : State → Prop)
    (Path : Nat → State) : FirstHittingTime Goal Path = 0 ↔ Goal (Path 0) := by
  constructor
  · intro TimeIsZero
    have HitByZero : FirstHittingTime Goal Path ≤ (0 : WithTop Nat) := by
      rw [TimeIsZero]
    obtain ⟨s, BeforeZero, Reached⟩ := (FirstHittingTimeLeIff Goal Path 0).mp HitByZero
    have TimeEqualsZero : s = 0 := by
      exact Nat.eq_zero_of_le_zero BeforeZero
    rw [TimeEqualsZero] at Reached
    exact Reached
  · intro InitiallyReached
    have HitByZero : FirstHittingTime Goal Path ≤ (0 : WithTop Nat) := by
      apply (FirstHittingTimeLeIff Goal Path 0).mpr
      exact ⟨0, Nat.le_refl 0, InitiallyReached⟩
    
    have NonnegativeTime : (0 : WithTop Nat) ≤ FirstHittingTime Goal Path := by
      exact zero_le
    exact le_antisymm HitByZero NonnegativeTime

end ECTheoryLib.Probability
