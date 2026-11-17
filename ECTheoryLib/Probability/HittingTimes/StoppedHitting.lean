import ECTheoryLib.Probability.HittingTimes.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Stopping at a first hit

Reuse Mathlib stopping, preserving initialization and first-hitting events.
No finite hitting time or target absorption is assumed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω State : Type*}

/-- Reuse Mathlib's stopped process at the original process's first hit. -/
def StopAtFirstHit (Goal : State → Prop) (X : ℕ → Ω → State) : ℕ → Ω → State :=
  stoppedProcess X (hittingAfter X {x | Goal x} 0)

theorem FirstHittingTimeProcessEq (Goal : State → Prop) (X : ℕ → Ω → State) (ω : Ω) :
    FirstHittingTime Goal (fun j => X j ω)=hittingAfter X {x | Goal x} 0 ω := rfl

theorem StopAtFirstHitInitial (Goal : State → Prop) (X : ℕ → Ω → State) (ω : Ω) :
    StopAtFirstHit Goal X 0 ω=X 0 ω := stoppedProcess_eq_of_le bot_le

/-- Every stopped value is an actual value of the original process. -/
theorem StopAtFirstHitValues (Goal : State → Prop) (X : ℕ → Ω → State) (S : Set State)
    (Values : ∀ t ω, X t ω∈S) (t : ℕ) (ω : Ω) : StopAtFirstHit Goal X t ω∈S :=
  Values _ ω

/-- The stopped process satisfies the goal exactly after the original first
hit, including time zero and trajectories that never hit. -/
theorem StopAtFirstHitGoalIff (Goal : State → Prop) (X : ℕ → Ω → State) (t : ℕ) (ω : Ω) :
    Goal (StopAtFirstHit Goal X t ω) ↔ FirstHittingTime Goal (fun j => X j ω)≤(t : WithTop ℕ) := by
  rw [FirstHittingTimeProcessEq]
  constructor
  · intro AtGoal
    by_contra NotHit
    have Before : (t : WithTop ℕ)≤hittingAfter X {x | Goal x} 0 ω := (lt_of_not_ge NotHit).le
    have Equal : StopAtFirstHit Goal X t ω=X t ω := stoppedProcess_eq_of_le Before
    rw [Equal] at AtGoal
    exact NotHit (hittingAfter_le_of_mem (Nat.zero_le t) AtGoal)
  · intro Hit
    have Finite : hittingAfter X {x | Goal x} 0 ω≠⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top Hit
    change Goal (stoppedProcess X (hittingAfter X {x | Goal x} 0) t ω)
    rw [stoppedProcess_eq_of_ge (u := X) (i := t) Hit]
    exact hittingAfter_mem_set_of_ne_top Finite

theorem StopAtFirstHitAbsorbing (Goal : State → Prop) (X : ℕ → Ω → State) (t : ℕ) (ω : Ω) :
    Goal (StopAtFirstHit Goal X t ω) → Goal (StopAtFirstHit Goal X (t+1) ω) := by
  intro AtGoal
  apply (StopAtFirstHitGoalIff Goal X (t+1) ω).mpr
  exact ((StopAtFirstHitGoalIff Goal X t ω).mp AtGoal).trans
    (WithTop.coe_le_coe.mpr (Nat.le_succ t))

/-- Before the stopped process has hit, both endpoints of its next increment
agree with the original increment. The step that first hits is included. -/
theorem StopAtFirstHitStepBefore (Goal : State → Prop) (X : ℕ → Ω → State) (t : ℕ) (ω : Ω)
    (BeforeGoal : ¬Goal (StopAtFirstHit Goal X t ω)) :
    StopAtFirstHit Goal X t ω=X t ω ∧ StopAtFirstHit Goal X (t+1) ω=X (t+1) ω := by
  have Before : (t : WithTop ℕ)<hittingAfter X {x | Goal x} 0 ω := by
    apply lt_of_not_ge
    intro Hit
    apply BeforeGoal
    exact (StopAtFirstHitGoalIff Goal X t ω).mpr Hit
  have NextLe : ((t+1 : ℕ) : WithTop ℕ)≤hittingAfter X {x | Goal x} 0 ω := by
    cases H : hittingAfter X {x | Goal x} 0 ω using WithTop.recTopCoe with
    | top => exact le_top
    | coe k =>
      rw [H] at Before
      exact WithTop.coe_le_coe.mpr (Nat.succ_le_iff.mpr (WithTop.coe_lt_coe.mp Before))
  exact ⟨stoppedProcess_eq_of_le Before.le, stoppedProcess_eq_of_le NextLe⟩

theorem StopAtFirstHitEvent (Goal : State → Prop) (X : ℕ → Ω → State) (t : ℕ) :
    {ω | FirstHittingTime Goal (fun j => StopAtFirstHit Goal X j ω)≤(t : WithTop ℕ)} =
      {ω | FirstHittingTime Goal (fun j => X j ω)≤(t : WithTop ℕ)} := by
  ext ω
  change (FirstHittingTime Goal (fun j => StopAtFirstHit Goal X j ω)≤(t : WithTop ℕ)) ↔
    (FirstHittingTime Goal (fun j => X j ω)≤(t : WithTop ℕ))
  rw [FirstHittingTimeLeIff]
  simp_rw [StopAtFirstHitGoalIff Goal X]
  constructor
  · rintro ⟨j,Before,Hit⟩
    exact Hit.trans (WithTop.coe_le_coe.mpr Before)
  · intro Hit
    exact ⟨t,le_rfl,Hit⟩

theorem StopAtFirstHitAdapted [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (Goal : ℝ → Prop) (MeasurableGoal : MeasurableSet {x | Goal x}) :
    Adapted F (StopAtFirstHit Goal X) := by
  have Strongly : StronglyAdapted F X := fun t => (AdaptedX t).stronglyMeasurable
  exact (Strongly.stoppedProcess_of_discrete
    (AdaptedX.isStoppingTime_hittingAfter (n := 0) MeasurableGoal)).adapted

end
end ECTheoryLib.Probability
