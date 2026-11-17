import ECTheoryLib.Operators.Mutation.OneBit
import ECTheoryLib.Operators.Selection.Elitist
import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.HittingTimes.HittingTime

/-!
# RLS initialization, transitions, and trajectories

The standard initial law is uniform on binary strings. Each iteration proposes
a uniformly chosen one-bit flip and accepts according to `NotWorse Candidate Parent`.
The transition kernel supplies a fresh conditional uniform choice at each step.
Positive length is required for mutation.

`RLSRun` is a finite-step law; `RLSRunUntil` freezes the state at the goal.
`RLSProcess` and `RLSStoppedProcess` give full trajectory laws, on which first
hitting times include infinity. Time zero is initialization; steps count mutation
iterations. Evaluation costs require a separate initialization and per-step convention.

The state remains a single solution even for a Pareto comparison: incomparable
candidates are rejected. No population, archive, or runtime theorem is defined here.
-/

namespace ECTheoryLib

/-- A specified one-bit mutation followed by the supplied survivor selection. -/
def RLSUpdate {n : Nat}
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (x : Bits n) (i : Fin n) : Bits n :=
  let Parent : Bits n := x
  let Candidate : Bits n := OnebitMutation Parent i
  ElitistSelect NotWorse Parent Candidate

noncomputable section

/-- Uniform initialization on all `2^n` strings, including the unique empty string. -/
def RLSInit (n : Nat) : PMF (Bits n) :=
  PMF.uniformOfFintype (Bits n)

/-- Every initial string has probability `2^(-n)`. -/
@[simp] theorem RLSInitProbability {n : Nat} (x : Bits n) :
    RLSInit n x = ((2 : ENNReal) ^ n)⁻¹ := by
  have NumberOfBitStrings : Fintype.card (Bits n) = 2 ^ n := by
    
    unfold Bits
    rw [Fintype.card_fun]
    rw [Fintype.card_bool]
    rw [Fintype.card_fin]
  unfold RLSInit
  rw [PMF.uniformOfFintype_apply]
  rw [NumberOfBitStrings]
  
  rw [Nat.cast_pow]
  rfl

/-- The actual successor PMF: uniform one-bit proposal followed by survivor selection. -/
def RLSStep {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (x : Bits n) : PMF (Bits n) :=
  (RandomOneBitMutation PositiveLength x).map
    (fun Candidate => ElitistSelect NotWorse x Candidate)

/-- Mutation followed by selection equals a single map of the complete update
over uniformly chosen coordinates. -/
theorem RLSStepEqUniformUpdate {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (x : Bits n) :
    RLSStep PositiveLength NotWorse x =
      (UniformBitIndex n PositiveLength).map (RLSUpdate NotWorse x) := by
  unfold RLSStep
  unfold RandomOneBitMutation
  -- Compose mutation and selection before taking the pushforward distribution.
  rw [PMF.map_comp]
  
  rfl

/-- A successor's probability sums all coordinate choices producing that state.
Several rejected offspring may all return the parent, so their masses accumulate. -/
theorem RLSStepProbability {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (x y : Bits n) :
    RLSStep PositiveLength NotWorse x y =
      ∑ i : Fin n, if RLSUpdate NotWorse x i = y then (n : ENNReal)⁻¹ else 0 := by
  classical
  rw [RLSStepEqUniformUpdate]
  
  rw [PMF.map_apply]
  
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _Membership
  have PositionProbability : UniformBitIndex n PositiveLength i = (n : ENNReal)⁻¹ := by
    exact UniformBitIndexProbability n PositiveLength i
  rw [PositionProbability]
  
  by_cases ProducesY : RLSUpdate NotWorse x i = y
  · have YEqualsUpdate : y = RLSUpdate NotWorse x i := by
      exact ProducesY.symm
    rw [if_pos YEqualsUpdate]
    rw [if_pos ProducesY]
  · have YDiffersFromUpdate : y ≠ RLSUpdate NotWorse x i := by
      intro YEqualsUpdate
      exact ProducesY YEqualsUpdate.symm
    rw [if_neg YDiffersFromUpdate]
    rw [if_neg ProducesY]

/-- Distribution after the specified number of iterations. Initialization defaults
to uniform sampling; a pure PMF specifies a fixed initial state. -/
def RLSRun {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Steps : Nat) (Initial : PMF (Bits n) := RLSInit n) : PMF (Bits n) :=
  Probability.Evolve (RLSStep PositiveLength NotWorse) Initial Steps

/-- Execute up to the specified number of iterations, freezing upon a goal hit,
including success at initialization. -/
def RLSRunUntil {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Goal : Bits n → Prop) [DecidablePred Goal]
    (Steps : Nat) (Initial : PMF (Bits n) := RLSInit n) : PMF (Bits n) :=
  Probability.Evolve (Probability.StopAt (RLSStep PositiveLength NotWorse) Goal)
    Initial Steps

/-- Full trajectory law; coordinate `t` is the state after `t` mutation iterations. -/
def RLSProcess {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Initial : PMF (Bits n) := RLSInit n) : MeasureTheory.Measure (Nat → Bits n) :=
  Probability.PathMeasure (RLSStep PositiveLength NotWorse) Initial

/-- Full trajectory law frozen after reaching the supplied goal. Almost-sure
reachability is not required to define this law. -/
def RLSStoppedProcess {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Goal : Bits n → Prop) [DecidablePred Goal]
    (Initial : PMF (Bits n) := RLSInit n) : MeasureTheory.Measure (Nat → Bits n) :=
  Probability.PathMeasure (Probability.StopAt (RLSStep PositiveLength NotWorse) Goal) Initial

instance RLSProcessIsProbability {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (Initial : PMF (Bits n)) :
    MeasureTheory.IsProbabilityMeasure (RLSProcess PositiveLength NotWorse Initial) := by
  unfold RLSProcess
  infer_instance

instance RLSStoppedProcessIsProbability {n : Nat} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Goal : Bits n → Prop) [DecidablePred Goal] (Initial : PMF (Bits n)) :
    MeasureTheory.IsProbabilityMeasure
      (RLSStoppedProcess PositiveLength NotWorse Goal Initial) := by
  unfold RLSStoppedProcess
  infer_instance

end
end ECTheoryLib
