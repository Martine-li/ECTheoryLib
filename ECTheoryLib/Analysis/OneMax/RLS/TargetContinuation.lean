import ECTheoryLib.Tools.Runtime.NonabsorbingVariableJumpLower
import ECTheoryLib.Analysis.OneMax.RLS.RuntimeJumpLowerBounds

/-!
# RLS lower bounds with arbitrary post-target continuation

The actual kernel agrees with RLS away from the goal. Local descent,
jump floor and exact mean drift are reused before the first success.
The theorem is a runtime lower bound, not a full hitting-law equivalence.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift ECTheoryLib.Tools.Runtime
noncomputable section

/-- The jump-floor lower bound is unchanged when RLS uses any continuation
kernel after reaching its goal. Premises are derived from actual RLS steps. -/
theorem RuntimeJumpLowerBoundOfTargetContinuation {n : ℕ} (PositiveLength : 0<n)
    (Continue : Transition (Bits n)) (Agrees : ∀ x, ¬IsTarget x → Continue x=Step PositiveLength x)
    (Initial : PMF (Bits n)) :
    ENNReal.ofReal (∫ x, VariableDriftPotential 1 (fun s => (s+1)/(n : ℝ)) (Potential x) ∂Initial.toMeasure)≤
      ExpectedHittingTime Continue IsTarget Initial := by
  classical
  let S : Finset ℝ := insert 0 (Finset.univ.image (Potential (n := n)))
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  have Lower : ∀ s∈S, s=0 ∨ (1 : ℝ)≤s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | Image
    · exact Or.inl Zero
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp Image
      by_cases Zero : ZeroCount x=0
      · exact Or.inl (Nat.cast_eq_zero.mpr Zero)
      · exact Or.inr (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero Zero))
  have Away (x : Bits n) (Active : Potential x≠0) : ¬IsTarget x := by
    intro Goal
    exact Active ((PotentialEqZeroIffTarget x).mpr Goal)
  apply VariableRuntimeLowerBoundOfJumpFloorNonabsorbing Continue Initial Potential IsTarget (fun _ => True)
    S 1 (fun s => (s+1)/(n : ℝ)) (fun s => s-1) zero_lt_one Lower
    (fun x => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩))
    PotentialEqZeroIffTarget (ae_of_all _ (fun _ => True.intro))
    (fun _ => ae_of_all _ (fun _ _ => True.intro))
    (fun x Nonnegative => div_pos (by linarith) PositiveN)
    (fun _ _ _ _ Before => div_le_div_of_nonneg_right (add_le_add Before le_rfl) PositiveN.le)
    (fun s InS Nonzero => sub_nonneg.mpr ((Lower s InS).resolve_left Nonzero))
  · intro x
    by_cases Active : Potential x=0
    · exact ae_of_all _ (fun _ _ Nonzero => (Nonzero Active).elim)
    · rw [Agrees x (Away x Active)]
      filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Desc
      exact fun _ _ => Desc
  · intro x
    by_cases Active : Potential x=0
    · exact ae_of_all _ (fun _ _ Nonzero => (Nonzero Active).elim)
    · rw [Agrees x (Away x Active)]
      filter_upwards [StepPotentialDropAtMostOne PositiveLength x] with y Drop
      intro _ _
      linarith
  · intro x _ Active
    rw [Agrees x (Away x Active),OneStepDrift,sub_add_cancel]

theorem FixedRuntimeJumpLowerBoundOfTargetContinuation {n : ℕ} (PositiveLength : 0<n)
    (Continue : Transition (Bits n)) (Agrees : ∀ x, ¬IsTarget x → Continue x=Step PositiveLength x)
    (InitialState : Bits n) (InitialPositive : 0<ZeroCount InitialState) :
    ENNReal.ofReal ((n : ℝ)/2+(n : ℝ)*(Real.log ((ZeroCount InitialState : ℝ)+1)-Real.log 2))≤
      ExpectedHittingTime Continue IsTarget (PMF.pure InitialState) := by
  have Bound := RuntimeJumpLowerBoundOfTargetContinuation PositiveLength Continue Agrees (PMF.pure InitialState)
  rw [PMF.toMeasure_pure,integral_dirac] at Bound
  have Positive : 0<Potential InitialState := Nat.cast_pos.mpr InitialPositive
  rw [VariableDriftPotential,if_neg Positive.ne',ShiftedReciprocalDriftIntegral _ _ Positive.le,one_div_div] at Bound
  norm_num only [show (1+1 : ℝ)=2 by norm_num] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
