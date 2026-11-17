import ECTheoryLib.Analysis.Needle.RLS.ExponentialMoments
import ECTheoryLib.Tools.Drift.ExponentialBarrier
import ECTheoryLib.Probability.Processes.ConditionalTransition
import ECTheoryLib.Probability.Processes.PathInvariant

/-!
# Exponential early-hit bounds for actual RLS on Needle

The fixed initial distance is at least n/4. All conditional moments,
finite-range and absorption assumptions are proved for the actual kernel.
For n=4m the result is Pr[T <= t] <= 2t/2^m. Time counts mutation iterations
after initialization. No finite-mean or almost-sure termination premise is used.
-/

namespace ECTheoryLib.Analysis.RLSOnNeedle
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

theorem StepTargetAbsorbing {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential x ≤ 0 → Potential y ≤ 0 := by
  rw [Step, RLSStepEqUniformUpdate]
  apply PMFAEOfSupport
  intro y Supported
  obtain ⟨i, _Possible, Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Supported
  intro Zero
  have AtTarget := (PotentialEqZeroIffTarget x).mp (le_antisymm Zero (PotentialNonnegative x))
  change Update x i = y at Equal
  rw [UpdateAtTarget x i AtTarget] at Equal
  rw [← Equal]
  exact Zero

/-- Actual weak-selection RLS needs exponential time to cross the distance-n/4
barrier on Needle, in the explicit finite-time probability sense below.
The initial state is fixed and lies at distance at least n/4 from the optimum. -/
theorem FixedRuntimeExponentialLowerTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitiallyFar : (n : ℝ)/4 ≤ Potential InitialState) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*2*Real.exp (-Real.log 2*((n : ℝ)/4))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := n))
  let b : ℝ := (n : ℝ)/4
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  have Ordered : 0<b := div_pos PositiveN (by norm_num)
  have LogNonnegative : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have InitiallyAbove : ∀ᵐ Path ∂μ, b ≤ X 0 Path := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path Initial
    change b ≤ Potential (Path 0)
    rw [Initial]
    exact InitiallyFar
  have Absorbing (j : ℕ) : ∀ᵐ Path ∂μ, X j Path ≤ 0 → X (j+1) Path ≤ 0 :=
    PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential x ≤ 0 → Potential y ≤ 0) (StepTargetAbsorbing PositiveLength) j
  have Interior (j : ℕ) (s : ℝ) (_Member : s ∈ S) (Above : 0<s) (Below : s<b)
      (Positive : 0 < μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun Path => Real.exp (-Real.log 2*(X (j+1) Path-s)))
        (StateEvent X j s) ≤ 1 := by
    rw [EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound (Step PositiveLength)
      (PMF.pure InitialState) j {x | Potential x=s}
      (fun _ y => Real.exp (-Real.log 2*(Potential y-s))) 1 Positive (by
        intro x Equal
        change Potential x=s at Equal
        rw [← Equal]
        apply InteriorExponentialMoment PositiveLength x
        · rw [Equal]; exact Above
        · rw [Equal]; exact Below)
  have Entrance (j : ℕ) (s : ℝ) (_Member : s ∈ S) (Above : b≤s)
      (Positive : 0 < μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun Path => Real.exp (-Real.log 2*(X (j+1) Path-b)))
        (StateEvent X j s) ≤ 2 := by
    rw [EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound (Step PositiveLength)
      (PMF.pure InitialState) j {x | Potential x=s}
      (fun _ y => Real.exp (-Real.log 2*(Potential y-b))) 2 Positive (by
        intro x Equal
        apply EntranceExponentialMoment PositiveLength x
        change Potential x=s at Equal
        rw [Equal]
        exact Above)
  have Bound := ExponentialBarrierHittingTail μ X S 0 b (Real.log 2) 2 Ordered
    LogNonnegative (by norm_num) Coordinates Values InitiallyAbove Absorbing Interior Entrance t
  have Hitting (Path : ℕ → Bits n) :
      FirstHittingTime (fun s : ℝ => s≤0) (fun j => X j Path)=FirstHittingTime IsTarget Path := by
    have SameGoal (j : ℕ) : (X j Path ≤ 0) ↔ IsTarget (Path j) := by
      rw [← PotentialEqZeroIffTarget]
      exact ⟨fun Zero => le_antisymm Zero (PotentialNonnegative _), fun Zero => Zero.le⟩
    unfold FirstHittingTime hittingAfter
    change (if ∃ j, 0 ≤ j ∧ X j Path ≤ 0 then
      ((sInf {j : ℕ | 0 ≤ j ∧ X j Path ≤ 0} : ℕ) : WithTop ℕ) else ⊤) =
        if ∃ j, 0 ≤ j ∧ IsTarget (Path j) then
          ((sInf {j : ℕ | 0 ≤ j ∧ IsTarget (Path j)} : ℕ) : WithTop ℕ) else ⊤
    simp only [SameGoal]
  simp_rw [Hitting] at Bound
  rw [sub_zero] at Bound
  exact Bound

/-- For lengths 4m the same bound has the elementary form 2t/2^m. -/
theorem FixedRuntimeDyadicLowerTail (m : ℕ) (PositiveM : 0 < m)
    (InitialState : Bits (4*m)) (InitiallyFar : (m : ℝ) ≤ Potential InitialState) (t : ℕ) :
    (PathMeasure (Step (by omega : 0 < 4*m)) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((2 : ℝ)*(t : ℝ)/2^m) := by
  have Scale : ((4*m : ℕ) : ℝ)/4=(m : ℝ) := by push_cast; ring
  have Bound := FixedRuntimeExponentialLowerTail (by omega : 0 < 4*m) InitialState
    (by rw [Scale]; exact InitiallyFar) t
  rw [Scale, show -Real.log 2*(m : ℝ) = -((m : ℝ)*Real.log 2) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)] at Bound
  have Rearrange : (t : ℝ)*2*(2^m)⁻¹=2*(t : ℝ)/2^m := by ring
  rw [Rearrange] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnNeedle
