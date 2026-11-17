import ECTheoryLib.Probability.Processes.PathDrift
import ECTheoryLib.Tools.Drift.Additive

/-!
# Exact additive runtime from a finite transition kernel

When expected potential decrease equals Delta at every non-target state, the
proved additive upper and lower bounds coincide. Finite algorithm state supplies
a pointwise finite real potential range. Runtime is the extended first-hit
integral on the actual infinite trajectory law; finiteness is concluded.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {State : Type*} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Exact local decrease Delta > 0 gives expected runtime V(initial)/Delta
from any fixed state, including an initial target. The real potential must be
nonnegative, characterize the target by zero, and remain zero almost surely
after a zero-state transition. Finite algorithm state supplies the finite range. -/
theorem AdditiveRuntimeExactOfLocalDrift
    (Step : Transition State) (V : State → ℝ) (Goal : State → Prop)
    (Nonnegative : ∀ x, 0 ≤ V x)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Delta : ℝ) (DeltaPositive : 0 < Delta)
    (LocalDrift : ∀ x, (∫ y, V x - V y ∂(Step x).toMeasure) =
      if V x = 0 then 0 else Delta)
    (StepPreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, V x = 0 → V y = 0)
    (InitialState : State) :
    ExpectedHittingTime Step Goal (PMF.pure InitialState) =
      ENNReal.ofReal (V InitialState / Delta) := by
  classical
  let μ := PathMeasure Step (PMF.pure InitialState)
  let X : Nat → (Nat → State) → ℝ := fun t Path => V (Path t)
  let S : Finset ℝ := insert 0 (Finset.univ.image V)

  -- Every trajectory coordinate lies pointwise in the image of the finite state space.
  have CoordinatesMeasurable : ∀ t, Measurable (X t) := by
    intro t
    exact (measurable_of_finite V).comp (measurable_pi_apply t)
  have ZeroInS : (0 : ℝ) ∈ S := by
    exact Finset.mem_insert_self _ _
  have StatesNonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with IsZero | InImage
    · rw [IsZero]
    · obtain ⟨x, _InUniv, ValueEq⟩ := Finset.mem_image.mp InImage
      rw [← ValueEq]
      exact Nonnegative x
  have ValuesInS : ∀ t Path, X t Path ∈ S := by
    intro t Path
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩

  -- Lift one-step zero preservation to absorption under the actual path law.
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro t
    exact PathMeasureFollowsTransition Step (PMF.pure InitialState)
      (fun x y => V x = 0 → V y = 0) StepPreservesZero t

  -- Lift exact local drift to conditional drift on each positive-probability potential event.
  have ExactConditionalDrift : ∀ t s, s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s = Delta := by
    intro t s Nonzero EventPositive
    have ExactDrift := PathMeasureStateDrift Step (PMF.pure InitialState) V
      (fun s => if s = 0 then 0 else Delta) LocalDrift t s EventPositive
    rw [if_neg Nonzero] at ExactDrift
    exact ExactDrift
  have StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta ≤ StateDrift μ X t s := by
    intro t s _InS Nonzero EventPositive
    exact le_of_eq (ExactConditionalDrift t s Nonzero EventPositive).symm
  have StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ Delta := by
    intro t s _InS Nonzero EventPositive
    exact le_of_eq (ExactConditionalDrift t s Nonzero EventPositive)
  have InitialMean : ExpectedValue μ (X 0) = V InitialState := by
    exact PathMeasurePureInitialIntegral Step InitialState V

  -- Apply the existing upper and lower bounds to the same extended expectation.
  have Upper := AdditiveDriftUpperBound μ X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS Absorbing DeltaPositive StateDriftLowerBound
  have Lower := AdditiveDriftLowerBound μ X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS Absorbing DeltaPositive StateDriftUpperBound
  rw [InitialMean] at Upper Lower
  have ZeroRuntimeExact : ExpectedZeroHittingTime μ X =
      ENNReal.ofReal (V InitialState / Delta) := by
    exact le_antisymm Upper Lower

  -- Potential zero and the actual goal have identical first-hit times, including time zero.
  have HittingTimeEquality : ∀ Path : Nat → State,
      ZeroHittingTime X Path = FirstHittingTime Goal Path := by
    intro Path
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [X, Set.mem_ofPred_eq, ZeroIffGoal]
  have RuntimeEquality : ExpectedHittingTime Step Goal (PMF.pure InitialState) =
      ExpectedZeroHittingTime μ X := by
    unfold ExpectedHittingTime ExpectedZeroHittingTime
    apply lintegral_congr
    intro Path
    rw [HittingTimeEquality]
    rfl
  rw [RuntimeEquality]
  exact ZeroRuntimeExact

end
end ECTheoryLib.Tools.Drift
