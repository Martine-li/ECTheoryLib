import ECTheoryLib.Probability.Processes.PathDrift
import ECTheoryLib.Tools.Drift.Multiplicative

/-!
# Fixed-state multiplicative bounds from a finite transition kernel

This interface lifts exact local drift of the actual kernel to the existing
scalar multiplicative theorem. Finite algorithm state supplies the natural
potential's pointwise finite range. Initialization is pure and runtime is the
extended first-hitting-time integral on complete trajectories.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

variable {State : Type*} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Exact local multiplicative drift yields a logarithmic runtime bound
from a fixed non-target state. Zero potential characterizes the goal, and
absorption is checked directly on the actual one-step kernel. -/
theorem MultiplicativeRuntimeUpperBoundOfExactDrift
    (Step : Transition State) (V : State → Nat) (Goal : State → Prop)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, (∫ y, (V x : ℝ) - (V y : ℝ) ∂(Step x).toMeasure) =
      Delta * (V x : ℝ))
    (StepPreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, V x = 0 → V y = 0)
    (InitialState : State) (InitialPositive : 0 < V InitialState) :
    ExpectedHittingTime Step Goal (PMF.pure InitialState) ≤
      ENNReal.ofReal ((1 + Real.log (V InitialState : ℝ)) / Delta) := by
  classical
  let μ := PathMeasure Step (PMF.pure InitialState)
  let X : Nat → (Nat → State) → ℝ := fun t Path => (V (Path t) : ℝ)
  let S : Finset ℝ := insert 0 (Finset.univ.image (fun x : State => (V x : ℝ)))
  have CoordinatesMeasurable : ∀ t, Measurable (X t) := by
    intro t
    exact (measurable_of_finite (fun x : State => (V x : ℝ))).comp
      (measurable_pi_apply t)
  have ZeroInS : (0 : ℝ) ∈ S := by
    exact Finset.mem_insert_self _ _
  have StateLowerBound : ∀ s ∈ S, s = 0 ∨ (1 : ℝ) ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with IsZero | InImage
    · exact Or.inl IsZero
    · obtain ⟨x, _InUniv, ValueEq⟩ := Finset.mem_image.mp InImage
      by_cases VZero : V x = 0
      · left
        rw [← ValueEq, VZero, Nat.cast_zero]
      · right
        rw [← ValueEq]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr VZero
  have ValuesInS : ∀ t Path, X t Path ∈ S := by
    intro t Path
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro t
    have Follows := PathMeasureFollowsTransition Step (PMF.pure InitialState)
      (fun x y => V x = 0 → V y = 0) StepPreservesZero t
    filter_upwards [Follows] with Path Preserves
    intro CurrentZero
    have NatZero : V (Path t) = 0 := Nat.cast_eq_zero.mp CurrentZero
    change (V (Path (t + 1)) : ℝ) = 0
    exact Nat.cast_eq_zero.mpr (Preserves NatZero)
  have StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s := by
    intro t s _InS _Nonzero EventPositive
    have ExactDrift := PathMeasureStateDrift Step (PMF.pure InitialState)
      (fun x => (V x : ℝ)) (fun s => Delta * s) LocalDrift t s EventPositive
    exact le_of_eq ExactDrift.symm
  have InitialFixed : ∀ᵐ Path ∂μ, Path 0 = InitialState := by
    exact PathMeasureInitialPure Step InitialState
  have InitialNonzero : ∀ᵐ Path ∂μ, X 0 Path ≠ 0 := by
    filter_upwards [InitialFixed] with Path AtInitial
    change (V (Path 0) : ℝ) ≠ 0
    rw [AtInitial]
    exact ne_of_gt (Nat.cast_pos.mpr InitialPositive)
  have InitialLogMean :
      ExpectedValue μ (fun Path => Real.log (X 0 Path / 1)) =
        Real.log (V InitialState : ℝ) := by
    unfold ExpectedValue
    have LogIsConstant : (fun Path => Real.log (X 0 Path / 1)) =ᵐ[μ]
        (fun _ => Real.log (V InitialState : ℝ)) := by
      filter_upwards [InitialFixed] with Path AtInitial
      change Real.log ((V (Path 0) : ℝ) / 1) = _
      rw [AtInitial, div_one]
    rw [integral_congr_ae LogIsConstant, integral_const, probReal_univ, one_smul]
  have Bound := MultiplicativeDriftUpperBoundOfPositiveInitial μ X S 1 Delta
    CoordinatesMeasurable ZeroInS (by norm_num) StateLowerBound ValuesInS
    Absorbing PositiveDelta StateDriftLowerBound InitialNonzero
  rw [InitialLogMean] at Bound
  have HittingTimeEquality : ∀ Path : Nat → State,
      ZeroHittingTime X Path = FirstHittingTime Goal Path := by
    intro Path
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [X, Set.mem_ofPred_eq, Nat.cast_eq_zero, ZeroIffGoal]
  have RuntimeEquality : ExpectedHittingTime Step Goal (PMF.pure InitialState) =
      ExpectedZeroHittingTime μ X := by
    unfold ExpectedHittingTime ExpectedZeroHittingTime
    apply lintegral_congr
    intro Path
    rw [HittingTimeEquality]
    rfl
  rw [RuntimeEquality]
  exact Bound

end
end ECTheoryLib.Tools.Drift
