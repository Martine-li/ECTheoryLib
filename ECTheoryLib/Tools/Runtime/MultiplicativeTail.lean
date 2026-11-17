import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Tools.Drift.MultiplicativeTail

/-!
# Multiplicative runtime tails from local kernel inequalities

The full state may be countable. The potential has a pointwise finite range,
and legality is established from the initial law and the actual transition.
These interfaces verify the scalar theorem's obligations on mathlib trajectories.
No hitting-time bound or prior runtime finiteness is an input.
-/

namespace ECTheoryLib.Tools.Runtime

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift

noncomputable section

variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Local multiplicative progress gives a tail bound on actual trajectories,
including arbitrary initialization and countable full state representations. -/
theorem MultiplicativeRuntimeTailAtTimeOfFiniteRange
    (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal Valid : State → Prop) (S : Finset ℝ)
    (smin Delta : ℝ) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ x, V x ∈ S) (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x = 0 → V y = 0)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta * V x ≤ ∫ y, V x - V y ∂(Step x).toMeasure)
    (t : Nat) :
    (PathMeasure Step Initial) {Path | (t : WithTop Nat) < FirstHittingTime Goal Path} ≤
      ENNReal.ofReal (Real.exp (-Delta * (t : ℝ)) *
        (∫ x, V x ∂Initial.toMeasure) / smin) := by
  let μ := PathMeasure Step Initial
  let X : Nat → (Nat → State) → ℝ := fun t Path => V (Path t)
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have MeasurableX : ∀ t, Measurable (X t) :=
    fun t => (measurable_of_countable V).comp (measurable_pi_apply t)
  have BoundV (x : State) : ‖V x‖ ≤ ∑ s ∈ S, ‖s‖ :=
    Finset.single_le_sum (fun s _ => norm_nonneg s) (ValuesInS x)
  have Absorbing := PathMeasureZeroIsAbsorbing Step Initial V Valid ValidOnPaths PreservesZero
  have Drift : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      Delta * s ≤ StateDrift μ X t s := by
    intro t s _InS Nonzero EventPositive
    exact PathMeasureStateDriftLowerBoundOfBounded Step Initial V (fun s => Delta * s) Valid
      (∑ s ∈ S, ‖s‖) BoundV LocalDrift t s Nonzero (ValidOnPaths t) EventPositive
  have Bound := MultiplicativeDriftTailAtTime μ X S smin Delta MeasurableX
    MinimumPositive StateLowerBound (fun _ Path => ValuesInS (Path _)) Absorbing Drift t
  have InitialMean : ExpectedValue μ (X 0) = ∫ x, V x ∂Initial.toMeasure :=
    PathMeasureInitialIntegral Step Initial V
  have HittingEquality : ∀ Path : Nat → State,
      ZeroHittingTime X Path = FirstHittingTime Goal Path := by
    intro Path
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [X, Set.mem_ofPred_eq, ZeroIffGoal]
    have SameExistence : (∃ j, 0 ≤ j ∧ V (Path j) = 0) ↔
        (∃ j, 0 ≤ j ∧ Goal (Path j)) := by
      exact exists_congr (fun j => and_congr_right (fun _ => ZeroIffGoal (Path j)))
    by_cases Reached : ∃ j, 0 ≤ j ∧ Goal (Path j)
    · rw [if_pos (SameExistence.mpr Reached), if_pos Reached]
    · rw [if_neg (fun Hit => Reached (SameExistence.mp Hit)), if_neg Reached]
  simp_rw [InitialMean, HittingEquality] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Retain the exact one-step contraction factor on actual kernel paths. -/
theorem MultiplicativeRuntimeGeometricTailOfFiniteRange
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin δ : ℝ) (DeltaAtMostOne : δ≤1) (MinimumPositive : 0<smin)
    (StateLower : ∀ s∈S, s=0 ∨ smin≤s) (Values : ∀ x, V x∈S)
    (ZeroIffGoal : ∀ x, V x=0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x=0 → V y=0)
    (LocalDrift : ∀ x, Valid x → V x≠0 → δ*V x≤∫ y, V x-V y ∂(Step x).toMeasure)
    (t : ℕ) :
    (PathMeasure Step Initial) {Path | (t : WithTop ℕ)<FirstHittingTime Goal Path}≤
      ENNReal.ofReal ((1-δ)^t*(∫ x, V x ∂Initial.toMeasure)/smin) := by
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => V (Path t)
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have MeasurableX : ∀ t, Measurable (X t) :=
    fun t => (measurable_of_countable V).comp (measurable_pi_apply t)
  have BoundV (x : State) : ‖V x‖≤∑ s∈S, ‖s‖ :=
    Finset.single_le_sum (fun s _ => norm_nonneg s) (Values x)
  have Absorbing := PathMeasureZeroIsAbsorbing Step Initial V Valid ValidOnPaths PreservesZero
  have Drift : ∀ t s, s∈S → s≠0 → 0<μ (StateEvent X t s) → δ*s≤StateDrift μ X t s := by
    intro t s _ Nonzero Positive
    exact PathMeasureStateDriftLowerBoundOfBounded Step Initial V (fun s => δ*s) Valid
      (∑ s∈S, ‖s‖) BoundV LocalDrift t s Nonzero (ValidOnPaths t) Positive
  have Bound := MultiplicativeDriftGeometricTailAtTime μ X S smin δ DeltaAtMostOne MeasurableX
    MinimumPositive StateLower (fun _ Path => Values (Path _)) Absorbing Drift t
  have InitialMean : ExpectedValue μ (X 0)=∫ x, V x ∂Initial.toMeasure := PathMeasureInitialIntegral Step Initial V
  have Times (Path : ℕ → State) : ZeroHittingTime X Path=FirstHittingTime Goal Path := by
    apply WithTop.eq_of_forall_le_coe_iff
    intro j
    have Left := FirstHittingTimeLeIff (fun s : ℝ => s=0) (fun k => X k Path) j
    have Right := FirstHittingTimeLeIff Goal Path j
    refine Left.trans (Iff.trans ?_ Right.symm)
    simp only [X,ZeroIffGoal]
  simp_rw [InitialMean,Times] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
