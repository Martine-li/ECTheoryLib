import ECTheoryLib.Tools.Runtime.FiniteRange
import ECTheoryLib.Tools.Drift.Multiplicative

/-! Runtime bounds from local inequalities, with arbitrary initialization.
Legality is proved on initialization and one transition, then lifted by the library.
Finite potential ranges remain pointwise; runtime finiteness is a conclusion. -/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

variable {State : Type*} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Additive runtime bound from a lower bound on legal non-target states. -/
theorem AdditiveRuntimeUpperBound (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal Valid : State → Prop)
    (Nonnegative : ∀ x, 0 ≤ V x) (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x = 0 → V y = 0)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta ≤ ∫ y, V x - V y ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤
      ENNReal.ofReal ((∫ x, V x ∂Initial.toMeasure) / Delta) := by
  classical
  let S : Finset ℝ := insert 0 (Finset.univ.image V)
  have StatesNonnegative : ∀ s ∈ S, 0 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · rw [Zero]
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp InImage
      exact Nonnegative x
  exact AdditiveRuntimeUpperBoundOfFiniteRange Step Initial V Goal Valid S
    (Finset.mem_insert_self _ _) StatesNonnegative
    (fun x => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    ZeroIffGoal Initially PreservesValid PreservesZero Delta PositiveDelta LocalDrift

/-- Multiplicative runtime bound; the logarithmic potential's zero branch handles
initially optimal mass explicitly. The potential is natural-valued, minimum positive value 1. -/
theorem MultiplicativeRuntimeUpperBound (Step : Transition State) (Initial : PMF State)
    (V : State → Nat) (Goal Valid : State → Prop)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x = 0 → V y = 0)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta * (V x : ℝ) ≤ ∫ y, (V x : ℝ) - (V y : ℝ) ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤ ENNReal.ofReal
      (∫ x, MultiplicativeDriftPotential 1 Delta (V x : ℝ) ∂Initial.toMeasure) := by
  classical
  let μ := PathMeasure Step Initial
  let X : Nat → (Nat → State) → ℝ := fun t Path => (V (Path t) : ℝ)
  let S : Finset ℝ := insert 0 (Finset.univ.image (fun x : State => (V x : ℝ)))
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have MeasurableX : ∀ t, Measurable (X t) := by
    intro t
    exact (measurable_of_finite (fun x : State => (V x : ℝ))).comp (measurable_pi_apply t)
  have StateLowerBound : ∀ s ∈ S, s = 0 ∨ (1 : ℝ) ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | InImage
    · exact Or.inl Zero
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp InImage
      by_cases VZero : V x = 0
      · exact Or.inl (Nat.cast_eq_zero.mpr VZero)
      · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr VZero)
  have ValuesInS : ∀ t Path, X t Path ∈ S := by
    intro t Path
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have RealPreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure,
      Valid x → (V x : ℝ) = 0 → (V y : ℝ) = 0 := by
    intro x
    filter_upwards [PreservesZero x] with y Preserves
    intro IsValid IsZero
    exact Nat.cast_eq_zero.mpr (Preserves IsValid (Nat.cast_eq_zero.mp IsZero))
  have Absorbing := PathMeasureZeroIsAbsorbing Step Initial
    (fun x => (V x : ℝ)) Valid ValidOnPaths RealPreservesZero
  have RealLocalDrift : ∀ x, Valid x → (V x : ℝ) ≠ 0 →
      Delta * (V x : ℝ) ≤ ∫ y, (V x : ℝ) - (V y : ℝ) ∂(Step x).toMeasure := by
    intro x IsValid Nonzero
    exact LocalDrift x IsValid (fun IsZero => Nonzero (Nat.cast_eq_zero.mpr IsZero))
  have DriftBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s := by
    intro t s _InS Nonzero EventPositive
    exact PathMeasureStateDriftLowerBound Step Initial (fun x => (V x : ℝ))
      (fun s => Delta * s) Valid RealLocalDrift t s Nonzero (ValidOnPaths t) EventPositive
  have Bound := MultiplicativeDriftUpperBound μ X S 1 Delta MeasurableX
    (Finset.mem_insert_self _ _) (by norm_num) StateLowerBound ValuesInS
    Absorbing PositiveDelta DriftBound
  have RealZeroIff : ∀ x, (V x : ℝ) = 0 ↔ Goal x := by
    intro x
    rw [Nat.cast_eq_zero, ZeroIffGoal]
  rw [ExpectedHittingTimeEqExpectedZero Step Initial (fun x => (V x : ℝ)) Goal RealZeroIff]
  have InitialMean :
      ExpectedValue μ (fun Path => MultiplicativeDriftPotential 1 Delta (X 0 Path)) =
        ∫ x, MultiplicativeDriftPotential 1 Delta (V x : ℝ) ∂Initial.toMeasure :=
    PathMeasureInitialIntegral Step Initial (fun x => MultiplicativeDriftPotential 1 Delta (V x : ℝ))
  rw [InitialMean] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
