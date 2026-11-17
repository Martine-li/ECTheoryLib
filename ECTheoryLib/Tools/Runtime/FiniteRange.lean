import ECTheoryLib.Probability.Processes.PathDriftBounds
import ECTheoryLib.Tools.Drift.Additive

/-!
# Runtime bounds with finite potential range and countable full state

The full state representation need not itself be finite. A fixed finite range
of potential values suffices for the existing scalar additive drift theorem.
This is useful for list populations: validity can impose a fixed length, while
the complete raw-list kernel and its actual trajectory law remain unchanged.
The range convention remains pointwise for every state and hence every path.
-/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Additive runtime bound on the actual countable-state process, with a finite
nonnegative potential range. Legality is required almost surely at initialization
and preserved by the kernel. Finiteness of the hitting-time expectation follows
from the bound rather than being an input. -/
theorem AdditiveRuntimeUpperBoundOfFiniteRange (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal Valid : State → Prop) (S : Finset ℝ)
    (ZeroInS : 0 ∈ S) (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ x, V x ∈ S) (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PreservesZero : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → V x = 0 → V y = 0)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 → Delta ≤ ∫ y, V x - V y ∂(Step x).toMeasure) :
    ExpectedHittingTime Step Goal Initial ≤ ENNReal.ofReal ((∫ x, V x ∂Initial.toMeasure) / Delta) := by
  classical
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => V (Path t)
  have ValidOnPaths := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid
  have MeasurableX : ∀ t, Measurable (X t) :=
    fun t => (measurable_of_countable V).comp (measurable_pi_apply t)
  have BoundV (x : State) : ‖V x‖ ≤ ∑ s ∈ S, ‖s‖ :=
    Finset.single_le_sum (fun s _ => norm_nonneg s) (ValuesInS x)
  have Absorbing := PathMeasureZeroIsAbsorbing Step Initial V Valid ValidOnPaths PreservesZero
  have Drift : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      Delta ≤ StateDrift μ X t s := by
    intro t s _InS Nonzero EventPositive
    exact PathMeasureStateDriftLowerBoundOfBounded Step Initial V (fun _ => Delta) Valid
      (∑ s ∈ S, ‖s‖) BoundV LocalDrift t s Nonzero (ValidOnPaths t) EventPositive
  have Bound := AdditiveDriftUpperBound μ X S Delta MeasurableX ZeroInS StatesNonnegative
    (fun _ Path => ValuesInS (Path _)) Absorbing PositiveDelta Drift
  rw [ExpectedHittingTimeEqExpectedZero Step Initial V Goal ZeroIffGoal]
  have InitialMean : ExpectedValue μ (X 0) = ∫ x, V x ∂Initial.toMeasure :=
    PathMeasureInitialIntegral Step Initial V
  rw [InitialMean] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
