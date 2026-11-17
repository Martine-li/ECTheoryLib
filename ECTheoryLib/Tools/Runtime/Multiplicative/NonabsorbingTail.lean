import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicativeTail
import ECTheoryLib.Probability.Processes.FinitePotentialHistory
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-! Nonabsorbing first-hitting tails on the original countable-state kernel.
Only the real potential range is finite. Global goal equivalence and legal
state conditions are kept separate;no expected-runtime premise is used. -/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

private theorem LocalMultiplicativeDriftOnPaths
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Valid : State → Prop)
    (S : Finset ℝ) (Values : ∀ x, V x ∈ S) (Delta : ℝ)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta * V x ≤ ∫ y, V x - V y ∂(Step x).toMeasure) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure Step Initial, V (Path t) ≠ 0 →
      Delta * V (Path t) ≤ ((PathMeasure Step Initial)[
        fun P => V (P t) - V (P (t + 1)) |
        Filtration.piLE (X := fun _ : ℕ => State) t]) Path := by
  have Legal := PathMeasurePreservesProperty Step Initial Valid Initially PreservesValid t
  filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial V S Values t,Legal]
    with Path Equal IsValid
  intro Nonzero
  rw [Equal]
  exact LocalDrift (Path t) IsValid Nonzero

omit [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State] in
private theorem PotentialFirstHittingTime (V : State → ℝ) (Goal : State → Prop)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x) (Path : ℕ → State) :
    ZeroHittingTime (fun t P => V (P t)) Path = FirstHittingTime Goal Path := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  have Left := FirstHittingTimeLeIff (fun s : ℝ => s = 0) (fun j => V (Path j)) t
  have Right := FirstHittingTimeLeIff Goal Path t
  refine Left.trans (Iff.trans ?_ Right.symm)
  simp only [ZeroIffGoal]

/-- A local-kernel tail for arbitrary initialization,without target absorption.
Delta may be any real;positive Delta gives the contracting regime. -/
theorem MultiplicativeRuntimeTailAtTimeOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin Delta : ℝ) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ x, V x ∈ S)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta * V x ≤ ∫ y, V x - V y ∂(Step x).toMeasure) (t : ℕ) :
    (PathMeasure Step Initial) {Path | (t : WithTop ℕ) < FirstHittingTime Goal Path} ≤
      ENNReal.ofReal (Real.exp (-Delta * (t : ℝ)) *
        (∫ x, V x ∂Initial.toMeasure) / smin) := by
  have Bound := MultiplicativeDriftTailAtTimeNonabsorbing (PathMeasure Step Initial)
    (fun j Path => V (Path j)) (Filtration.piLE (X := fun _ : ℕ => State))
    (CountablePathPotentialAdapted V) S smin Delta MinimumPositive StateLowerBound
    (fun _ Path => Values (Path _))
    (LocalMultiplicativeDriftOnPaths Step Initial V Valid S Values Delta Initially PreservesValid LocalDrift) t
  have InitialMean : ExpectedValue (PathMeasure Step Initial) (fun Path => V (Path 0)) =
      ∫ x, V x ∂Initial.toMeasure := PathMeasureInitialIntegral Step Initial V
  simp_rw [InitialMean,PotentialFirstHittingTime V Goal ZeroIffGoal] at Bound
  exact Bound

/-- The source-style ceil tail with a genuinely fixed positive initial potential.
The PMF condition is transported to paths;no target absorption is assumed. -/
theorem MultiplicativeRuntimeUpperTailOfFiniteRangeNonabsorbing
    (Step : Transition State) (Initial : PMF State) (V : State → ℝ) (Goal Valid : State → Prop)
    (S : Finset ℝ) (smin Delta s0 : ℝ) (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s) (Values : ∀ x, V x ∈ S)
    (ZeroIffGoal : ∀ x, V x = 0 ↔ Goal x)
    (Initially : ∀ᵐ x ∂Initial.toMeasure, Valid x)
    (PreservesValid : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, Valid x → Valid y)
    (PositiveDelta : 0 < Delta)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 →
      Delta * V x ≤ ∫ y, V x - V y ∂(Step x).toMeasure)
    (InitialFixed : ∀ᵐ x ∂Initial.toMeasure, V x = s0) (InitialPositive : 0 < s0)
    (r : ℝ) (NonnegativeR : 0 ≤ r) :
    (PathMeasure Step Initial) {Path |
      (⌈(r + Real.log (s0 / smin)) / Delta⌉₊ : WithTop ℕ) < FirstHittingTime Goal Path} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  have MappedInitial : ∀ᵐ x ∂(PathMeasure Step Initial).map
      (fun Path : ℕ → State => Path 0), V x = s0 := by
    rw [PathMeasureInitial Step Initial]
    exact InitialFixed
  have InitialOnPaths := ae_of_ae_map (measurable_pi_apply 0).aemeasurable MappedInitial
  have Bound := MultiplicativeDriftUpperTailNonabsorbing (PathMeasure Step Initial)
    (fun j Path => V (Path j)) (Filtration.piLE (X := fun _ : ℕ => State))
    (CountablePathPotentialAdapted V) S smin Delta s0 ZeroInS MinimumPositive StateLowerBound
    (fun _ Path => Values (Path _)) PositiveDelta
    (LocalMultiplicativeDriftOnPaths Step Initial V Valid S Values Delta Initially PreservesValid LocalDrift)
    InitialOnPaths InitialPositive r NonnegativeR
  simp_rw [PotentialFirstHittingTime V Goal ZeroIffGoal] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime

