import ECTheoryLib.Analysis.OneMax.RLS.Drift
import ECTheoryLib.Tools.Drift.FiniteMarkov

/-!
# Logarithmic fixed-state bound for RLS on OneMax

Binary, all-ones specialization of Doerr, Doerr, and Koetzing (2018),
Theorem 6's proof, pp. 1745–1746.
https://hpi.de/friedrich/docs/publications/2018/Algorithmica_d.pdf

The actual RLS kernel and exact drift are reused. Initialization is a pure law,
not a conditional uniform law. For `k>0` initial zero bits the bound is
`n(1+log k)`; an initially optimal state hits at time zero. Time counts mutation
iterations. The arbitrary-target version is in TargetOneMax/RLS/RuntimeBounds.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift

noncomputable section

/-- Zero natural potential is equivalent to the OneMax target predicate. -/
theorem ZeroCountEqZeroIffTarget {n : Nat} (x : Bits n) :
    ZeroCount x = 0 ↔ IsTarget x := by
  rw [← PotentialEqZeroIffTarget]
  exact Nat.cast_eq_zero.symm

/-- The actual one-step kernel preserves zero potential almost surely. -/
theorem StepPreservesZeroCount {n : Nat} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, ZeroCount x = 0 → ZeroCount y = 0 := by
  have InRange :
      ∀ᵐ y ∂((UniformBitIndex n PositiveLength).toMeasure.map (Update x)),
        y ∈ Set.range (Update x) := by
    apply ae_map_mem_range
    exact (Set.to_countable _).measurableSet
  rw [PMF.toMeasure_map (Update x) (UniformBitIndex n PositiveLength)
    (measurable_of_finite _)] at InRange
  rw [Step, RLSStepEqUniformUpdate]
  filter_upwards [InRange] with y PossibleUpdate
  intro ParentZero
  obtain ⟨i, UpdateEq⟩ := PossibleUpdate
  rw [← UpdateEq]
  have ParentPotentialZero : Potential x = 0 := by
    exact Nat.cast_eq_zero.mpr ParentZero
  exact Nat.cast_eq_zero.mp (UpdatePreservesZero x i ParentPotentialZero)

/-- From any nonoptimal fixed state with `k` zero bits, expected iterations
are at most `n(1+log k)`. Only positive length and `k>0` remain as premises. -/
theorem FixedRuntimeUpperBound {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialPositive : 0 < ZeroCount InitialState) :
    ExpectedRuntime PositiveLength InitialState ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (ZeroCount InitialState : ℝ))) := by
  have LengthPositive : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have LocalDrift : ∀ x : Bits n,
      (∫ y, (ZeroCount x : ℝ) - (ZeroCount y : ℝ) ∂(Step PositiveLength x).toMeasure) =
        (1 / (n : ℝ)) * (ZeroCount x : ℝ) := by
    intro x
    change (∫ y, Potential x - Potential y ∂(Step PositiveLength x).toMeasure) =
      (1 / (n : ℝ)) * Potential x
    rw [OneStepDrift PositiveLength x]
    ring
  have Bound := MultiplicativeRuntimeUpperBoundOfExactDrift
    (Step PositiveLength) ZeroCount IsTarget ZeroCountEqZeroIffTarget
    (1 / (n : ℝ)) (one_div_pos.mpr LengthPositive) LocalDrift
    (StepPreservesZeroCount PositiveLength) InitialState InitialPositive
  have BoundValue : (1 + Real.log (ZeroCount InitialState : ℝ)) / (1 / (n : ℝ)) =
      (n : ℝ) * (1 + Real.log (ZeroCount InitialState : ℝ)) := by
    rw [one_div, div_inv_eq_mul, mul_comm]
  rw [BoundValue] at Bound
  exact Bound

/-- A fixed optimal initial state has expected hitting time zero. -/
theorem FixedRuntimeEqZero {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (InitialZero : ZeroCount InitialState = 0) :
    ExpectedRuntime PositiveLength InitialState = 0 := by
  exact ExpectedHittingTimeOfPureTarget (Step PositiveLength) IsTarget InitialState
    ((ZeroCountEqZeroIffTarget InitialState).mp InitialZero)

end
end ECTheoryLib.Analysis.RLSOnOneMax
