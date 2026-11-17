import ECTheoryLib.Probability.HittingTimes.Expectation
import ECTheoryLib.Algorithms.RLS
import ECTheoryLib.Problems.OneMax
import ECTheoryLib.Problems.Comparison

/-!
# RLS on OneMax: model and runtime definitions

This analysis interface combines the generic algorithm and the concrete problem.
It defines the update, goal, zero-count potential, actual transition kernel, and
extended expected hitting time. The goal is exactly the problem's optimizer set.
`Drift`, `RuntimeBounds`, and `ExactRuntime` establish the corresponding results.
Time zero is initialization; runtime counts subsequent mutation iterations.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

/-- Specialize the generic deterministic RLS update to OneMax maximization. -/
abbrev Update {n : Nat} (x : Bits n) (i : Fin n) : Bits n :=
  RLSUpdate (Problems.MaxNotWorse OneMax) x i

/-- Compatibility alias retained for older notes; new code uses Update. -/
abbrev update {n : Nat} (x : Bits n) (i : Fin n) : Bits n :=
  Update x i

/-- The goal event that every coordinate is one. -/
def IsTarget {n : Nat} (x : Bits n) : Prop :=
  ∀ i, x i = true

instance IsTargetDecidable {n : Nat} : DecidablePred (IsTarget (n := n)) := by
  intro x
  unfold IsTarget
  infer_instance

/-- Coordinatewise ones are equivalent to equality with the all-ones string. -/
theorem IsTargetIffEqAllOnes {n : Nat} (x : Bits n) :
    IsTarget x ↔ x = AllOnes n := by
  constructor
  · intro Reached
    funext i
    change x i = true
    exact Reached i
  · intro StringEqualsAllOnes
    unfold IsTarget
    intro i
    rw [StringEqualsAllOnes]
    rfl

/-- The analysis goal is exactly the problem-level global optimum predicate. -/
theorem IsTargetIffOptimal {n : Nat} (x : Bits n) :
    IsTarget x ↔ Problems.OneMax.IsOptimal x := by
  constructor
  · intro Reached
    have StringEqualsAllOnes : x = AllOnes n := by
      exact (IsTargetIffEqAllOnes x).mp Reached
    exact (Problems.OneMax.IsOptimalIffEqAllOnes x).mpr StringEqualsAllOnes
  · intro Optimal
    have StringEqualsAllOnes : x = AllOnes n := by
      exact (Problems.OneMax.IsOptimalIffEqAllOnes x).mp Optimal
    exact (IsTargetIffEqAllOnes x).mpr StringEqualsAllOnes

end ECTheoryLib.Analysis.RLSOnOneMax

namespace ECTheoryLib.Analysis.RLSOnOneMax

open ECTheoryLib.Probability

noncomputable section

/-- Number of zero bits; OneMaxLeN ensures subtraction is ordinary counting. -/
abbrev ZeroCount {n : Nat} (x : Bits n) : Nat :=
  Problems.OneMax.ZeroCount x

/-- Real zero count, used for signed one-step potential differences. -/
def Potential {n : Nat} (x : Bits n) : ℝ :=
  (ZeroCount x : ℝ)

/-- The actual RLS kernel with OneMax-maximizing selection. -/
def Step {n : Nat} (PositiveLength : 0 < n) : Transition (Bits n) :=
  RLSStep PositiveLength (Problems.MaxNotWorse OneMax)

/-- Extended expected iterations until all ones from the specified fixed
initial state. Nontermination and divergent expectation are preserved as infinity. -/
def ExpectedRuntime {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength) IsTarget (PMF.pure InitialState)

theorem PotentialNonnegative {n : Nat} (x : Bits n) :
    0 ≤ Potential x := by
  unfold Potential
  exact Nat.cast_nonneg (ZeroCount x)

theorem PotentialEqZeroIffTarget {n : Nat} (x : Bits n) :
    Potential x = 0 ↔ IsTarget x := by
  constructor
  · intro PotentialIsZero
    have ZeroCountIsZero : ZeroCount x = 0 := by
      unfold Potential at PotentialIsZero
      exact Nat.cast_eq_zero.mp PotentialIsZero
    have LowerBound : n ≤ OneMax x := by
      unfold ZeroCount Problems.OneMax.ZeroCount at ZeroCountIsZero
      exact Nat.le_of_sub_eq_zero ZeroCountIsZero
    have ValueEqualsN : OneMax x = n := by
      exact Nat.le_antisymm (Problems.OneMax.OneMaxLeN x) LowerBound
    have StringEqualsAllOnes : x = AllOnes n := by
      exact (Problems.OneMax.OneMaxEqNIffEqAllOnes x).mp ValueEqualsN
    exact (IsTargetIffEqAllOnes x).mpr StringEqualsAllOnes
  · intro Reached
    have StringEqualsAllOnes : x = AllOnes n := by
      exact (IsTargetIffEqAllOnes x).mp Reached
    rw [StringEqualsAllOnes]
    unfold Potential ZeroCount Problems.OneMax.ZeroCount
    rw [Problems.OneMax.OneMaxAllOnes, Nat.sub_self]
    exact Nat.cast_zero

/-- Local condition for the coarse additive bound. The actual algorithm
satisfies it by OneStepDriftLowerBoundProof in the Drift module. -/
def OneStepDriftLowerBound {n : Nat} (PositiveLength : 0 < n) : Prop :=
  ∀ x : Bits n, ¬ IsTarget x →
    (1 : ℝ) / (n : ℝ) ≤ ExpectedDecrease (Step PositiveLength) Potential x

/-- Zero count is bounded by the string length. -/
theorem PotentialLeLength {n : Nat} (x : Bits n) :
    Potential x ≤ (n : ℝ) := by
  unfold Potential ZeroCount Problems.OneMax.ZeroCount
  exact Nat.cast_le.mpr (Nat.sub_le n (OneMax x))


end

end ECTheoryLib.Analysis.RLSOnOneMax
