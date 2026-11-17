import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith

/-!
# Telescoping expected decreases and runtime tails

The deterministic sequences represent nonnegative expected potentials and
extended nonnegative tail probabilities. Finite sums are bounded first, then
the supremum of the nonnegative partial sums yields the infinite-sum bound.
No concrete process or convergence premise is built into these rules.
-/

namespace ECTheoryLib.Tools.Drift

open scoped BigOperators

/-- Sum one-step expected decreases while retaining the terminal potential;
no convergence of the infinite sum is assumed. -/
theorem ExpectedDecreaseSumLowerBound (a : Nat → ℝ) (p : Nat → ENNReal)
    (Delta : ℝ)
    (OneStepDecrease : ∀ t, Delta * (p t).toReal ≤ a t - a (t + 1))
    (n : Nat) :
    Delta * (∑ t ∈ Finset.range n, (p t).toReal) ≤ a 0 - a n := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, mul_zero, sub_self]
  | succ n PreviousBound =>
    rw [Finset.sum_range_succ, mul_add]
    have LastStepDecrease : Delta * (p n).toReal ≤ a n - a (n + 1) := by
      exact OneStepDecrease n
    linarith

/-- Nonnegative expected potentials and positive drift imply a finite upper
bound on the tail sum. Each term being finite permits faithful real conversion;
the infinite tail sum is not assumed finite. -/
theorem ExpectedDecreaseTailSumUpperBound (a : Nat → ℝ) (p : Nat → ENNReal)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (ExpectationsNonnegative : ∀ t, 0 ≤ a t)
    (ProbabilitiesFinite : ∀ t, p t ≠ ⊤)
    (OneStepDecrease : ∀ t, Delta * (p t).toReal ≤ a t - a (t + 1)) :
    (∑' t, p t) ≤ ENNReal.ofReal (a 0 / Delta) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have FiniteSumBound : Delta * (∑ t ∈ Finset.range n, (p t).toReal) ≤ a 0 := by
    have TelescopingBound := ExpectedDecreaseSumLowerBound a p Delta OneStepDecrease n
    have LastExpectationNonnegative : 0 ≤ a n := by
      exact ExpectationsNonnegative n
    linarith
  have RealSumBound : (∑ t ∈ Finset.range n, (p t).toReal) ≤ a 0 / Delta := by
    apply (le_div_iff₀ PositiveDelta).mpr
    rw [mul_comm]
    exact FiniteSumBound
  have SumAsReal :
      (∑ t ∈ Finset.range n, p t) =
        ENNReal.ofReal (∑ t ∈ Finset.range n, (p t).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro t _InRange
      exact (ENNReal.ofReal_toReal (ProbabilitiesFinite t)).symm
    · intro t _InRange
      exact ENNReal.toReal_nonneg
  rw [SumAsReal]
  exact ENNReal.ofReal_le_ofReal RealSumBound

end ECTheoryLib.Tools.Drift
