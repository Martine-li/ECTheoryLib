import ECTheoryLib.Tools.Drift.Telescoping

/-!
# Tail-sum lower bounds from bounded expected decrease

Finite summation bounds accumulated decrease while retaining the terminal mean.
An infinite tail sum satisfies the lower bound immediately. Only when the tail
sum is finite must the terminal mean be shown to vanish; neither finite runtime
expectation nor termination is imposed unconditionally.
-/

namespace ECTheoryLib.Tools.Drift

open Filter
open scoped BigOperators

/-- Summing one-step upper bounds controls accumulated expected decrease
over a finite horizon. -/
theorem ExpectedDecreaseSumUpperBound (a : Nat → ℝ) (p : Nat → ENNReal)
    (Delta : ℝ)
    (OneStepDecrease : ∀ t, a t - a (t + 1) ≤ Delta * (p t).toReal)
    (n : Nat) :
    a 0 - a n ≤ Delta * (∑ t ∈ Finset.range n, (p t).toReal) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, mul_zero, sub_self]
  | succ n PreviousBound =>
    rw [Finset.sum_range_succ, mul_add]
    have LastStepDecrease : a n - a (n + 1) ≤ Delta * (p n).toReal := by
      exact OneStepDecrease n
    linarith

/-- A positive upper bound on expected decrease per unit tail probability
yields a tail-sum lower bound. Vanishing terminal means are required only under
the conditional premise that the tail sum is finite. Finite-range processes
can discharge this using their uniform value bound and vanishing tails. -/
theorem ExpectedDecreaseTailSumLowerBound (a : Nat → ℝ) (p : Nat → ENNReal)
    (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (ProbabilitiesFinite : ∀ t, p t ≠ ⊤)
    (OneStepDecrease : ∀ t, a t - a (t + 1) ≤ Delta * (p t).toReal)
    (TerminalExpectationTendstoZero :
      (∑' t, p t) ≠ ⊤ → Tendsto a atTop (nhds 0)) :
    ENNReal.ofReal (a 0 / Delta) ≤ ∑' t, p t := by
  by_cases InfiniteTailSum : (∑' t, p t) = ⊤
  · rw [InfiniteTailSum]
    exact le_top
  · have RealProbabilitiesSummable : Summable (fun t => (p t).toReal) := by
      exact ENNReal.summable_toReal InfiniteTailSum
    have PartialSumsTendsto :
        Tendsto (fun n => ∑ t ∈ Finset.range n, (p t).toReal) atTop
          (nhds ((∑' t, p t).toReal)) := by
      have RealSeriesLimit := RealProbabilitiesSummable.hasSum.tendsto_sum_nat
      rw [← ENNReal.tsum_toReal_eq ProbabilitiesFinite] at RealSeriesLimit
      exact RealSeriesLimit
    have WeightedSumsTendsto :
        Tendsto (fun n => Delta * (∑ t ∈ Finset.range n, (p t).toReal)) atTop
          (nhds (Delta * (∑' t, p t).toReal)) := by
      exact PartialSumsTendsto.const_mul Delta
    have TerminalTendsto : Tendsto a atTop (nhds 0) := by
      exact TerminalExpectationTendstoZero InfiniteTailSum
    have CumulativeDecreaseTendsto :
        Tendsto (fun n => a 0 - a n) atTop (nhds (a 0)) := by
      have DecreaseLimit := TerminalTendsto.const_sub (a 0)
      rw [sub_zero] at DecreaseLimit
      exact DecreaseLimit
    have InitialExpectationLeWeightedSum :
        a 0 ≤ Delta * (∑' t, p t).toReal := by
      apply le_of_tendsto_of_tendsto' CumulativeDecreaseTendsto WeightedSumsTendsto
      intro n
      exact ExpectedDecreaseSumUpperBound a p Delta OneStepDecrease n
    have InitialOverDeltaLeRealSum : a 0 / Delta ≤ (∑' t, p t).toReal := by
      apply (div_le_iff₀ PositiveDelta).mpr
      rw [mul_comm]
      exact InitialExpectationLeWeightedSum
    calc
      ENNReal.ofReal (a 0 / Delta) ≤ ENNReal.ofReal ((∑' t, p t).toReal) := by
        exact ENNReal.ofReal_le_ofReal InitialOverDeltaLeRealSum
      _ = ∑' t, p t := by
        exact ENNReal.ofReal_toReal InfiniteTailSum

end ECTheoryLib.Tools.Drift
