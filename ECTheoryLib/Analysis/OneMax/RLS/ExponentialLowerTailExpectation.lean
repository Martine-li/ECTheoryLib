import ECTheoryLib.Probability.Moments.ExponentialLowerTailExpectation
import ECTheoryLib.Analysis.OneMax.RLS.LastBitRuntime
import Mathlib.Tactic.IntervalCases

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- The closed lower tail under the actual last-bit RLS trajectory law.
It is the measurable complement of the existing exact strict upper tail. -/
theorem LastBitRuntimeClosedLowerTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : Nat) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState)).real
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop Nat)} =
        1 - (1 - 1 / (n : ℝ)) ^ t := by
  have TimeMeasurable : Measurable (FirstHittingTime (IsTarget (n := n))) :=
    FirstHittingTimeProcessMeasurable IsTarget (fun k (Path : Nat → Bits n) => Path k)
      (Set.to_countable _).measurableSet (fun k => measurable_pi_apply k)
  have Event : {Path : Nat → Bits n | FirstHittingTime IsTarget Path ≤ (t : WithTop Nat)} =
      {Path | (t : WithTop Nat) < FirstHittingTime IsTarget Path}ᶜ := by
    ext Path
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [Event, probReal_compl_eq_one_sub (measurableSet_lt measurable_const TimeMeasurable),
    LastBitRuntimeTail PositiveLength InitialState OneZero t]

/-- The finite-window lower-tail theorem applied to the actual extended runtime.
This non-sharp bound validates reuse; no prior termination or mean is used. -/
theorem LastBitRuntimeLowerBoundOfExponentialTail {n : Nat} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    ENNReal.ofReal (2 - Real.exp 1 / (n : ℝ)) ≤ ExpectedRuntime PositiveLength InitialState := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have TimeMeasurable : Measurable (FirstHittingTime (IsTarget (n := n))) :=
    FirstHittingTimeProcessMeasurable IsTarget (fun k (Path : Nat → Bits n) => Path k)
      (Set.to_countable _).measurableSet (fun k => measurable_pi_apply k)
  have ClosedMass (t : Nat) :
      μ {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop Nat)} =
        ENNReal.ofReal (1 - (1 - 1 / (n : ℝ)) ^ t) := by
    rw [← LastBitRuntimeClosedLowerTail PositiveLength InitialState OneZero t]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have Tail : ∀ k : Nat, 0 < k → k ≤ 2 →
      μ {Path | FirstHittingTime IsTarget Path ≤ ((2 - k : Nat) : WithTop Nat)} ≤
        ENNReal.ofReal ((Real.exp 1 / (n : ℝ)) * Real.exp (-(k : ℝ) / 1)) := by
    intro k Positive Within
    interval_cases k
    · change μ {Path | FirstHittingTime IsTarget Path ≤ ((1 : Nat) : WithTop Nat)} ≤ _
      rw [ClosedMass 1]
      simp only [pow_one, div_one, Nat.cast_one]
      have Cancel : (Real.exp 1 / (n : ℝ)) * Real.exp (-1) = 1 / (n : ℝ) := by
        calc
          _ = (Real.exp 1 * Real.exp (-1)) / (n : ℝ) := by ring
          _ = 1 / (n : ℝ) := by rw [← Real.exp_add]; norm_num
      rw [Cancel]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · change μ {Path | FirstHittingTime IsTarget Path ≤ ((0 : Nat) : WithTop Nat)} ≤ _
      rw [ClosedMass 0]
      simp only [pow_zero, sub_self, ENNReal.ofReal_zero]
      exact zero_le
  have Bound := ExpectedWithTopNatGeOfExponentialLowerTail μ
    (FirstHittingTime (IsTarget (n := n))) 2 (Real.exp 1 / (n : ℝ)) 1 TimeMeasurable
    (div_pos (Real.exp_pos 1) PositiveN) (by norm_num) Tail
  change ENNReal.ofReal (2 - Real.exp 1 / (n : ℝ)) ≤
    ∫⁻ Path, ENat.toENNReal (FirstHittingTime IsTarget Path) ∂μ
  simpa only [Nat.cast_ofNat, mul_one] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax

