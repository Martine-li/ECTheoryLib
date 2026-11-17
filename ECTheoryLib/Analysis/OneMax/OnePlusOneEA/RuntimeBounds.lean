import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift
import ECTheoryLib.Tools.Runtime.LocalDrift

/-!
# Expected runtime of the actual (1+1) EA on OneMax

`RuntimeUpperBound` allows any initial PMF, including initially optimal mass.
`RuntimeLogBound` gives the explicit bound `e * n * (1 + log n)` for `n > 0`.
Time counts transitions after initialization; nontermination is represented by
infinity in `ENNReal`. Finiteness follows from the bound, rather than being assumed.

The argument uses the single-zero-bit events and multiplicative drift, as in
Lengler, *Drift Analysis* (2018), Sections 3.2–3.3. This module specializes the
library's finite-state local-inequality interface to its existing EA kernel.
-/
namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Expected first-optimum hitting time under the actual EA path measure.
Initialization is at time zero and is not charged as an iteration. -/
def ExpectedRuntime {n : Nat} (hn : 0 < n) (Initial : PMF (Bits n)) : ENNReal :=
  ExpectedHittingTime (Step hn) (fun x => x = AllOnes n) Initial

/-- An initial-distribution-dependent bound via the zero-safe logarithmic potential.
The one-bit event probability is a lower bound on drift, not an exact drift formula. -/
theorem RuntimeUpperBound {n : Nat} (hn : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal
      (∫ x, MultiplicativeDriftPotential 1 (StandardOneBitProbability n) (ZeroCount x : ℝ)
        ∂Initial.toMeasure) := by
  apply Tools.Runtime.MultiplicativeRuntimeUpperBound (Step hn) Initial ZeroCount
    (fun x => x = AllOnes n) (fun _ => True) ZeroIffTarget
  · exact ae_of_all _ (fun _ => trivial)
  · intro x
    exact ae_of_all _ (fun _ _ => trivial)
  · intro x
    filter_upwards [StepPreservesZero hn x] with y Preserves
    intro _Valid
    exact Preserves
  · exact StandardOneBitProbabilityPositive hn
  · intro x _Valid _Nonzero
    exact OneStepDriftLowerBound hn x

/-- The bound's integrand is uniformly at most `e n (1 + log n)`.
The zero-potential branch contributes zero even when initialization can be optimal. -/
theorem LogPotentialBound {n : Nat} (hn : 0 < n) (x : Bits n) :
    MultiplicativeDriftPotential 1 (StandardOneBitProbability n) (ZeroCount x : ℝ) ≤
      Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  have LengthPositive : (0 : ℝ) < n := by exact_mod_cast hn
  have LengthAtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have LogNonnegative : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg LengthAtLeastOne
  have CoefficientNonnegative : 0 ≤ Real.exp 1 * (n : ℝ) :=
    mul_nonneg (Real.exp_pos 1).le LengthPositive.le
  unfold MultiplicativeDriftPotential
  by_cases Zero : ZeroCount x = 0
  · rw [Zero, Nat.cast_zero, if_pos rfl]
    exact mul_nonneg CoefficientNonnegative (by linarith)
  · have PotentialPositive : (0 : ℝ) < ZeroCount x :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero Zero)
    rw [if_neg (ne_of_gt PotentialPositive), div_one]
    have PotentialBound : (ZeroCount x : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n (OneMax x)
    have LogBound := Real.log_le_log PotentialPositive PotentialBound
    have DivBound :
        (1 + Real.log (ZeroCount x : ℝ)) / StandardOneBitProbability n ≤
          (1 + Real.log (n : ℝ)) / StandardOneBitProbability n := by
      exact div_le_div_of_nonneg_right (by linarith) (StandardOneBitProbabilityPositive hn).le
    calc
      _ ≤ (1 + Real.log (n : ℝ)) / StandardOneBitProbability n := DivBound
      _ = (1 / StandardOneBitProbability n) * (1 + Real.log (n : ℝ)) := by ring
      _ ≤ (Real.exp 1 * (n : ℝ)) * (1 + Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (StandardOneBitProbabilityInverseBound hn) (by linarith)

/-- For every initial distribution, the expected number of iterations is at most
`e n (1 + ln n)`. The standard uniform initialization is included without excluding
its positive probability of starting at the optimum. -/
theorem RuntimeLogBound {n : Nat} (hn : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime hn Initial ≤
      ENNReal.ofReal (Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  apply (RuntimeUpperBound hn Initial).trans
  apply ENNReal.ofReal_le_ofReal
  have IntegralBound := integral_mono (μ := Initial.toMeasure)
    (Integrable.of_finite (f := fun x : Bits n =>
      MultiplicativeDriftPotential 1 (StandardOneBitProbability n) (ZeroCount x : ℝ)))
    (integrable_const (Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ))))
    (LogPotentialBound hn)
  simpa only [integral_const, probReal_univ, one_smul] using IntegralBound

/-- The proved finite bound rules out divergent expected runtime. -/
theorem RuntimeFinite {n : Nat} (hn : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime hn Initial ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (RuntimeLogBound hn Initial)

/-- An already optimal fixed initial state has zero hitting time in expectation. -/
theorem OptimalInitialRuntime {n : Nat} (hn : 0 < n) :
    ExpectedRuntime hn (PMF.pure (AllOnes n)) = 0 := by
  exact ExpectedHittingTimeOfPureTarget (Step hn) (fun x => x = AllOnes n) (AllOnes n) rfl

end
end ECTheoryLib.Analysis.EAOneMax
