import ECTheoryLib.Analysis.OneMax.RLS
import ECTheoryLib.Analysis.LeadingOnes.RLS.ExactRuntime
import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RuntimeUpperBounds

/-! Small executable clients of the runtime library. Time counts updates
after initialization; assumptions and initialization laws are retained. -/

namespace ECTheoryLibExamples
open MeasureTheory ECTheoryLib
noncomputable section

example {n : Nat} (PositiveLength : 0 < n) (InitialState : Bits n) :
    Analysis.RLSOnOneMax.ExpectedRuntime PositiveLength InitialState =
      ENNReal.ofReal ((n : Real) *
        (harmonic (Analysis.RLSOnOneMax.ZeroCount InitialState) : Real)) := by
  exact Analysis.RLSOnOneMax.FixedRuntimeExact PositiveLength InitialState

example :
    (Analysis.RLSOnLeadingOnes.ExpectedRuntime (by decide : 0 < 4)
      (RLSInit 4)).toReal = 8 := by
  rw [Analysis.RLSOnLeadingOnes.UniformRuntimeExactReal]
  norm_num

example {n : Nat} (PositiveLength : 0 < n) (Weights : Fin n → Real)
    (Positive : ∀ k, 0 < Weights k) (Initial : PMF (Bits n)) :
    Analysis.EALinearMinimization.ExpectedRuntime PositiveLength Weights Initial ≤
      ENNReal.ofReal ((4 * Real.exp 1 * (n : Real)) *
        (1 + Real.log (2 * (n : Real)))) := by
  exact Analysis.EALinearMinimization.RankRuntimeUpperBound
    PositiveLength Weights Positive Initial

end
end ECTheoryLibExamples
