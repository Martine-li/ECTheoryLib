import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.SelectedScoreConcentration
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.MutationTailBounds
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.AcceptanceExpectation
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.StochasticProgress
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.RuntimeBounds
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.GeometricTailBounds
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.VarianceTail
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.FiniteVarianceTail
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.FirstStepLowerTail

/-!
# OneMax / OnePlusOneEA

Public entry point for this case. Submodules separate the model, local progress,
and runtime results where applicable. Existing theorem namespaces are preserved.
See `ECTheoryLib/Analysis/README.md` for the mathematical scope of each case.
-/
