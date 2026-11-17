import ECTheoryLib.Analysis.OneMinMax.Archive.RuntimeBounds
import ECTheoryLib.Algorithms.GSEMO
import ECTheoryLib.Tools.Runtime.Cost

/-!
# GSEMO on OneMinMax through the shared coverage interface

The existing GSEMO independently flips each bit with probability 1/n. Its exact
one-bit offspring probability is positive and its reciprocal is at most e*n.
Substituting this into the frozen coverage theorem gives the explicit bound
`2 e n (n+1) H_(n+1)` on expected complete-front coverage iterations.

No coverage potential, archive-retention argument, trajectory bridge, or generic
drift proof is duplicated. The initialization and counting conventions coincide
with the SEMO instance, and arbitrary valid initial PMFs are also supported.
-/
namespace ECTheoryLib.Analysis.GSEMOOneMinMax
open MeasureTheory ECTheoryLib.Probability OneMinMaxCoverage
noncomputable section

/-- Expected iterations until the current GSEMO archive covers all objective values. -/
def ExpectedRuntime {n : Nat} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)) := GSEMOInit n) : ENNReal :=
  ExpectedHittingTime (GSEMOStep hn Dominates) Complete Initial

/-- GSEMO is definitionally the standard-bit-mutation instance of archive search. -/
theorem StepEqArchiveSearch {n : Nat} (hn : 0 < n) :
    GSEMOStep hn (Dominates (n := n)) =
      ArchiveSearchStep UniformParetoParent (StandardBitMutation hn) Dominates := rfl

/-- The exact one-bit probability floor gives a bound for every valid initial PMF. -/
theorem RuntimeProbabilityBound {n : Nat} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal
      (2 * (harmonic (n + 1) : ℝ) / ((1 / ((n : ℝ) + 1)) * StandardOneBitProbability n)) :=
  OneMinMaxCoverage.RuntimeHarmonicBound UniformParetoParent (StandardBitMutation hn)
    (1 / ((n : ℝ) + 1)) (StandardOneBitProbability n) (by positivity)
    (StandardOneBitProbabilityPositive hn) UniformParentFloor
    (fun x i => (StandardBitMutationOneBitReal hn x i).ge) Initial InitiallyValid

/-- Expected full-front coverage takes at most `2 e n (n+1) H_(n+1)` iterations
from any valid initial PMF. Multi-bit moves are allowed by the actual kernel;
the proof only discards their nonnegative contributions. -/
theorem RuntimeHarmonicBound {n : Nat} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal
      (2 * Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) := by
  apply (RuntimeProbabilityBound hn Initial InitiallyValid).trans
  apply ENNReal.ofReal_le_ofReal
  have HarmonicNonnegative : (0 : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
    unfold harmonic
    positivity
  have Normalize : 2 * (harmonic (n + 1) : ℝ) /
      ((1 / ((n : ℝ) + 1)) * StandardOneBitProbability n) =
      (2 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) * (1 / StandardOneBitProbability n) := by
    field_simp
  rw [Normalize]
  have Bound := mul_le_mul_of_nonneg_left (StandardOneBitProbabilityInverseBound hn)
    (show 0 ≤ 2 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) by positivity)
  calc
    _ ≤ (2 * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) * (Real.exp 1 * (n : ℝ)) := Bound
    _ = _ := by ring

/-- The standard uniform singleton initialization discharges archive validity. -/
theorem UniformRuntimeBound {n : Nat} (hn : 0 < n) :
    ExpectedRuntime hn ≤ ENNReal.ofReal
      (2 * Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) :=
  RuntimeHarmonicBound hn (GSEMOInit n) (fun P Possible => GSEMOInitValid Dominates P Possible)

/-- Explicit O(n² log n) upper bound on full front coverage for standard GSEMO. -/
theorem RuntimeLogBound {n : Nat} (hn : 0 < n) :
    ExpectedRuntime hn ≤ ENNReal.ofReal
      (2 * Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (1 + Real.log ((n : ℝ) + 1))) := by
  apply (UniformRuntimeBound hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)

/-- The finite coverage bound rules out divergent expected runtime. -/
theorem RuntimeFinite {n : Nat} (hn : 0 < n) : ExpectedRuntime hn ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (UniformRuntimeBound hn)

/-- One initial evaluation and one evaluation per mutation iteration give
expected evaluation count one plus expected runtime. -/
theorem EvaluationCostEq {n : Nat} (hn : 0 < n) :
    Tools.Runtime.ExpectedEvaluationCost (GSEMOStep hn Dominates) Complete (GSEMOInit n) 1 1 =
      1 + ExpectedRuntime hn := by
  rw [Tools.Runtime.ExpectedEvaluationCostEq]
  simp only [Nat.cast_one, one_mul]
  rfl

end
end ECTheoryLib.Analysis.GSEMOOneMinMax
