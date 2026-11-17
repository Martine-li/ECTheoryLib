import ECTheoryLib.Analysis.OneMinMax.Archive.RuntimeBounds
import ECTheoryLib.Algorithms.SEMO
import ECTheoryLib.Operators.Mutation.OneBitBounds
import ECTheoryLib.Tools.Runtime.Cost

/-!
# SEMO on OneMinMax: full front coverage

For `n > 0`, the library's SEMO uses a uniform parent, uniform one-bit mutation,
and strict-dominance rejection with replacement of objective ties. The expected
number of iterations until the current archive represents every one of the
`n+1` Pareto objective values is at most `2 n (n+1) H_(n+1)`.

The explicit bound is an O(n² log n) bound, obtained with the shared symmetric
missing-level potential. It is not a claim of a tight leading constant or of
following the same proof as a particular paper. Arbitrary valid initial archives
are supported, as well as the actual uniformly initialized singleton. One
offspring is evaluated per iteration; initialization contributes one evaluation
for that singleton initialization.
-/
namespace ECTheoryLib.Analysis.SEMOOneMinMax
open MeasureTheory ECTheoryLib.Probability
open OneMinMaxCoverage
noncomputable section

/-- Expected iterations to current complete coverage under the existing SEMO path law. -/
def ExpectedRuntime {n : Nat} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)) := SEMOInit n) : ENNReal :=
  ExpectedHittingTime (SEMOStep hn Dominates) Complete Initial

/-- SEMO is exactly the uniform-parent, one-bit instance of the shared archive kernel. -/
theorem StepEqArchiveSearch {n : Nat} (hn : 0 < n) :
    SEMOStep hn (Dominates (n := n)) =
      ArchiveSearchStep UniformParetoParent (RandomOneBitMutation hn) Dominates := rfl

/-- Every valid initial archive distribution has expected full-coverage time at
most `2 n (n+1) H_(n+1)`. The theorem bounds transitions after time zero. -/
theorem RuntimeHarmonicBound {n : Nat} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤
      ENNReal.ofReal (2 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) := by
  have LengthPositive : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have Bound := OneMinMaxCoverage.RuntimeHarmonicBound
    UniformParetoParent (RandomOneBitMutation hn) (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))
    (by positivity) (one_div_pos.mpr LengthPositive)
    UniformParentFloor (fun x i => (RandomOneBitProbabilityReal hn x i).ge)
    Initial InitiallyValid
  have Normalize : 2 * (harmonic (n + 1) : ℝ) /
      (1 / ((n : ℝ) + 1) * (1 / (n : ℝ))) =
      2 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ) := by
    field_simp
  rw [Normalize] at Bound
  exact Bound

/-- The standard uniformly initialized singleton satisfies all initialization
obligations; the runtime bound contains no unproved algorithm-specific premise. -/
theorem UniformRuntimeBound {n : Nat} (hn : 0 < n) :
    ExpectedRuntime hn ≤
      ENNReal.ofReal (2 * (n : ℝ) * ((n : ℝ) + 1) * (harmonic (n + 1) : ℝ)) :=
  RuntimeHarmonicBound hn (SEMOInit n) (fun P Possible => SEMOInitValid Dominates P Possible)

/-- Explicit logarithmic form of the full-front coverage bound. -/
theorem RuntimeLogBound {n : Nat} (hn : 0 < n) :
    ExpectedRuntime hn ≤
      ENNReal.ofReal (2 * (n : ℝ) * ((n : ℝ) + 1) * (1 + Real.log ((n : ℝ) + 1))) := by
  apply (UniformRuntimeBound hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)

/-- Full coverage has finite expected time; finiteness is derived from the bound. -/
theorem RuntimeFinite {n : Nat} (hn : 0 < n) : ExpectedRuntime hn ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (UniformRuntimeBound hn)

/-- With one initial evaluation and one offspring evaluation per iteration,
the expected evaluation count is exactly one plus the expected runtime. -/
theorem EvaluationCostEq {n : Nat} (hn : 0 < n) :
    Tools.Runtime.ExpectedEvaluationCost (SEMOStep hn Dominates) Complete (SEMOInit n) 1 1 =
      1 + ExpectedRuntime hn := by
  rw [Tools.Runtime.ExpectedEvaluationCostEq]
  simp only [Nat.cast_one, one_mul]
  rfl

end
end ECTheoryLib.Analysis.SEMOOneMinMax
