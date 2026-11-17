import ECTheoryLib.Analysis.LOTZ.Archive.RuntimeBounds
import ECTheoryLib.Algorithms.GSEMO
import ECTheoryLib.Operators.Mutation.IndependentBitBounds
import ECTheoryLib.Tools.Runtime.Cost

/-!
# Full current-front runtime of original GSEMO on LOTZ

Uniform archive parents and the full standard independent-bit mutation instantiate
the shared LOTZ policy theorem. Only the useful one-bit event is lower-bounded;
zero-bit and multi-bit outcomes are kept in the actual transition. Initialization
may be any law on valid nonempty archives. The evaluation identity is restricted
to the standard singleton initialization, with one evaluation per iteration.
-/
namespace ECTheoryLib.Analysis.GSEMOLOTZ
open MeasureTheory ECTheoryLib.Probability LOTZCoverage
noncomputable section

/-- Original-path expected iterations until all true LOTZ front points coexist. -/
def ExpectedRuntime {n : ℕ} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)) := GSEMOInit n) : ENNReal :=
  ExpectedHittingTime (GSEMOStep hn Dominates) Complete Initial

/-- Keep the exact useful one-bit probability in the complete-front bound. -/
theorem RuntimeProbabilityBound {n : ℕ} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal
      (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / StandardOneBitProbability n) := by
  have Bound := PolicyRuntimeBound UniformParetoParent (StandardBitMutation hn)
    (1 / ((n : ℝ) + 1)) (StandardOneBitProbability n) (by positivity)
    (StandardOneBitProbabilityPositive hn) UniformParentFloor
    (fun x i => (StandardBitMutationOneBitReal hn x i).ge) Initial InitiallyValid
  have Normalize : (2 * (n : ℝ) + 1) /
      ((1 / ((n : ℝ) + 1)) * StandardOneBitProbability n) =
      ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / StandardOneBitProbability n := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
    ring
  rw [Normalize] at Bound
  exact Bound

/-- The existing inverse mutation-probability bound gives an explicit cubic
runtime bound for every valid initial archive law, including n=1. -/
theorem RuntimeCubicBound {n : ℕ} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial ≤ ENNReal.ofReal
      (Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) := by
  apply (RuntimeProbabilityBound hn Initial InitiallyValid).trans
  apply ENNReal.ofReal_le_ofReal
  have Bound := mul_le_mul_of_nonneg_left (StandardOneBitProbabilityInverseBound hn)
    (show 0 ≤ ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) by positivity)
  calc
    _ = (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) * (1 / StandardOneBitProbability n) := by ring
    _ ≤ (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) * (Real.exp 1 * (n : ℝ)) := Bound
    _ = _ := by ring

/-- The standard uniform singleton initialization needs no validity premise. -/
theorem UniformRuntimeBound {n : ℕ} (hn : 0 < n) :
    ExpectedRuntime hn ≤ ENNReal.ofReal
      (Real.exp 1 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) :=
  RuntimeCubicBound hn (GSEMOInit n) (fun P Possible => GSEMOInitValid Dominates P Possible)

/-- Finite mean follows from the bound for every valid initial law. -/
theorem RuntimeFinite {n : ℕ} (hn : 0 < n)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedRuntime hn Initial < ⊤ :=
  lt_of_le_of_lt (RuntimeProbabilityBound hn Initial InitiallyValid) ENNReal.ofReal_lt_top

/-- Standard singleton initialization costs one evaluation; every transition
evaluates one offspring, including rejected or unchanged candidates. -/
theorem EvaluationCostEq {n : ℕ} (hn : 0 < n) :
    Tools.Runtime.ExpectedEvaluationCost (GSEMOStep hn Dominates) Complete (GSEMOInit n) 1 1 =
      1 + ExpectedRuntime hn := by
  rw [Tools.Runtime.ExpectedEvaluationCostEq]
  simp only [Nat.cast_one, one_mul]
  rfl

end
end ECTheoryLib.Analysis.GSEMOLOTZ
