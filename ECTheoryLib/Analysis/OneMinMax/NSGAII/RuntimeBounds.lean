import ECTheoryLib.Analysis.OneMinMax.NSGAII.CoverageDrift
import ECTheoryLib.Tools.Runtime.FiniteRange
import ECTheoryLib.Tools.Runtime.Cost
import ECTheoryLib.Tools.Runtime.Harmonic
import ECTheoryLib.Operators.Mutation.OneBitBounds

/-!
# Full-front runtime of uniform-parent NSGA-II on OneMinMax

For n >= 1 and population size N >= 4(n+1), the actual no-crossover algorithm
covers the entire front in at most `4 n H_(n+1)` expected generations with one-bit
mutation, or `4 e n H_(n+1)` with independent standard bit mutation. Initialization
may be any law supported on length N, including the actual independent uniform
initializer. Multiplicities and all survivor tie outcomes are retained in the model.

The proof follows the retention and batch-progress mechanism of Zheng and Doerr
(2023), arXiv:2112.08581v7, Lemma 1 and Theorem 2. The harmonic estimate here has
a looser constant, not the paper's precise constant. Generations exclude initial
evaluations; at generation boundaries the expected evaluation cost is N+N*E[T].
No within-generation early stopping or wall-clock complexity is asserted.
-/
namespace ECTheoryLib.Analysis.NSGAIIOneMinMax
open MeasureTheory Probability Tools.Runtime
noncomputable section

/-- Extended expected generations until the current population covers all n+1
objective values, on the original list process. Already covered initial states
have time zero; nontermination and divergent expectation are represented by infinity. -/
def ExpectedRuntime {n : ℕ} (Mutation : Bits n → PMF (Bits n))
    (Initial : PMF (List (Bits n))) : ENNReal :=
  ExpectedHittingTime (NSGAIIStep Mutation Fitness) Complete Initial

/-- Initial-potential-dependent runtime bound for every fixed-size initial law.
Positive one-bit probability and the proved capacity condition are sufficient;
finite expectation is concluded, not assumed. -/
theorem RuntimeUpperBound {n N : ℕ} (Room : 4 * (n + 1) ≤ N)
    (Mutation : Bits n → PMF (Bits n)) (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime Mutation Initial ≤ ENNReal.ofReal ((∫ P, Potential P ∂Initial.toMeasure) / (Delta / 2)) := by
  refine AdditiveRuntimeUpperBoundOfFiniteRange (NSGAIIStep Mutation Fitness) Initial Potential Complete
    (fun P => P.length = N) (PotentialValues n) (ZeroInValues n) ?_ PotentialInValues PotentialZeroIffComplete
    (PMFAEOfSupport Initial _ Initially) ?_ ?_ (Delta / 2) (by positivity) ?_
  · intro s Present
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp Present
    exact Tools.Coverage.MissingWeightNonnegative _ _ _ (fun j _ => (Tools.Coverage.LineWeightPositive n j).le)
  · intro P
    apply PMFAEOfSupport
    intro Q Possible Length
    exact (NSGAIIStepLength Mutation Fitness P Q Possible).trans Length
  · intro P
    apply PMFAEOfSupport
    intro Q Possible Length Zero
    apply (PotentialZeroIffComplete Q).mpr
    exact StepComplete Mutation P Q (by rw [Length]; exact Room)
      ((PotentialZeroIffComplete P).mp Zero) Possible
  · intro P Length Nonzero
    exact OneStepDriftLowerBound Mutation Delta PositiveDelta.le MutationFloor P
      (by rw [Length]; exact Room) (fun Covered => Nonzero ((PotentialZeroIffComplete P).mpr Covered))

/-- Uniform harmonic bound `4 H_(n+1)/Delta` for the actual NSGA-II process.
The population-size factor in parent selection is compensated by the independent
batch size; N remains constrained by the value-retention capacity condition. -/
theorem RuntimeHarmonicBound {n N : ℕ} (Room : 4 * (n + 1) ≤ N)
    (Mutation : Bits n → PMF (Bits n)) (Delta : ℝ) (PositiveDelta : 0 < Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime Mutation Initial ≤ ENNReal.ofReal (4 * (harmonic (n + 1) : ℝ) / Delta) := by
  apply (RuntimeUpperBound Room Mutation Delta PositiveDelta MutationFloor Initial Initially).trans
  apply ENNReal.ofReal_le_ofReal
  have MeanBound := integral_mono (PMFIntegrableOfBounded Initial Potential _ PotentialNormBound)
    (integrable_const (2 * (harmonic (n + 1) : ℝ))) PotentialBound
  simp only [integral_const, probReal_univ, one_smul] at MeanBound
  have Bound := div_le_div_of_nonneg_right MeanBound (by positivity : 0 ≤ Delta / 2)
  calc
    _ ≤ 2 * (harmonic (n + 1) : ℝ) / (Delta / 2) := Bound
    _ = _ := by ring

/-- With one-bit mutation, full current-front coverage takes at most
`4 n H_(n+1)` expected generations for any initial law of size N >= 4(n+1). -/
theorem OneBitRuntimeBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime (RandomOneBitMutation hn) Initial ≤
      ENNReal.ofReal (4 * (n : ℝ) * (harmonic (n + 1) : ℝ)) := by
  have Bound := RuntimeHarmonicBound Room (RandomOneBitMutation hn) (1 / (n : ℝ)) (by positivity)
    (fun x i => (RandomOneBitProbabilityReal hn x i).ge) Initial Initially
  convert Bound using 1
  congr 1
  field_simp

/-- With independent bit mutation at rate 1/n, full current-front coverage takes
at most `4 e n H_(n+1)` expected generations, with the actual crowding survivor rule. -/
theorem StandardRuntimeBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime (StandardBitMutation hn) Initial ≤
      ENNReal.ofReal (4 * Real.exp 1 * (n : ℝ) * (harmonic (n + 1) : ℝ)) := by
  apply (RuntimeHarmonicBound Room (StandardBitMutation hn) (StandardOneBitProbability n)
    (StandardOneBitProbabilityPositive hn) (fun x i => (StandardBitMutationOneBitReal hn x i).ge)
    Initial Initially).trans
  apply ENNReal.ofReal_le_ofReal
  have Bound := mul_le_mul_of_nonneg_left (StandardOneBitProbabilityInverseBound hn)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (HarmonicNonnegative (n + 1)))
  calc
    _ = (4 * (harmonic (n + 1) : ℝ)) * (1 / StandardOneBitProbability n) := by ring
    _ ≤ (4 * (harmonic (n + 1) : ℝ)) * (Real.exp 1 * n) := Bound
    _ = _ := by ring

/-- The actual independent uniform initialization satisfies the one-bit coverage bound. -/
theorem UniformOneBitRuntimeBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N) :
    ExpectedRuntime (RandomOneBitMutation hn) (PopulationInit n N) ≤
      ENNReal.ofReal (4 * (n : ℝ) * (harmonic (n + 1) : ℝ)) :=
  OneBitRuntimeBound hn Room (PopulationInit n N) (PopulationInitLength n N)

/-- The actual independent uniform initialization satisfies the standard-bit coverage bound. -/
theorem UniformStandardRuntimeBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N) :
    ExpectedRuntime (StandardBitMutation hn) (PopulationInit n N) ≤
      ENNReal.ofReal (4 * Real.exp 1 * (n : ℝ) * (harmonic (n + 1) : ℝ)) :=
  StandardRuntimeBound hn Room (PopulationInit n N) (PopulationInitLength n N)

/-- Explicit O(n log n) expected generations from any fixed-size initial law.
Population size N influences the admissible capacity and evaluation cost. -/
theorem StandardRuntimeLogBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime (StandardBitMutation hn) Initial ≤
      ENNReal.ofReal (4 * Real.exp 1 * (n : ℝ) * (1 + Real.log ((n : ℝ) + 1))) := by
  apply (StandardRuntimeBound hn Room Initial Initially).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)

/-- The standard-bit bound excludes divergent expected coverage time. -/
theorem StandardRuntimeFinite {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedRuntime (StandardBitMutation hn) Initial ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (StandardRuntimeBound hn Room Initial Initially)

/-- Starting with current full-front coverage gives zero generations, regardless
of mutation or whether later generations change representatives. -/
theorem RuntimeOfComplete {n : ℕ} (Mutation : Bits n → PMF (Bits n))
    (Pool : List (Bits n)) (Covered : Complete Pool) : ExpectedRuntime Mutation (PMF.pure Pool) = 0 :=
  ExpectedHittingTimeOfPureTarget _ _ _ Covered

/-- Under the fixed-cost model, N initialization evaluations and N evaluations
per completed generation give exactly N+N*E[T], including infinite expectations.
Interpreting this as this algorithm's cost requires initial length N; the runtime
bound below supplies that premise and the size invariant preserves it. -/
theorem EvaluationCostEq {n : ℕ} (Mutation : Bits n → PMF (Bits n))
    (Initial : PMF (List (Bits n))) (N : ℕ) :
    ExpectedEvaluationCost (NSGAIIStep Mutation Fitness) Complete Initial N N =
      (N : ENNReal) + (N : ENNReal) * ExpectedRuntime Mutation Initial :=
  ExpectedEvaluationCostEq _ _ _ _ _

/-- O(N n log n) expected evaluations for standard-bit NSGA-II, charging all
initial individuals and all offspring through the first successful generation. -/
theorem StandardEvaluationBound {n N : ℕ} (hn : 0 < n) (Room : 4 * (n + 1) ≤ N)
    (Initial : PMF (List (Bits n))) (Initially : ∀ P ∈ Initial.support, P.length = N) :
    ExpectedEvaluationCost (NSGAIIStep (StandardBitMutation hn) Fitness) Complete Initial N N ≤
      (N : ENNReal) + (N : ENNReal) * ENNReal.ofReal
        (4 * Real.exp 1 * (n : ℝ) * (1 + Real.log ((n : ℝ) + 1))) := by
  rw [EvaluationCostEq]
  gcongr
  exact StandardRuntimeLogBound hn Room Initial Initially

end
end ECTheoryLib.Analysis.NSGAIIOneMinMax
