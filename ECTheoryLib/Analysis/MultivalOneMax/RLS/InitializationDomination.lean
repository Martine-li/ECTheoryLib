import ECTheoryLib.Analysis.MultivalOneMax.RLS.UniformInitialLaw
import ECTheoryLib.Probability.Distributions.BinomialDomination

/-!
# Stochastic comparison of actual uniform RLS initialization

Longer strings and larger nonempty alphabets increase the initial Hamming
distance in stochastic order. Each target and search space may differ. The
existing initialization theorem supplies both complete binomial laws; callers
do not assume independent coordinates or a surrogate initialization model.
These statements concern time zero, not an ordering of algorithm runtimes.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- A larger alphabet makes a uniform coordinate at least as likely to mismatch. -/
theorem MismatchProbabilityMonotone {r s : ℕ} (PositiveR : 0 < r)
    (PositiveS : 0 < s) (Alphabets : r ≤ s) :
    MismatchProbability r PositiveR ≤ MismatchProbability s PositiveS := by
  change 1 - 1 / (r : ℝ) ≤ 1 - 1 / (s : ℝ)
  have PositiveRealR : (0 : ℝ) < r := by exact_mod_cast PositiveR
  have AlphabetOrder : (r : ℝ) ≤ s := by exact_mod_cast Alphabets
  have ReciprocalOrder : (1 : ℝ) / s ≤ 1 / r :=
    one_div_le_one_div_of_le PositiveRealR AlphabetOrder
  exact sub_le_sub_left ReciprocalOrder 1

/-- The actual initial-distance laws increase with length and alphabet size. -/
theorem UniformHammingStochasticDominated {n m r s : ℕ}
    (PositiveR : 0 < r) (PositiveS : 0 < s) (Lengths : n ≤ m) (Alphabets : r ≤ s)
    (TargetR : MultiValues n r) (TargetS : MultiValues m s) :
    StochasticDominated
      ((MultivalRLSInit n r PositiveR).toMeasure.map (Hamming TargetR))
      ((MultivalRLSInit m s PositiveS).toMeasure.map (Hamming TargetS)) := by
  rw [UniformHammingBinomial, UniformHammingBinomial]
  exact BinomialStochasticDominated n m _ _ Lengths
    (MismatchProbabilityMonotone PositiveR PositiveS Alphabets)

/-- Comparison at every initial-distance threshold, for the actual two PMFs. -/
theorem UniformHammingTailMonotone {n m r s : ℕ}
    (PositiveR : 0 < r) (PositiveS : 0 < s) (Lengths : n ≤ m) (Alphabets : r ≤ s)
    (TargetR : MultiValues n r) (TargetS : MultiValues m s) (k : ℕ) :
    (MultivalRLSInit n r PositiveR).toMeasure {x | k < Hamming TargetR x} ≤
      (MultivalRLSInit m s PositiveS).toMeasure {x | k < Hamming TargetS x} := by
  have SmallProbability : IsProbabilityMeasure
      ((MultivalRLSInit n r PositiveR).toMeasure.map (Hamming TargetR)) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite (Hamming TargetR)).aemeasurable
  have LargeProbability : IsProbabilityMeasure
      ((MultivalRLSInit m s PositiveS).toMeasure.map (Hamming TargetS)) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite (Hamming TargetS)).aemeasurable
  have Domination := UniformHammingStochasticDominated PositiveR PositiveS
    Lengths Alphabets TargetR TargetS
  have TailOrder := (StochasticDominatedIffStrictTail _ _).mp Domination k
  rw [Measure.map_apply (measurable_of_finite (Hamming TargetR)) measurableSet_Ioi,
    Measure.map_apply (measurable_of_finite (Hamming TargetS)) measurableSet_Ioi] at TailOrder
  exact TailOrder

end
end ECTheoryLib.Analysis.RLSMultival
