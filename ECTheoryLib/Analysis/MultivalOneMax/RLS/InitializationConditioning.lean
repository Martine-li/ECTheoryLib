import ECTheoryLib.Analysis.MultivalOneMax.RLS.UniformInitialLaw
import ECTheoryLib.Probability.Distributions.BinomialConditioning

/-!
# Distance-conditioned actual uniform initialization

For an alphabet of at least two symbols and a threshold x<=n, the event of
initial distance at least x has positive probability. Its true conditional
distance law lies between the original distance law and that law shifted by x.
Targets are arbitrary. This is a statement about time-zero conditioning, not
about subsequent trajectories or runtime domination.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- For at least two symbols, conditioning uniform initialization on distance at least x<=n is possible. -/
theorem UniformHammingConditionEventPositive {n r : ℕ} (PositiveAlphabet : 0 < r)
    (NontrivialAlphabet : 2 ≤ r) (Target : MultiValues n r) (x : ℕ) (Threshold : x ≤ n) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure {y | x ≤ Hamming Target y} ≠ 0 := by
  have PositiveReal : (0 : ℝ) < r := by exact_mod_cast PositiveAlphabet
  have GreaterThanOne : (1 : ℝ) < r := by exact_mod_cast NontrivialAlphabet
  have ReciprocalBelowOne : (1 : ℝ) / r < 1 := (div_lt_one PositiveReal).mpr GreaterThanOne
  have PositiveMismatch : 0 < (MismatchProbability r PositiveAlphabet : ℝ) := by
    change 0 < 1 - 1 / (r : ℝ)
    linarith
  have ImagePositive := BinomialUpperTailPositive n x (MismatchProbability r PositiveAlphabet)
    Threshold PositiveMismatch
  rw [← UniformHammingBinomial PositiveAlphabet Target,
    Measure.map_apply (measurable_of_finite (Hamming Target)) measurableSet_Ici] at ImagePositive
  exact ImagePositive

/-- The actual conditional initialization has the corresponding conditional binomial distance law. -/
theorem UniformHammingConditionalLaw {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (x : ℕ) :
    HasLaw (Hamming Target) (cond (binomial n (MismatchProbability r PositiveAlphabet)) (Set.Ici x))
      (cond (MultivalRLSInit n r PositiveAlphabet).toMeasure {y | x ≤ Hamming Target y}) := by
  refine ⟨(measurable_of_finite _).aemeasurable, ?_⟩
  change (cond (MultivalRLSInit n r PositiveAlphabet).toMeasure
    ((Hamming Target) ⁻¹' Set.Ici x)).map (Hamming Target) = _
  rw [ConditionalMap _ _ (measurable_of_finite _) _ measurableSet_Ici,
    UniformHammingBinomial]

/-- Complete lower and upper distribution bounds for actual uniform initialization conditioned on distance. -/
theorem UniformHammingConditionalBounds {n r : ℕ} (PositiveAlphabet : 0 < r)
    (NontrivialAlphabet : 2 ≤ r) (Target : MultiValues n r) (x : ℕ) (Threshold : x ≤ n) :
    StochasticDominated
        ((MultivalRLSInit n r PositiveAlphabet).toMeasure.map (Hamming Target))
        ((cond (MultivalRLSInit n r PositiveAlphabet).toMeasure
          {y | x ≤ Hamming Target y}).map (Hamming Target)) ∧
      StochasticDominated
        ((cond (MultivalRLSInit n r PositiveAlphabet).toMeasure
          {y | x ≤ Hamming Target y}).map (Hamming Target))
        ((MultivalRLSInit n r PositiveAlphabet).toMeasure.map (fun y => Hamming Target y + x)) := by
  have PositiveEvent := UniformHammingConditionEventPositive PositiveAlphabet
    NontrivialAlphabet Target x Threshold
  have PositiveBinomial : binomial n (MismatchProbability r PositiveAlphabet) (Set.Ici x) ≠ 0 := by
    rw [← UniformHammingBinomial PositiveAlphabet Target,
      Measure.map_apply (measurable_of_finite (Hamming Target)) measurableSet_Ici]
    exact PositiveEvent
  have ShiftedLaw : (MultivalRLSInit n r PositiveAlphabet).toMeasure.map
      (fun y => Hamming Target y + x) =
        (binomial n (MismatchProbability r PositiveAlphabet)).map (fun j => j + x) := by
    change Measure.map ((fun j : ℕ => j + x) ∘ Hamming Target) _ = _
    rw [← Measure.map_map (measurable_of_countable (fun j : ℕ => j + x))
      (measurable_of_finite (Hamming Target)), UniformHammingBinomial]
  rw [UniformHammingBinomial, (UniformHammingConditionalLaw PositiveAlphabet Target x).map_eq,
    ShiftedLaw]
  exact ConditionalBinomialBounds n x _ Threshold PositiveBinomial

end
end ECTheoryLib.Analysis.RLSMultival
