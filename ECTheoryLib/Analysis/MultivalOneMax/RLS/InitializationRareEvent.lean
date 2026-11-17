import ECTheoryLib.Probability.Conditioning.RareEventConditioning
import ECTheoryLib.Analysis.MultivalOneMax.RLS.InitializationOneSidedConcentration

/-!
# Excluding unusually distant initial states

Apply Cantelli to the true uniform initialization, then use the general
conditioning bounds for every event. The cutoff retains positive probability
when its squared offset is at least the actual variance. Empty strings and
single-symbol alphabets are included. Conditional coordinates need not be independent.
-/

namespace ECTheoryLib.Analysis.RLSMultival
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.MultivalOneMax
noncomputable section

/-- Keep initial distances no more than c above their actual mean. -/
def UniformHammingUpperCutoff {n r : ℕ} (Target : MultiValues n r) (c : ℝ) : Set (MultiValues n r) :=
  {y | (Hamming Target y : ℝ) ≤ (n : ℝ) * (1 - 1 / (r : ℝ)) + c}

/-- The actual removed probability is bounded by Cantelli; strict and closed tails are distinguished. -/
theorem UniformHammingCutoffComplementBound {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveOffset : 0 < c) :
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real (UniformHammingUpperCutoff Target c)ᶜ ≤
      ((n : ℝ) * (1 - 1/(r : ℝ)) * (1/(r : ℝ))) /
        ((n : ℝ) * (1 - 1/(r : ℝ)) * (1/(r : ℝ)) + c^2) := by
  have Bound := UniformHammingUpperDeviationProbability PositiveAlphabet Target c PositiveOffset
  apply le_trans ?_ Bound
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro y Excluded
  change ¬(Hamming Target y : ℝ) ≤ (n : ℝ) * (1-1/(r : ℝ)) + c at Excluded
  exact (lt_of_not_ge Excluded).le

private theorem CutoffErrorHalf {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveOffset : 0 < c)
    (OffsetLarge : (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) ≤ c^2) :
    ((n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ))) /
      ((n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) + c^2) ≤ 1/2 := by
  have NonnegativeVariance : 0 ≤ (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) := by
    rw [← UniformHammingVariance PositiveAlphabet Target]
    exact variance_nonneg _ _
  have DenominatorPositive : 0 < (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) + c^2 := by
    nlinarith [sq_pos_of_pos PositiveOffset]
  apply (div_le_iff₀ DenominatorPositive).mpr
  linarith

/-- The cutoff retains at least half the initial probability, so conditioning is legitimate. -/
theorem UniformHammingCutoffPositive {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveOffset : 0 < c)
    (OffsetLarge : (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) ≤ c^2) :
    0 < (MultivalRLSInit n r PositiveAlphabet).toMeasure (UniformHammingUpperCutoff Target c) := by
  have ExcludedHalf := le_trans (UniformHammingCutoffComplementBound PositiveAlphabet Target c PositiveOffset)
    (CutoffErrorHalf PositiveAlphabet Target c PositiveOffset OffsetLarge)
  have Decomposition := measureReal_add_measureReal_compl (μ := (MultivalRLSInit n r PositiveAlphabet).toMeasure)
    ((Set.to_countable (UniformHammingUpperCutoff Target c)).measurableSet)
  rw [probReal_univ] at Decomposition
  have PositiveReal : 0 < (MultivalRLSInit n r PositiveAlphabet).toMeasure.real (UniformHammingUpperCutoff Target c) := by
    linarith
  exact ENNReal.toReal_pos_iff.mp PositiveReal |>.1

/-- Every event has controlled probability after excluding unusually distant initial states. -/
theorem UniformHammingCutoffConditioningBounds {n r : ℕ} (PositiveAlphabet : 0 < r)
    (Target : MultiValues n r) (c : ℝ) (PositiveOffset : 0 < c)
    (OffsetLarge : (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ)) ≤ c^2)
    (A : Set (MultiValues n r)) :
    let V := (n : ℝ) * (1-1/(r : ℝ)) * (1/(r : ℝ))
    (MultivalRLSInit n r PositiveAlphabet).toMeasure.real A - V/(V+c^2) ≤
        ((MultivalRLSInit n r PositiveAlphabet).toMeasure[|UniformHammingUpperCutoff Target c]).real A ∧
      ((MultivalRLSInit n r PositiveAlphabet).toMeasure[|UniformHammingUpperCutoff Target c]).real A ≤
        (MultivalRLSInit n r PositiveAlphabet).toMeasure.real A + 2 * (V/(V+c^2)) := by
  apply ConditionalEventAdditiveOfComplementBound _ A (UniformHammingUpperCutoff Target c)
    (Set.to_countable A).measurableSet (Set.to_countable _).measurableSet
  · exact UniformHammingCutoffComplementBound PositiveAlphabet Target c PositiveOffset
  · exact CutoffErrorHalf PositiveAlphabet Target c PositiveOffset OffsetLarge

end
end ECTheoryLib.Analysis.RLSMultival
