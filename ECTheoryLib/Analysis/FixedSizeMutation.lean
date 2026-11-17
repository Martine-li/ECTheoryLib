import ECTheoryLib.Probability.Sampling.Hypergeometric
import ECTheoryLib.Algorithms.FixedSizeRLS

/-!
# Concentration of actual fixed-size mutation and selected local search

Proposal counts on m distinct observed coordinates use both tails. The
selected successor inherits upper displacement bounds because rejection
returns the parent. Lower proposal bounds are not claimed after selection.
-/

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

/-- Actual k-bit mutation concentration on a region of m distinct coordinates.
The mean is mk/n even though the mutation indicators are dependent. -/
theorem ProposalObservedUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))) := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip] using
    UniformSubset.ObservedCountUpperTail Admissible Observed Injective d Nonnegative

/-- The actual selected local-search step inherits the proposal's upper tail.
No independence of mutation positions or special objective is assumed. -/
theorem StepObservedUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        Real.exp (-((1+d)*Real.log (1+d)-d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))) := by
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (FixedSizeBitMutation Admissible Parent).toMeasure.real
        {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Child Member
      change (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤
        (ObservedBitDifference Observed Parent (ElitistSelect NotWorse Parent Child) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (ElitistObservedBitDifferenceLe Observed NotWorse Parent Child))
    _ ≤ _ := ProposalObservedUpperTail Admissible Observed Injective Parent d Nonnegative

end
end ECTheoryLib.Analysis.FixedSizeMutation

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

theorem ProposalObservedFiniteUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        FiniteChernoffUpperBound m ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip] using
    UniformSubset.ObservedCountFiniteUpperTail Admissible Observed Injective d Nonnegative

/-- Lower concentration describes the proposed mutation, before selection. -/
theorem ProposalObservedFiniteLowerTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (ObservedBitDifference Observed Parent Child : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))}≤
        FiniteChernoffLowerBound m ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip] using
    UniformSubset.ObservedCountFiniteLowerTail Admissible Observed Injective d InUnit

theorem StepObservedFiniteUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        FiniteChernoffUpperBound m ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (FixedSizeBitMutation Admissible Parent).toMeasure.real
        {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Child Member
      change (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤
        (ObservedBitDifference Observed Parent (ElitistSelect NotWorse Parent Child) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (ElitistObservedBitDifferenceLe Observed NotWorse Parent Child))
    _ ≤ _ := ProposalObservedFiniteUpperTail Admissible Observed Injective Parent d Nonnegative

end
end ECTheoryLib.Analysis.FixedSizeMutation

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory Set ECTheoryLib.Probability
noncomputable section

/-- Exact region displacement law for the actual proposed mutation. -/
theorem ProposalObservedProbability {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (r : ℕ) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | ObservedBitDifference Observed Parent Child=r}=
        UniformSubset.HypergeometricMass n k m r := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip,UniformSubset.HypergeometricMass] using
    UniformSubset.ObservedCountProbability Admissible Observed Injective r

theorem ProposalObservedMinUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        FiniteChernoffUpperBound (min k m) ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip] using
    UniformSubset.ObservedCountMinUpperTail Admissible Observed Injective d Nonnegative

theorem ProposalObservedMinLowerTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (Parent : Bits n) (d : ℝ) (InUnit : d∈Icc 0 1) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (ObservedBitDifference Observed Parent Child : ℝ)≤(1-d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))}≤
        FiniteChernoffLowerBound (min k m) ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  simpa only [Set.preimage_ofPred_eq,ObservedBitDifferenceFlip] using
    UniformSubset.ObservedCountMinLowerTail Admissible Observed Injective d InUnit

theorem StepObservedMinUpperTail {n k m : ℕ} (Admissible : k≤n)
    (Observed : Fin m → Fin n) (Injective : Function.Injective Observed)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)}≤
        FiniteChernoffUpperBound (min k m) ((m : ℝ)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (FixedSizeBitMutation Admissible Parent).toMeasure.real
        {Child | (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤(ObservedBitDifference Observed Parent Child : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Child Member
      change (1+d)*((m : ℝ)*((k : ℝ)/(n : ℝ)))≤
        (ObservedBitDifference Observed Parent (ElitistSelect NotWorse Parent Child) : ℝ) at Member
      exact Member.trans (Nat.cast_le.mpr (ElitistObservedBitDifferenceLe Observed NotWorse Parent Child))
    _ ≤ _ := ProposalObservedMinUpperTail Admissible Observed Injective Parent d Nonnegative

end
end ECTheoryLib.Analysis.FixedSizeMutation
