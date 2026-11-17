import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationFiniteVariance
import ECTheoryLib.Analysis.FixedSizeVariance

/-!
# Finite-size variance tails of actual fixed-size mutation

Reuse the actual weighted-displacement mean and marginal variance sum
from FixedSizeVariance. Unit-interval weights yield both candidate
tails; arbitrary elitist selection preserves the upper displacement tail.
-/

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

theorem ProposalWeightedFiniteVarianceUpper {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
      VarianceFiniteUpperBound n (WeightedVarianceProxy n k Weights) d := by
  have Bounds (i : Fin n) : ∀ᵐ U ∂(UniformSubset.Law n k Admissible).toMeasure,
      0+(Weights i-0)*{V : Finset (Fin n) | i∈V}.indicator (fun _ => (1 : ℝ)) U≤
        (∫ V, 0+(Weights i-0)*{W : Finset (Fin n) | i∈W}.indicator (fun _ => (1 : ℝ)) V
          ∂(UniformSubset.Law n k Admissible).toMeasure)+1 := by
    rw [AffineIndicatorIntegral]
    · apply ae_of_all
      intro U
      have NonnegativeMean : 0≤(Weights i)*((UniformSubset.Law n k Admissible).toMeasure.real {V | i∈V}) :=
        mul_nonneg (NonnegativeWeights i) ENNReal.toReal_nonneg
      have Bounded := AffineIndicatorInUnit {V : Finset (Fin n) | i∈V} 0 (Weights i)
        (NonnegativeWeights i) le_rfl (AtMostOne i) U
      simp only [sub_zero,zero_add] at Bounded ⊢
      linarith [Bounded.2]
    · exact (Set.to_countable _).measurableSet
  have Bound := OneNegativeCorrelationFiniteVarianceUpper (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.OneNegativeCorrelation Admissible) (fun _ => 0) Weights NonnegativeWeights Bounds d Nonnegative
  rw [AffineSumIntegral] at Bound
  · simp only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul] at Bound
    rw [SubsetWeightedMarginalVariance Admissible Weights NonnegativeWeights] at Bound
    unfold FixedSizeBitMutation
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
      map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
    simpa only [WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound
  · exact fun _ => (Set.to_countable _).measurableSet

theorem ProposalWeightedFiniteVarianceLower {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | WeightedDisplacement Weights Parent Child≤(∑ i, Weights i)*((k : ℝ)/(n : ℝ))-d}≤
      VarianceFiniteUpperBound n (WeightedVarianceProxy n k Weights) d := by
  have Bounds (i : Fin n) : ∀ᵐ U ∂(UniformSubset.Law n k Admissible).toMeasure,
      (∫ V, 0+(Weights i-0)*{W : Finset (Fin n) | i∈W}.indicator (fun _ => (1 : ℝ)) V
          ∂(UniformSubset.Law n k Admissible).toMeasure)-1≤
        0+(Weights i-0)*{V : Finset (Fin n) | i∈V}.indicator (fun _ => (1 : ℝ)) U := by
    rw [AffineIndicatorIntegral]
    · apply ae_of_all
      intro U
      have MeanBound : (Weights i)*((UniformSubset.Law n k Admissible).toMeasure.real {V | i∈V})≤1 :=
        (mul_le_mul_of_nonneg_left measureReal_le_one (NonnegativeWeights i)).trans (by simpa using AtMostOne i)
      have Bounded := AffineIndicatorInUnit {V : Finset (Fin n) | i∈V} 0 (Weights i)
        (NonnegativeWeights i) le_rfl (AtMostOne i) U
      simp only [sub_zero,zero_add] at Bounded ⊢
      linarith [Bounded.1]
    · exact (Set.to_countable _).measurableSet
  have Bound := ZeroNegativeCorrelationFiniteVarianceLower (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.ZeroNegativeCorrelation Admissible) (fun _ => 0) Weights NonnegativeWeights Bounds d Nonnegative
  rw [AffineSumIntegral] at Bound
  · simp only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul] at Bound
    rw [SubsetWeightedMarginalVariance Admissible Weights NonnegativeWeights] at Bound
    unfold FixedSizeBitMutation
    rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
      map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
    simpa only [WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound
  · exact fun _ => (Set.to_countable _).measurableSet

theorem StepWeightedFiniteVarianceUpper {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
      VarianceFiniteUpperBound n (WeightedVarianceProxy n k Weights) d := by
  have DistanceBound (Child : Bits n) :
      WeightedDisplacement Weights Parent (ElitistSelect NotWorse Parent Child)≤
        WeightedDisplacement Weights Parent Child := by
    exact ElitistWeightedDisplacementLe Weights NonnegativeWeights NotWorse Parent Child
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  apply le_trans _ (ProposalWeightedFiniteVarianceUpper Admissible Weights NonnegativeWeights AtMostOne Parent d Nonnegative)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro Child Member
  exact le_trans Member (DistanceBound Child)

end
end ECTheoryLib.Analysis.FixedSizeMutation
