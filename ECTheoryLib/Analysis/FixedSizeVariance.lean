import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationVariance
import ECTheoryLib.Analysis.FixedSizeWeightedMutation

/-!
# Marginal variance bounds for actual fixed-size mutation

Coordinate contributions have variance sum q*(1-q)*sum(weights^2),
q=k/n, proved on both the sampling law and the actual mutation PMF. For
weights in[0,1], two Bennett tails and an arbitrary selected upper tail
follow. The statistic is weighted displacement, not objective gain.
The total variance need not equal the marginal sum.
-/

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

/-- Sum of marginal coordinate variances for fixed-size sampling.
It is not the variance of the total weighted displacement. -/
def WeightedVarianceProxy (n k : ℕ) (Weights : Fin n → ℝ) : ℝ :=
  ((k : ℝ)/(n : ℝ))*(1-(k : ℝ)/(n : ℝ))*(∑ i, (Weights i)^2)

theorem SubsetWeightedMarginalVariance {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) :
    (∑ i : Fin n, variance (fun U : Finset (Fin n) => Weights i*
      {V : Finset (Fin n) | i∈V}.indicator (fun _ => (1 : ℝ)) U)
        (UniformSubset.Law n k Admissible).toMeasure)=WeightedVarianceProxy n k Weights := by
  have Each (i : Fin n) := AffineIndicatorVariance (UniformSubset.Law n k Admissible).toMeasure
    {V : Finset (Fin n) | i∈V} ((Set.to_countable _).measurableSet) 0 (Weights i) (NonnegativeWeights i)
  simp only [sub_zero,zero_add,UniformSubset.Marginal] at Each
  simp_rw [Each]
  unfold WeightedVarianceProxy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The proxy is also the actual marginal variance sum on the proposal PMF. -/
theorem ProposalWeightedMarginalVariance {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (Parent : Bits n) :
    (∑ i : Fin n, variance (fun Child : Bits n => if Child i≠Parent i then Weights i else 0)
      (FixedSizeBitMutation Admissible Parent).toMeasure)=WeightedVarianceProxy n k Weights := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  simp_rw [variance_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable]
  have Coordinate (i : Fin n) :
      (fun Child : Bits n => if Child i≠Parent i then Weights i else 0) ∘ FlipBitSubset Parent=
        (fun U : Finset (Fin n) => Weights i*{V : Finset (Fin n) | i∈V}.indicator (fun _ => (1 : ℝ)) U) := by
    funext U
    simp only [Function.comp_apply,FlipBitSubsetChanged]
    by_cases Inside : i∈U <;> simp [Inside]
  simp_rw [Coordinate]
  exact SubsetWeightedMarginalVariance Admissible Weights NonnegativeWeights

theorem ProposalWeightedBennettUpper {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
      BennettUpperBound (WeightedVarianceProxy n k Weights) d := by
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
  have Bound := OneNegativeCorrelationAffineBennettUpper (UniformSubset.Law n k Admissible).toMeasure
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

theorem ProposalWeightedBennettLower {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | WeightedDisplacement Weights Parent Child≤(∑ i, Weights i)*((k : ℝ)/(n : ℝ))-d}≤
      BennettUpperBound (WeightedVarianceProxy n k Weights) d := by
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
  have Bound := ZeroNegativeCorrelationAffineBennettLower (UniformSubset.Law n k Admissible).toMeasure
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

theorem StepWeightedBennettUpper {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i) (AtMostOne : ∀ i, Weights i≤1)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
      BennettUpperBound (WeightedVarianceProxy n k Weights) d := by
  have DistanceBound (Child : Bits n) :
      WeightedDisplacement Weights Parent (ElitistSelect NotWorse Parent Child)≤
        WeightedDisplacement Weights Parent Child := by
    exact ElitistWeightedDisplacementLe Weights NonnegativeWeights NotWorse Parent Child
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  apply le_trans _ (ProposalWeightedBennettUpper Admissible Weights NonnegativeWeights AtMostOne Parent d Nonnegative)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro Child Member
  exact le_trans Member (DistanceBound Child)

end
end ECTheoryLib.Analysis.FixedSizeMutation
