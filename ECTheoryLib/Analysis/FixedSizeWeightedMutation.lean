import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationChernoff
import ECTheoryLib.Algorithms.FixedSizeRLS
import ECTheoryLib.Probability.NegativeDependence.NegativeCorrelationHoeffding

/-!
# Weighted displacement of actual fixed-size mutation

The proposal has exact mean (k/n) times the sum of coordinate weights.
Nonnegative weights yield two Hoeffding tails; arbitrary survivor selection
preserves the upper displacement estimate. The statistic measures changed
coordinates with weights, not objective gain or total runtime.
-/

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

/-- Sum of caller-supplied coordinate weights over the positions that changed. -/
def WeightedDisplacement {n : ℕ} (Weights : Fin n → ℝ) (Parent Child : Bits n) : ℝ :=
  ∑ i, if Child i≠Parent i then Weights i else 0

theorem WeightedDisplacementSelf {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n) :
    WeightedDisplacement Weights Parent Parent=0 := by simp [WeightedDisplacement]

theorem WeightedDisplacementNonnegative {n : ℕ} (Weights : Fin n → ℝ)
    (Nonnegative : ∀ i, 0≤Weights i) (Parent Child : Bits n) :
    0≤WeightedDisplacement Weights Parent Child := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact Nonnegative i
  · exact le_rfl

/-- Elitist parent/candidate selection cannot increase displacement with
nonnegative coordinate weights. The comparison relation may be arbitrary. -/
theorem ElitistWeightedDisplacementLe {n : ℕ} (Weights : Fin n → ℝ)
    (NonnegativeWeights : ∀ i, 0≤Weights i)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent Child : Bits n) :
    WeightedDisplacement Weights Parent (ElitistSelect NotWorse Parent Child)≤
      WeightedDisplacement Weights Parent Child := by
  unfold ElitistSelect
  split_ifs
  · exact le_rfl
  · rw [WeightedDisplacementSelf]
    exact WeightedDisplacementNonnegative Weights NonnegativeWeights Parent Child

theorem WeightedDisplacementFlip {n : ℕ} (Weights : Fin n → ℝ)
    (Parent : Bits n) (Positions : Finset (Fin n)) :
    WeightedDisplacement Weights Parent (FlipBitSubset Parent Positions)=
      ∑ i, Weights i*{U : Finset (Fin n) | i∈U}.indicator (fun _ => (1 : ℝ)) Positions := by
  unfold WeightedDisplacement
  simp only [FlipBitSubsetChanged]
  apply Finset.sum_congr rfl
  intro i _
  by_cases Inside : i∈Positions <;> simp [Inside]

/-- Exact weighted proposal mean from the actual without-replacement law. -/
theorem ProposalWeightedExpectation {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (Parent : Bits n) :
    (∫ Child, WeightedDisplacement Weights Parent Child ∂(FixedSizeBitMutation Admissible Parent).toMeasure)=
      (∑ i, Weights i)*((k : ℝ)/(n : ℝ)) := by
  unfold FixedSizeBitMutation
  rw [PMFIntegralMap]
  simp_rw [WeightedDisplacementFlip]
  have Mean := AffineSumIntegral (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (fun _ => 0) Weights
  simp only [sub_zero,zero_add] at Mean
  rw [Mean]
  simp_rw [UniformSubset.Marginal Admissible]
  rw [Finset.sum_mul]

theorem ProposalWeightedUpperTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
        Real.exp (-2*d^2/(∑ i, (Weights i)^2)) := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  have Bound := OneNegativeCorrelationHoeffdingUpper (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.OneNegativeCorrelation Admissible) (fun _ => 0) Weights NonnegativeWeights d Nonnegative
  simpa only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul,
    WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound

theorem ProposalWeightedLowerTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | WeightedDisplacement Weights Parent Child≤(∑ i, Weights i)*((k : ℝ)/(n : ℝ))-d}≤
        Real.exp (-2*d^2/(∑ i, (Weights i)^2)) := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  have Bound := ZeroNegativeCorrelationHoeffdingLower (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.ZeroNegativeCorrelation Admissible) (fun _ => 0) Weights NonnegativeWeights d Nonnegative
  simpa only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul,
    WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound

/-- Arbitrary selection preserves the upper weighted-displacement estimate
when all coordinate weights are nonnegative. -/
theorem StepWeightedUpperTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (NonnegativeWeights : ∀ i, 0≤Weights i)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child}≤
        Real.exp (-2*d^2/(∑ i, (Weights i)^2)) := by
  have DistanceBound (Child : Bits n) :
      WeightedDisplacement Weights Parent (ElitistSelect NotWorse Parent Child)≤
        WeightedDisplacement Weights Parent Child := by
    exact ElitistWeightedDisplacementLe Weights NonnegativeWeights NotWorse Parent Child
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (FixedSizeBitMutation Admissible Parent).toMeasure.real
        {Child | (∑ i, Weights i)*((k : ℝ)/(n : ℝ))+d≤WeightedDisplacement Weights Parent Child} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Child Member
      exact le_trans Member (DistanceBound Child)
    _ ≤ _ := ProposalWeightedUpperTail Admissible Weights NonnegativeWeights Parent d Nonnegative

end
end ECTheoryLib.Analysis.FixedSizeMutation

namespace ECTheoryLib.Analysis.FixedSizeMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

/-- The actual weighted proposal with weights in [0,1] retains the strongest
finite-size correction. Its mean is ProposalWeightedExpectation. -/
theorem ProposalWeightedFiniteUpperTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (InUnit : ∀ i, Weights i∈Icc 0 1)
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | (1+d)*((∑ i, Weights i)*((k : ℝ)/(n : ℝ)))≤WeightedDisplacement Weights Parent Child}≤
        FiniteChernoffUpperBound n ((∑ i, Weights i)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  have Bound := OneNegativeCorrelationAffineFiniteChernoffUpper (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.OneNegativeCorrelation Admissible) (fun _ => 0) Weights (fun i => (InUnit i).1)
    (fun _ => le_rfl) (fun i => (InUnit i).2) d Nonnegative
  simpa only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul,
    WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound

theorem ProposalWeightedFiniteLowerTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (InUnit : ∀ i, Weights i∈Icc 0 1)
    (Parent : Bits n) (d : ℝ) (DeviationInUnit : d∈Icc 0 1) :
    (FixedSizeBitMutation Admissible Parent).toMeasure.real
      {Child | WeightedDisplacement Weights Parent Child≤(1-d)*((∑ i, Weights i)*((k : ℝ)/(n : ℝ)))}≤
        FiniteChernoffLowerBound n ((∑ i, Weights i)*((k : ℝ)/(n : ℝ))) d := by
  unfold FixedSizeBitMutation
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  have Bound := ZeroNegativeCorrelationAffineFiniteChernoffLower (UniformSubset.Law n k Admissible).toMeasure
    (fun i : Fin n => {U : Finset (Fin n) | i∈U}) (fun _ => (Set.to_countable _).measurableSet)
    (UniformSubset.ZeroNegativeCorrelation Admissible) (fun _ => 0) Weights (fun i => (InUnit i).1)
    (fun _ => le_rfl) (fun i => (InUnit i).2) d DeviationInUnit
  simpa only [sub_zero,zero_add,UniformSubset.Marginal,← Finset.sum_mul,
    WeightedDisplacementFlip,Set.preimage_ofPred_eq] using Bound

theorem StepWeightedFiniteUpperTail {n k : ℕ} (Admissible : k≤n)
    (Weights : Fin n → ℝ) (InUnit : ∀ i, Weights i∈Icc 0 1)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Parent : Bits n) (d : ℝ) (Nonnegative : 0≤d) :
    (FixedSizeRLSStep Admissible NotWorse Parent).toMeasure.real
      {Child | (1+d)*((∑ i, Weights i)*((k : ℝ)/(n : ℝ)))≤WeightedDisplacement Weights Parent Child}≤
        FiniteChernoffUpperBound n ((∑ i, Weights i)*((k : ℝ)/(n : ℝ))) d := by
  have DistanceBound (Child : Bits n) :
      WeightedDisplacement Weights Parent (ElitistSelect NotWorse Parent Child)≤
        WeightedDisplacement Weights Parent Child := by
    exact ElitistWeightedDisplacementLe Weights (fun i => (InUnit i).1) NotWorse Parent Child
  unfold FixedSizeRLSStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  calc
    _ ≤ (FixedSizeBitMutation Admissible Parent).toMeasure.real
        {Child | (1+d)*((∑ i, Weights i)*((k : ℝ)/(n : ℝ)))≤WeightedDisplacement Weights Parent Child} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro Child Member
      exact le_trans Member (DistanceBound Child)
    _ ≤ _ := ProposalWeightedFiniteUpperTail Admissible Weights InUnit Parent d Nonnegative

end
end ECTheoryLib.Analysis.FixedSizeMutation
