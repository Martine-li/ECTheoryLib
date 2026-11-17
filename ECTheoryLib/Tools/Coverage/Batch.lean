import ECTheoryLib.Tools.Coverage.Finite
import ECTheoryLib.Operators.Sampling.Batch

/-!
# Weighted coverage gains for a batch of samples

These rules separate production of new values from their retention. They apply
to any finite target set and nonnegative weights. If an N-sample batch has a
per-sample probability floor of `1/N` times a reference sampling law, its expected
new-value weight is at least half that of one reference sample. An application
must still prove that its survivor rule retains both old values and batch values.
-/
namespace ECTheoryLib.Tools.Coverage
open MeasureTheory Probability Operators.Selection Operators.Sampling
noncomputable section
variable {ι : Type*} [DecidableEq ι]

/-- Weight still available at one target; already represented values contribute zero. -/
def DiscoveryWeight (Old : Finset ι) (Weight : ι → ℝ) (j : ι) : ℝ :=
  if j ∈ Old then 0 else Weight j

/-- Total weight of newly discovered target values; repeated discoveries count once. -/
def CoverageGain (Targets Old : Finset ι) (Weight : ι → ℝ) (Found : ι → Prop) : ℝ :=
  ∑ j ∈ Targets, DiscoveryWeight Old Weight j * EventValue Found j

theorem DiscoveryWeightNonnegative (Old : Finset ι) (Weight : ι → ℝ) (j : ι)
    (Nonnegative : 0 ≤ Weight j) : 0 ≤ DiscoveryWeight Old Weight j := by
  unfold DiscoveryWeight
  split_ifs
  · exact le_rfl
  · exact Nonnegative

theorem CoverageGainNonnegative (Targets Old : Finset ι) (Weight : ι → ℝ) (Found : ι → Prop)
    (Nonnegative : ∀ j ∈ Targets, 0 ≤ Weight j) : 0 ≤ CoverageGain Targets Old Weight Found :=
  Finset.sum_nonneg (fun j Present => mul_nonneg
    (DiscoveryWeightNonnegative Old Weight j (Nonnegative j Present)) (EventValueNonnegative Found j))

/-- A batch can discover no more than the total target weight, independent of
its length or the number of repeated samples. -/
theorem CoverageGainBound (Targets Old : Finset ι) (Weight : ι → ℝ) (Found : ι → Prop)
    (Nonnegative : ∀ j ∈ Targets, 0 ≤ Weight j) :
    CoverageGain Targets Old Weight Found ≤ ∑ j ∈ Targets, Weight j := by
  apply Finset.sum_le_sum
  intro j Present
  unfold DiscoveryWeight EventValue
  split_ifs
  · simpa only [zero_mul] using Nonnegative j Present
  · simpa only [zero_mul] using Nonnegative j Present
  · simp only [mul_one, le_refl]
  · simpa only [mul_zero] using Nonnegative j Present

/-- Retaining old values and every discovered target guarantees the claimed
potential decrease; no identities of representatives are required. -/
theorem CoverageGainLeDecrease (Targets Old New : Finset ι) (Weight : ι → ℝ)
    (Found : ι → Prop) (Nonnegative : ∀ j ∈ Targets, 0 ≤ Weight j)
    (Retained : Old ⊆ New) (Added : ∀ j ∈ Targets, Found j → j ∈ New) :
    CoverageGain Targets Old Weight Found ≤
      MissingWeight Targets Old Weight - MissingWeight Targets New Weight := by
  classical
  unfold CoverageGain MissingWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j Target
  by_cases Already : j ∈ Old
  · simp only [DiscoveryWeight, if_pos Already, if_pos (Retained Already), zero_mul, sub_self, le_refl]
  · by_cases Discovered : Found j
    · simp only [DiscoveryWeight, if_neg Already, EventValue, if_pos Discovered,
        if_pos (Added j Target Discovered), mul_one, sub_zero, le_refl]
    · simp only [DiscoveryWeight, if_neg Already, EventValue, if_neg Discovered, mul_zero]
      split_ifs
      · simpa only [sub_zero] using Nonnegative j Target
      · exact sub_self _ |>.ge

/-- Inserting one value decreases the missing-weight potential by exactly its
new target weight. Values outside the target set have zero gain. -/
theorem CoverageGainSingle (Targets Old : Finset ι) (Weight : ι → ℝ) (Value : ι) :
    CoverageGain Targets Old Weight (fun j => Value = j) =
      MissingWeight Targets Old Weight - MissingWeight Targets (insert Value Old) Weight := by
  classical
  unfold CoverageGain MissingWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases Already : j ∈ Old
  · simp [DiscoveryWeight, Already]
  · by_cases Same : Value = j
    · subst j
      simp [DiscoveryWeight, EventValue, Already]
    · simp [DiscoveryWeight, EventValue, Already, Same, Ne.symm Same]

/-- Expected weighted gain is the finite sum of target weights times their
discovery probabilities. Bounded indicators justify integration term by term. -/
theorem CoverageGainIntegral {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (Targets Old : Finset ι)
    (Weight : ι → ℝ) (Found : α → ι → Prop) :
    (∫ x, CoverageGain Targets Old Weight (Found x) ∂p.toMeasure) =
      ∑ j ∈ Targets, DiscoveryWeight Old Weight j * EventProbability p (fun x => Found x j) := by
  unfold CoverageGain
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    rfl
  · intro j _
    exact (PMFIntegrableOfBounded p _ 1 (EventValueBound (fun x => Found x j))).const_mul _

/-- Independent batch production preserves at least half the expected gain of
a reference law when each target's sampling probability has a `1/N` floor. -/
theorem CoverageBatchHalfReference {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace (List α)] [MeasurableSingletonClass (List α)]
    (p Reference : PMF α) (N : ℕ) (Value : α → ι) (Targets Old : Finset ι) (Weight : ι → ℝ)
    (Nonnegative : ∀ j ∈ Targets, 0 ≤ Weight j)
    (Rate : ∀ j ∈ Targets, EventProbability Reference (fun x => Value x = j) ≤
      N * EventProbability p (fun x => Value x = j)) :
    (∫ x, CoverageGain Targets Old Weight (fun j => Value x = j) ∂Reference.toMeasure) / 2 ≤
      ∫ L, CoverageGain Targets Old Weight (fun j => ∃ x ∈ L, Value x = j)
        ∂(IndependentSamples p N).toMeasure := by
  rw [CoverageGainIntegral, CoverageGainIntegral, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j Target
  have Probability := IndependentSamplesSuccessLower p (fun x => Value x = j) N
    (EventProbability Reference (fun x => Value x = j))
    (EventProbabilityLeOne Reference _) (Rate j Target)
  have Weighted := mul_le_mul_of_nonneg_left Probability
    (DiscoveryWeightNonnegative Old Weight j (Nonnegative j Target))
  simpa only [mul_div_assoc] using Weighted

end
end ECTheoryLib.Tools.Coverage
