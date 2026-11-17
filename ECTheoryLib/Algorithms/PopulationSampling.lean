import ECTheoryLib.Algorithms.Population
import ECTheoryLib.Operators.Sampling.Batch

/-!
# Event probabilities under uniform parent sampling

The parent is sampled by occurrence, not by distinct genotype. For any event,
the offspring probability is the average of the mutation probabilities over all
positions. Thus multiplying by the population length dominates the mutation
probability from each particular parent occurrence, even with duplicates.
-/
namespace ECTheoryLib
open MeasureTheory Probability Operators.Sampling
noncomputable section

/-- Uniform-parent offspring event probability as an average over occurrences. -/
theorem PopulationOffspringEventAverage {α : Type*} [Countable α] [Inhabited α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (Mutation : α → PMF α) (Pool : List α) (Positive : 0 < Pool.length) (Event : α → Prop) :
    EventProbability (PopulationOffspring Mutation Pool) Event =
      (Pool.length : ℝ)⁻¹ * ∑ i : Fin Pool.length, EventProbability (Mutation Pool[i]) Event := by
  unfold EventProbability PopulationOffspring
  rw [PMFIntegralBindOfBounded _ _ _ 1 (EventValueBound Event)]
  unfold UniformParent
  rw [dif_pos Positive, PMFIntegralMapCountable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, Finset.mul_sum]

/-- N times the offspring event probability is at least the event probability
from any one represented parent; all other occurrences contribute nonnegatively. -/
theorem PopulationOffspringEventRate {α : Type*} [Countable α] [Inhabited α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (Mutation : α → PMF α) (Pool : List α) (x : α) (Present : x ∈ Pool) (Event : α → Prop) :
    EventProbability (Mutation x) Event ≤
      Pool.length * EventProbability (PopulationOffspring Mutation Pool) Event := by
  obtain ⟨i, Valid, AtX⟩ := List.mem_iff_getElem.mp Present
  have Positive : 0 < Pool.length := by omega
  rw [PopulationOffspringEventAverage Mutation Pool Positive Event, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt Positive), one_mul]
  have Bound := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => EventProbabilityNonnegative (Mutation Pool[j]) Event) (Finset.mem_univ (⟨i, Valid⟩ : Fin Pool.length))
  change EventProbability (Mutation Pool[i]) Event ≤ _ at Bound
  simpa only [AtX] using Bound

end
end ECTheoryLib
