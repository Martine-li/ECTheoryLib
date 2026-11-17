import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import Mathlib.Probability.ConditionalProbability

/-!
# Finite-support comparison and conditional distribution bridges

The likelihood-ratio criterion compares cross-products rather than dividing
point masses, retaining zeros and degenerate distributions. It uses Mathlib
finite additivity and probability normalization. Conditioning itself is Mathlib
cond; a positive event is required whenever it is interpreted as a probability
law. The map identity remains valid for the zero-measure convention as well.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- A finite-support likelihood-ratio order implies stochastic order; zero masses are allowed. -/
theorem StochasticDominatedOfFiniteLikelihoodRatio {α : Type*} [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Finset α) (FirstSupport : ∀ᵐ x ∂μ, x ∈ S) (SecondSupport : ∀ᵐ x ∂ν, x ∈ S)
    (RatioOrder : ∀ i ∈ S, ∀ j ∈ S, i ≤ j →
      ν.real {i} * μ.real {j} ≤ μ.real {i} * ν.real {j}) :
    StochasticDominated μ ν := by
  classical
  have FiniteEvent (ρ : Measure α) [IsProbabilityMeasure ρ]
      (Support : ∀ᵐ x ∂ρ, x ∈ S) (A : Set α) :
      ρ.real A = ∑ i ∈ S.filter (fun i => i ∈ A), ρ.real {i} := by
    rw [sum_measureReal_singleton]
    have EventEq : (S.filter (fun i => i ∈ A) : Set α) = (S : Set α) ∩ A := by
      ext i
      simp only [Finset.mem_coe, Finset.mem_filter, mem_inter_iff]
    rw [EventEq, measureReal_def, measureReal_def, Measure.measure_inter_eq_of_ae Support]
  intro a
  let Low := S.filter (fun i => i ≤ a)
  let High := S.filter (fun i => ¬ i ≤ a)
  have Total (ρ : Measure α) [IsProbabilityMeasure ρ]
      (Support : ∀ᵐ x ∂ρ, x ∈ S) :
      (∑ i ∈ Low, ρ.real {i}) + (∑ j ∈ High, ρ.real {j}) = 1 := by
    change (∑ i ∈ S.filter (fun i => i ≤ a), ρ.real {i}) +
      (∑ j ∈ S.filter (fun j => ¬ j ≤ a), ρ.real {j}) = 1
    rw [Finset.sum_filter_add_sum_filter_not, sum_measureReal_singleton]
    have Full : ρ (S : Set α) = 1 := by
      calc
        ρ (S : Set α) = ρ ((S : Set α) ∩ univ) := by rw [inter_univ]
        _ = ρ univ := Measure.measure_inter_eq_of_ae Support
        _ = 1 := measure_univ
    rw [measureReal_def, Full, ENNReal.toReal_one]
  have Cross : (∑ i ∈ Low, ν.real {i}) * (∑ j ∈ High, μ.real {j}) ≤
      (∑ i ∈ Low, μ.real {i}) * (∑ j ∈ High, ν.real {j}) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i InLow
    apply Finset.sum_le_sum
    intro j InHigh
    have LowMembership := Finset.mem_filter.mp InLow
    have HighMembership := Finset.mem_filter.mp InHigh
    exact RatioOrder i LowMembership.1 j HighMembership.1
      (le_trans LowMembership.2 (le_of_lt (lt_of_not_ge HighMembership.2)))
  have FirstTotal := Total μ FirstSupport
  have SecondTotal := Total ν SecondSupport
  have FirstHigh : (∑ j ∈ High, μ.real {j}) = 1 - ∑ i ∈ Low, μ.real {i} := by
    linarith
  have SecondHigh : (∑ j ∈ High, ν.real {j}) = 1 - ∑ i ∈ Low, ν.real {i} := by
    linarith
  rw [FirstHigh, SecondHigh] at Cross
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ν.real (Iic a) ≤ μ.real (Iic a)
  rw [FiniteEvent ν SecondSupport, FiniteEvent μ FirstSupport]
  simp only [mem_Iic]
  change (∑ i ∈ Low, ν.real {i}) ≤ ∑ i ∈ Low, μ.real {i}
  nlinarith

/-- A conditional point mass, with the same zero-event convention as Mathlib cond. -/
theorem ConditionalSingletonReal {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) (A : Set α) [DecidablePred (· ∈ A)] (i : α) :
    (cond μ A).real {i} = (if i ∈ A then μ.real {i} else 0) / μ.real A := by
  classical
  rw [measureReal_def, cond_apply' (measurableSet_singleton i), ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  by_cases Member : i ∈ A
  · rw [Set.inter_singleton_of_mem Member, if_pos Member]
    change (μ A).toReal⁻¹ * (μ {i}).toReal = (μ {i}).toReal / (μ A).toReal
    rw [div_eq_mul_inv, mul_comm]
  · rw [Set.inter_singleton_of_notMem Member, measure_empty, ENNReal.toReal_zero,
      mul_zero, if_neg Member, zero_div]

/-- Conditioning a finite-support probability law on a positive upper event increases it in law. -/
theorem StochasticDominatedFiniteUpperCondition {α : Type*} [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset α)
    (Support : ∀ᵐ i ∂μ, i ∈ S) (A : Set α) (Upper : IsUpperSet A)
    (Positive : μ A ≠ 0) : StochasticDominated μ (cond μ A) := by
  classical
  have ConditionalProbability : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure Positive
  have ConditionalSupport : ∀ᵐ i ∂cond μ A, i ∈ S := cond_absolutelyContinuous.ae_le Support
  apply StochasticDominatedOfFiniteLikelihoodRatio μ (cond μ A) S Support ConditionalSupport
  intro i _ j _ Ordered
  rw [ConditionalSingletonReal, ConditionalSingletonReal]
  by_cases Member : i ∈ A
  · have LargerMember : j ∈ A := Upper Ordered Member
    rw [if_pos Member, if_pos LargerMember]
    exact le_of_eq (by ring)
  · rw [if_neg Member, zero_div, zero_mul]
    apply mul_nonneg measureReal_nonneg
    apply div_nonneg
    · split_ifs
      · exact measureReal_nonneg
      · exact le_rfl
    · exact measureReal_nonneg

/-- Adding a fixed natural number preserves stochastic domination of natural-valued measures. -/
theorem StochasticDominatedNatAdd (μ ν : Measure ℕ) (Dominated : StochasticDominated μ ν)
    (x : ℕ) : StochasticDominated (μ.map (fun j => j + x)) (ν.map (fun j => j + x)) := by
  intro a
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
    Measure.map_apply (measurable_of_countable _) measurableSet_Iic]
  by_cases Above : x ≤ a
  · have Fiber : (fun j : ℕ => j + x) ⁻¹' Iic a = Iic (a - x) := by
      ext j
      simp only [mem_preimage, mem_Iic]
      omega
    rw [Fiber]
    exact Dominated (a - x)
  · have Fiber : (fun j : ℕ => j + x) ⁻¹' Iic a = ∅ := by
      ext j
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      omega
    rw [Fiber, measure_empty, measure_empty]

/-- Measurable pushforward commutes with conditioning on a measurable range event. -/
theorem ConditionalMap {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (X : Ω → α) (MeasurableX : Measurable X)
    (A : Set α) (MeasurableA : MeasurableSet A) :
    (cond P (X ⁻¹' A)).map X = cond (P.map X) A := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, ← Measure.restrict_map MeasurableX MeasurableA,
    Measure.map_apply MeasurableX MeasurableA]

end
end ECTheoryLib.Probability
