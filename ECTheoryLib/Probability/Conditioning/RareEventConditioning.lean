import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditioning away a small-probability event

Book Lemma 1.7.2, with the positive-event convention from section 1.7.
The event probability is 1-p with p<1. For p<=1/2, both book additive
bounds are available, including a variant using only an upper bound on the
excluded mass. No independence is asserted under the conditional measure.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

private theorem ConditionalRealFormula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A C : Set Ω) (Event : MeasurableSet A) :
    (P[|C]).real A = P.real (A ∩ C) / P.real C := by
  unfold Measure.real
  rw [cond_apply' Event, ENNReal.toReal_mul, ENNReal.toReal_inv, Set.inter_comm]
  rw [div_eq_mul_inv, mul_comm]

/-- Book 1.7.2: two ratio bounds, with the section's positive-conditioning convention. -/
theorem ConditionalEventBounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A C : Set Ω)
    (Event : MeasurableSet A) (Condition : MeasurableSet C)
    (p : ℝ) (ConditionMass : P.real C = 1 - p) (FailureLessOne : p < 1) :
    (P.real A - p) / (1-p) ≤ (P[|C]).real A ∧
      (P[|C]).real A ≤ P.real A / (1-p) := by
  have PositiveDenominator : 0 < 1-p := sub_pos.mpr FailureLessOne
  have ComplementMass : P.real Cᶜ = p := by
    rw [measureReal_compl Condition, probReal_univ, ConditionMass]
    ring
  have ExcludedBound : P.real (A \ C) ≤ p := by
    rw [← ComplementMass]
    exact measureReal_mono (fun _ Member => Member.2)
  have Decomposition : P.real (A ∩ C) + P.real (A \ C) = P.real A :=
    measureReal_inter_add_sdiff Condition
  have IntersectionLower : P.real A - p ≤ P.real (A ∩ C) := by linarith
  have IntersectionUpper : P.real (A ∩ C) ≤ P.real A := measureReal_mono inter_subset_left
  rw [ConditionalRealFormula P A C Event, ConditionMass]
  constructor
  · exact div_le_div_of_nonneg_right IntersectionLower PositiveDenominator.le
  · exact div_le_div_of_nonneg_right IntersectionUpper PositiveDenominator.le

/-- Book 1.7.2 additive form for conditioning away an event of probability at most one half. -/
theorem ConditionalEventAdditiveBounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A C : Set Ω)
    (Event : MeasurableSet A) (Condition : MeasurableSet C)
    (p : ℝ) (ConditionMass : P.real C = 1-p) (FailureHalf : p ≤ 1/2) :
    P.real A - p ≤ (P[|C]).real A ∧ (P[|C]).real A ≤ P.real A + 2*p := by
  have FailureLessOne : p < 1 := by linarith
  have PositiveDenominator : 0 < 1-p := sub_pos.mpr FailureLessOne
  have EventBound : P.real A ≤ 1 := measureReal_le_one
  have ConditionBound : P.real C ≤ 1 := measureReal_le_one
  have NonnegativeFailure : 0 ≤ p := by rw [ConditionMass] at ConditionBound; linarith
  obtain ⟨Lower, Upper⟩ := ConditionalEventBounds P A C Event Condition p ConditionMass FailureLessOne
  constructor
  · by_cases NonnegativeNumerator : 0 ≤ P.real A-p
    · have RatioLower : P.real A-p ≤ (P.real A-p)/(1-p) := by
        apply (le_div_iff₀ PositiveDenominator).mpr
        nlinarith [mul_nonneg NonnegativeNumerator NonnegativeFailure]
      exact le_trans RatioLower Lower
    · exact le_trans (le_of_not_ge NonnegativeNumerator) measureReal_nonneg
  · have RatioUpper : P.real A/(1-p) ≤ P.real A+2*p := by
      apply (div_le_iff₀ PositiveDenominator).mpr
      have ProductBound : p * P.real A ≤ p := mul_le_of_le_one_right NonnegativeFailure EventBound
      nlinarith [mul_nonneg NonnegativeFailure (sub_nonneg.mpr FailureHalf)]
    exact le_trans Upper RatioUpper

/-- A usable additive version needs only an upper bound on the excluded probability. -/
theorem ConditionalEventAdditiveOfComplementBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A C : Set Ω)
    (Event : MeasurableSet A) (Condition : MeasurableSet C)
    (p : ℝ) (ExcludedBound : P.real Cᶜ ≤ p) (FailureHalf : p ≤ 1/2) :
    P.real A - p ≤ (P[|C]).real A ∧ (P[|C]).real A ≤ P.real A + 2*p := by
  have ConditionMass : P.real C = 1 - P.real Cᶜ := by
    rw [measureReal_compl Condition, probReal_univ]
    ring
  obtain ⟨Lower, Upper⟩ := ConditionalEventAdditiveBounds P A C Event Condition
    (P.real Cᶜ) ConditionMass (le_trans ExcludedBound FailureHalf)
  constructor
  · linarith
  · linarith

end
end ECTheoryLib.Probability

