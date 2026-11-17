import ECTheoryLib.Analysis.OneMax.MutationDomination
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift

/-!
# Stochastic one-step progress of the actual (1+1) EA on OneMax

The mutation result concerns offspring before selection. This module separately
identifies the actual elitist update score as the maximum of parent and offspring
scores, then proves the selected-score order and its strict upper tails.
The stated standard-rate application requires n >= 2.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Analysis.OneMaxMutation
noncomputable section

private theorem MaxLawDomination (μ ν : Measure ℕ) (a b : ℕ)
    (Counts : a ≤ b) (Ordered : StochasticDominated μ ν) :
    StochasticDominated (μ.map (max a)) (ν.map (max b)) := by
  intro c
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
    Measure.map_apply (measurable_of_countable _) measurableSet_Iic]
  have Preimage (d : ℕ) (Below : d ≤ c) : (max d) ⁻¹' Iic c = Iic c := by
    ext x
    change max d x ≤ c ↔ x ≤ c
    simp only [max_le_iff, Below, true_and]
  by_cases Below : b ≤ c
  · rw [Preimage b Below, Preimage a (le_trans Counts Below)]
    exact Ordered c
  · have Empty : (max b) ⁻¹' Iic c = ∅ := by
      ext x
      change max b x ≤ c ↔ False
      simp only [max_le_iff, Below, false_and]
    rw [Empty, measure_empty]
    exact zero_le

/-- The accepted one-count is the maximum of the parent and candidate counts. -/
theorem UpdateOneMax {n : ℕ} (Parent Candidate : Bits n) :
    OneMax (Update Parent Candidate) = max (OneMax Parent) (OneMax Candidate) := by
  unfold Update ElitistSelect Problems.MaxNotWorse
  by_cases Accepted : OneMax Parent ≤ OneMax Candidate
  · rw [if_pos Accepted, max_eq_right Accepted]
  · rw [if_neg Accepted, max_eq_left (le_of_not_ge Accepted)]

/-- The actual selected-score law is the mutation-score law capped below by the parent score. -/
theorem StepOneMaxLaw {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n) :
    (Step PositiveLength Parent).toMeasure.map OneMax =
      ((StandardBitMutation PositiveLength Parent).toMeasure.map OneMax).map (max (OneMax Parent)) := by
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_map (measurable_of_countable _) (measurable_of_finite _)]
  congr 1
  funext Candidate
  exact UpdateOneMax Parent Candidate

/-- Actual (1+1) EA one-step score distributions preserve the parent-score order. -/
theorem StepOneMaxStochasticMonotone {n : ℕ} (PositiveLength : 0 < n)
    (AtLeastTwo : 2 ≤ n) (Parent Other : Bits n) (Counts : OneMax Parent ≤ OneMax Other) :
    StochasticDominated ((Step PositiveLength Parent).toMeasure.map OneMax)
      ((Step PositiveLength Other).toMeasure.map OneMax) := by
  rw [StepOneMaxLaw, StepOneMaxLaw]
  apply MaxLawDomination _ _ _ _ Counts
  exact StandardMutationOneMaxStochasticMonotone PositiveLength AtLeastTwo Parent Other Counts

/-- The distribution comparison yields every strict upper-tail comparison after selection. -/
theorem StepOneMaxStrictTailMonotone {n : ℕ} (PositiveLength : 0 < n)
    (AtLeastTwo : 2 ≤ n) (Parent Other : Bits n) (Counts : OneMax Parent ≤ OneMax Other) (k : ℕ) :
    (Step PositiveLength Parent).toMeasure {Next | k < OneMax Next} ≤
      (Step PositiveLength Other).toMeasure {Next | k < OneMax Next} := by
  have Ordered := StepOneMaxStochasticMonotone PositiveLength AtLeastTwo Parent Other Counts
  have ParentProbability : IsProbabilityMeasure ((Step PositiveLength Parent).toMeasure.map OneMax) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  have OtherProbability : IsProbabilityMeasure ((Step PositiveLength Other).toMeasure.map OneMax) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  have Bound := (StochasticDominatedIffStrictTail _ _).mp Ordered k
  rw [Measure.map_apply (measurable_of_finite _) measurableSet_Ioi,
    Measure.map_apply (measurable_of_finite _) measurableSet_Ioi] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.EAOneMax
