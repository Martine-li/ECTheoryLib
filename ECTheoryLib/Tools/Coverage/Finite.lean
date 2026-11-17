import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Weighted deficits for finite current-coverage tasks

Positive weights turn missing targets into a nonnegative potential, zero exactly
at complete coverage. If observed values are retained, the potential cannot
increase; adding a previously missing target decreases it by at least that target's
weight. These are deterministic rules, independent of objectives and algorithms.
-/
namespace ECTheoryLib.Tools.Coverage
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Total weight of targets absent from the current observed set. -/
def MissingWeight (Targets Observed : Finset α) (Weight : α → ℝ) : ℝ :=
  ∑ a ∈ Targets, if a ∈ Observed then 0 else Weight a

/-- Nonnegative target weights give a nonnegative coverage potential. -/
theorem MissingWeightNonnegative (Targets Observed : Finset α) (Weight : α → ℝ)
    (Nonnegative : ∀ a ∈ Targets, 0 ≤ Weight a) :
    0 ≤ MissingWeight Targets Observed Weight := by
  apply Finset.sum_nonneg
  intro a InTargets
  by_cases Present : a ∈ Observed
  · simp only [if_pos Present, le_refl]
  · simp only [if_neg Present]
    exact Nonnegative a InTargets

/-- Positive weights make zero potential equivalent to simultaneous full coverage. -/
theorem MissingWeightEqZeroIff (Targets Observed : Finset α) (Weight : α → ℝ)
    (Positive : ∀ a ∈ Targets, 0 < Weight a) :
    MissingWeight Targets Observed Weight = 0 ↔ Targets ⊆ Observed := by
  have TermsNonnegative : ∀ a ∈ Targets, 0 ≤ (if a ∈ Observed then 0 else Weight a) := by
    intro a InTargets
    split_ifs with Present
    · exact le_rfl
    · exact (Positive a InTargets).le
  rw [MissingWeight, Finset.sum_eq_zero_iff_of_nonneg TermsNonnegative]
  constructor
  · intro TermsZero a InTargets
    by_contra Missing
    have ZeroTerm := TermsZero a InTargets
    rw [if_neg Missing] at ZeroTerm
    exact (ne_of_gt (Positive a InTargets)) ZeroTerm
  · intro Covered a InTargets
    exact if_pos (Covered InTargets)

/-- Retaining observed values cannot increase the missing-target potential. -/
theorem MissingWeightAntitone (Targets Old New : Finset α) (Weight : α → ℝ)
    (Nonnegative : ∀ a ∈ Targets, 0 ≤ Weight a) (Retained : Old ⊆ New) :
    MissingWeight Targets New Weight ≤ MissingWeight Targets Old Weight := by
  apply Finset.sum_le_sum
  intro a InTargets
  by_cases WasPresent : a ∈ Old
  · rw [if_pos WasPresent, if_pos (Retained WasPresent)]
  · rw [if_neg WasPresent]
    by_cases NowPresent : a ∈ New
    · rw [if_pos NowPresent]
      exact Nonnegative a InTargets
    · rw [if_neg NowPresent]

/-- Adding a previously missing target decreases potential by at least its weight,
provided all previously observed values are retained. -/
theorem MissingWeightDecrease (Targets Old New : Finset α) (Weight : α → ℝ)
    (Nonnegative : ∀ a ∈ Targets, 0 ≤ Weight a) (Retained : Old ⊆ New)
    (a : α) (Target : a ∈ Targets) (Missing : a ∉ Old) (Added : a ∈ New) :
    Weight a ≤ MissingWeight Targets Old Weight - MissingWeight Targets New Weight := by
  unfold MissingWeight
  rw [← Finset.sum_sub_distrib]
  have NonnegativeDecrease : ∀ b ∈ Targets,
      0 ≤ (if b ∈ Old then 0 else Weight b) - (if b ∈ New then 0 else Weight b) := by
    intro b InTargets
    by_cases WasPresent : b ∈ Old
    · rw [if_pos WasPresent, if_pos (Retained WasPresent), sub_self]
    · rw [if_neg WasPresent]
      by_cases NowPresent : b ∈ New
      · rw [if_pos NowPresent, sub_zero]
        exact Nonnegative b InTargets
      · rw [if_neg NowPresent, sub_self]
  have AtTarget := Finset.single_le_sum NonnegativeDecrease Target
  rw [if_neg Missing, if_pos Added, sub_zero] at AtTarget
  exact AtTarget

/-- The total target weight uniformly bounds every coverage deficit. -/
theorem MissingWeightLeTotal (Targets Observed : Finset α) (Weight : α → ℝ)
    (Nonnegative : ∀ a ∈ Targets, 0 ≤ Weight a) :
    MissingWeight Targets Observed Weight ≤ ∑ a ∈ Targets, Weight a := by
  apply Finset.sum_le_sum
  intro a InTargets
  split_ifs with Present
  · exact Nonnegative a InTargets
  · exact le_rfl

end
end ECTheoryLib.Tools.Coverage
