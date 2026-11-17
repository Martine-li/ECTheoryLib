import ECTheoryLib.Probability.Conditioning.FiniteConditioning
import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.StochasticProgress

/-!
# One-step EA expectation split by acceptance

Apply the general partition theorem to the actual mutation proposal law.
Acceptance contributes the conditional candidate score; rejection contributes
the retained parent score. Zero-probability branches and n=1 are included.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
noncomputable section

/-- Acceptance refers to the proposed offspring, before the actual elitist selection. -/
def AcceptanceEvent {n : ℕ} (Parent : Bits n) : Set (Bits n) :=
  {Candidate | OneMax Parent ≤ OneMax Candidate}

/-- The actual selected score, averaged over the mutation proposal law. -/
theorem StepScoreIntegral {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n) :
    (∫ Next, (OneMax Next : ℝ) ∂(Step PositiveLength Parent).toMeasure) =
      ∫ Candidate, (OneMax (Update Parent Candidate) : ℝ) ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  exact PMFIntegralMap (StandardBitMutation PositiveLength Parent) (Update Parent)
    (fun Next => (OneMax Next : ℝ))

/-- A complete one-step expectation decomposition by the actual acceptance event. -/
theorem StepScoreExpectationByAcceptance {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n) :
    (∫ Next, (OneMax Next : ℝ) ∂(Step PositiveLength Parent).toMeasure) =
      (StandardBitMutation PositiveLength Parent).toMeasure.real (AcceptanceEvent Parent) *
        (∫ Candidate, (OneMax Candidate : ℝ)
          ∂(StandardBitMutation PositiveLength Parent).toMeasure[|AcceptanceEvent Parent]) +
      (StandardBitMutation PositiveLength Parent).toMeasure.real (AcceptanceEvent Parent)ᶜ * (OneMax Parent : ℝ) := by
  classical
  let P := (StandardBitMutation PositiveLength Parent).toMeasure
  let C : Bool → Set (Bits n) := fun b => if b then AcceptanceEvent Parent else (AcceptanceEvent Parent)ᶜ
  have Cells : ∀ b, MeasurableSet (C b) := fun _ => (Set.to_countable _).measurableSet
  have DisjointCells : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j Different
    cases i
    · cases j
      · exact False.elim (Different rfl)
      · exact disjoint_compl_left
    · cases j
      · exact disjoint_compl_right
      · exact False.elim (Different rfl)
  have Cover : ∀ x, ∃ b, x ∈ C b := by
    intro Candidate
    by_cases Accepted : Candidate ∈ AcceptanceEvent Parent
    · exact ⟨true, Accepted⟩
    · exact ⟨false, Accepted⟩
  have FiniteMean : Integrable (fun Candidate => (OneMax (Update Parent Candidate) : ℝ)) P :=
    Integrable.of_finite
  have Decomposition := FinitePartitionTotalExpectation P C Cells DisjointCells Cover _ FiniteMean
  simp only [Fintype.sum_bool, C, Bool.false_eq_true, if_false, if_true] at Decomposition
  have AcceptedIntegral :
      (∫ Candidate, (OneMax (Update Parent Candidate) : ℝ) ∂P[|AcceptanceEvent Parent]) =
      ∫ Candidate, (OneMax Candidate : ℝ) ∂P[|AcceptanceEvent Parent] := by
    apply integral_congr_ae
    filter_upwards [ae_cond_mem (μ := P) (Set.to_countable (AcceptanceEvent Parent)).measurableSet] with Candidate Accepted
    change OneMax Parent ≤ OneMax Candidate at Accepted
    rw [UpdateOneMax, max_eq_right Accepted]
  have RejectedIntegral :
      (∫ Candidate, (OneMax (Update Parent Candidate) : ℝ) ∂P[|(AcceptanceEvent Parent)ᶜ]) =
      ∫ _Candidate, (OneMax Parent : ℝ) ∂P[|(AcceptanceEvent Parent)ᶜ] := by
    apply integral_congr_ae
    filter_upwards [ae_cond_mem (μ := P) (Set.to_countable (AcceptanceEvent Parent)ᶜ).measurableSet] with Candidate Rejected
    change ¬OneMax Parent ≤ OneMax Candidate at Rejected
    rw [UpdateOneMax, max_eq_left (le_of_not_ge Rejected)]
  rw [AcceptedIntegral, RejectedIntegral] at Decomposition
  rw [StepScoreIntegral]
  change (∫ Candidate, (OneMax (Update Parent Candidate) : ℝ) ∂P) = _
  rw [Decomposition]
  congr 1
  by_cases ZeroRejection : P (AcceptanceEvent Parent)ᶜ = 0
  · have ZeroReal : P.real (AcceptanceEvent Parent)ᶜ = 0 := by
      change (P (AcceptanceEvent Parent)ᶜ).toReal = 0
      rw [ZeroRejection, ENNReal.toReal_zero]
    rw [ZeroReal, zero_mul, zero_mul]
  · have ConditionalProbability : IsProbabilityMeasure P[|(AcceptanceEvent Parent)ᶜ] :=
      cond_isProbabilityMeasure ZeroRejection
    rw [integral_const, probReal_univ, one_smul]

end
end ECTheoryLib.Analysis.EAOneMax
