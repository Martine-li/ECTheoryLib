import ECTheoryLib.Analysis.OneMax.MutationVariance
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.Drift

/-!
# Selected EA score tail from actual mutation variance

A score threshold strictly above the retained parent allows transfer of
the candidate upper tail to the existing standard(1+1)EA. Equality is not
allowed; Tests/Bennett contains an actual optimum-parent counterexample.
-/

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Analysis.OneMaxMutation
open scoped unitInterval
noncomputable section

/-- The actual selected EA score inherits the candidate upper tail when
the threshold lies strictly above the retained parent's score. -/
theorem StepScoreBernsteinUpper {n : ℕ} (PositiveLength : 0<n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d)
    (AboveParent : (OneMax Parent : ℝ)<1+(1-2/(n : ℝ))*(OneMax Parent : ℝ)+d) :
    (Step PositiveLength Parent).toMeasure.real
      {y | 1+(1-2/(n : ℝ))*(OneMax Parent : ℝ)+d≤(OneMax y : ℝ)}≤
      Real.exp (-d^2/(2*(1-1/(n : ℝ))+2*d/3)) := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ),⟨by positivity,(div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ)=(n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ))=(n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN,ENNReal.ofReal_one,ENNReal.ofReal_natCast,one_div]
  have Unit : (n : ℝ)*(p : ℝ)=1 := mul_one_div_cancel PositiveN.ne'
  have Proposal := MutationOneMaxBernsteinUpper p Parent d Nonnegative
  rw [Unit,one_mul] at Proposal
  have Coefficient : 2*(p : ℝ)=2/(n : ℝ) := by dsimp [p]; ring
  simp only [Rate,Coefficient] at Proposal
  change (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | 1+(1-2/(n : ℝ))*(OneMax Parent : ℝ)+d≤(OneMax y : ℝ)}≤
      Real.exp (-d^2/(2*(1-1/(n : ℝ))+2*d/3)) at Proposal
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  apply le_trans _ Proposal
  apply measureReal_mono _ (measure_ne_top _ _)
  intro Candidate Member
  change 1+(1-2/(n : ℝ))*(OneMax Parent : ℝ)+d≤
    (OneMax (Update Parent Candidate) : ℝ) at Member
  unfold Update ElitistSelect at Member
  split_ifs at Member
  · exact Member
  · exact False.elim (not_le_of_gt AboveParent Member)

end
end ECTheoryLib.Analysis.EAOneMax
