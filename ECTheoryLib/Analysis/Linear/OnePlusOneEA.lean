import ECTheoryLib.Analysis.Linear.MutationVariance
import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Problems.Comparison

/-!
# Variance tail of the actual EA maximizing a signed linear objective

Use the existing standard mutation and weak elitist comparison, accepting
ties. Candidate upper tails transfer only strictly above the parent score.
-/

namespace ECTheoryLib.Analysis.EALinear
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Analysis.LinearMutation
open scoped unitInterval
noncomputable section

/-- The existing standard EA kernel maximizing the actual linear score. -/
def Step {n : ℕ} (PositiveLength : 0<n) (Weights : Fin n → ℝ) : Transition (Bits n) :=
  OnePlusOneEAStep PositiveLength (Problems.MaxNotWorse (Score Weights))

theorem StepScoreFiniteVarianceUpper {n : ℕ} (PositiveLength : 0<n)
    (Weights : Fin n → ℝ) (Parent : Bits n) (b : ℝ) (PositiveScale : 0<b)
    (WeightBound : ∀ i, |Weights i|≤b) (d : ℝ) (Nonnegative : 0≤d)
    (AboveParent : Score Weights Parent<(∑ i, Weights i)/(n : ℝ)+(1-2/(n : ℝ))*Score Weights Parent+d) :
    (Step PositiveLength Weights Parent).toMeasure.real
      {y | (∑ i, Weights i)/(n : ℝ)+(1-2/(n : ℝ))*Score Weights Parent+d≤Score Weights y}≤
      ScaledVarianceFiniteUpperBound n b ((1/(n : ℝ))*(1-1/(n : ℝ))*(∑ i, (Weights i)^2)) d := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ),⟨by positivity,(div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ)=(n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ))=(n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN,ENNReal.ofReal_one,ENNReal.ofReal_natCast,one_div]
  have Proposal := ScoreFiniteVarianceUpper p Weights Parent b PositiveScale WeightBound d Nonnegative
  have MeanRatio : (p : ℝ)*(∑ i, Weights i)=(∑ i, Weights i)/(n : ℝ) := by dsimp [p]; ring
  have Coefficient : 2*(p : ℝ)=2/(n : ℝ) := by dsimp [p]; ring
  simp only [Rate,MeanRatio,Coefficient] at Proposal
  change (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | (∑ i, Weights i)/(n : ℝ)+(1-2/(n : ℝ))*Score Weights Parent+d≤Score Weights y}≤
      ScaledVarianceFiniteUpperBound n b ((1/(n : ℝ))*(1-1/(n : ℝ))*(∑ i, (Weights i)^2)) d at Proposal
  unfold Step OnePlusOneEAStep
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) ((Set.to_countable _).measurableSet)]
  apply le_trans _ Proposal
  apply measureReal_mono _ (measure_ne_top _ _)
  intro Candidate Member
  change (∑ i, Weights i)/(n : ℝ)+(1-2/(n : ℝ))*Score Weights Parent+d≤
    Score Weights (ElitistSelect (Problems.MaxNotWorse (Score Weights)) Parent Candidate) at Member
  unfold ElitistSelect at Member
  split_ifs at Member
  · exact Member
  · exact False.elim (not_le_of_gt AboveParent Member)

end
end ECTheoryLib.Analysis.EALinear
