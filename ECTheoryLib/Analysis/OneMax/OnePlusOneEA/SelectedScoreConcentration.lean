import ECTheoryLib.Probability.Concentration.BoundedDifferences
import ECTheoryLib.Analysis.OneMax.OnePlusOneEA.AcceptanceExpectation
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic

/-!
# Concentration of the actual selected OneMax EA score

The standard (1+1) EA proposes independent bit mutations at rate1/n, then
performs the existing elitist selection. Apply bounded differences to the
nonadditive selected score as a function of proposal coordinates. Transfer
the whole score law and its actual mean to Step using existing interfaces.
The centered MGF parameter is n/4; both closed tails have exponent -2*d^2/n.
Only n>0 is required, including the deterministic n=1 mutation endpoint.
These are one-step score bounds, not runtime improvement claims.
-/


namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval NNReal
noncomputable section

/-- The selected score has width one per independent proposal coordinate. -/
theorem StepScoreBoundedDifferencesSubGaussian {n : ℕ}
    (PositiveLength : 0 < n) (Parent : Bits n) :
    HasSubgaussianMGF
      (fun Next => (OneMax Next : ℝ) -
        ∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure)
      ((n : ℝ≥0) / 4) (Step PositiveLength Parent).toMeasure := by
  classical
  let P := (StandardBitMutation PositiveLength Parent).toMeasure
  let f : Bits n → ℝ := fun Candidate => (OneMax (Update Parent Candidate) : ℝ)
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1 / (n : ℝ), ⟨by positivity,
    (div_le_one PositiveReal).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  have ProductLaw := IndependentBitMutationProductLaw p Parent
  simp only [Rate] at ProductLaw
  have Independent : iIndepFun (fun i (Candidate : Bits n) => Candidate i) P := by
    change iIndepFun _ (StandardBitMutation PositiveLength Parent).toMeasure
    unfold StandardBitMutation
    rw [← ProductLaw]
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have Coordinate : ∀ i (x y : Bits n), (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ ((1 : ℝ≥0) : ℝ) := by
    intro i x y Same
    have Distance : Problems.TargetOneMax.Hamming x y ≤ 1 := by
      calc
        Problems.TargetOneMax.Hamming x y = (if y i = x i then 0 else 1) := by
          unfold Problems.TargetOneMax.Hamming
          apply Finset.sum_eq_single i
          · intro j _Member Different
            simp [Same j Different]
          · simp
        _ ≤ 1 := by split_ifs <;> omega
    have Count := Problems.TargetOneMax.ZeroCountDifferenceLeHamming x y
    rw [Problems.OneMax.ZeroCountAsRealDifference,
      Problems.OneMax.ZeroCountAsRealDifference] at Count
    have Score : |(OneMax x : ℝ) - (OneMax y : ℝ)| ≤ 1 := by
      calc
        _ = |((n : ℝ) - (OneMax y : ℝ)) - ((n : ℝ) - (OneMax x : ℝ))| := by
          congr 1
          ring
        _ ≤ (Problems.TargetOneMax.Hamming x y : ℝ) := Count
        _ ≤ 1 := by exact_mod_cast Distance
    simpa only [f, UpdateOneMax, Nat.cast_max, max_comm, NNReal.coe_one] using
      (abs_max_sub_max_le_abs (OneMax x : ℝ) (OneMax y : ℝ) (OneMax Parent : ℝ)).trans Score
  have Proposal := IndependentBoundedDifferencesSubGaussian P
    (fun i (Candidate : Bits n) => Candidate i)
    (fun _ => (measurable_of_finite _).aemeasurable) Independent f (fun _ => 1)
    (measurable_of_finite _) Coordinate
  have ScoreLaw : IdentDistrib (fun Candidate => OneMax (Update Parent Candidate))
      OneMax P (Step PositiveLength Parent).toMeasure := by
    refine ⟨(measurable_of_finite _).aemeasurable,
      (measurable_of_finite _).aemeasurable, ?_⟩
    rw [StepOneMaxLaw, Measure.map_map (measurable_of_countable _) (measurable_of_finite _)]
    congr 1
    funext Candidate
    exact UpdateOneMax Parent Candidate
  have RealLaw : IdentDistrib f (fun Next => (OneMax Next : ℝ))
      P (Step PositiveLength Parent).toMeasure :=
    ScoreLaw.comp (measurable_of_countable (fun k : ℕ => (k : ℝ)))
  have CenteredLaw := RealLaw.comp (measurable_id.sub_const (∫ Candidate, f Candidate ∂P))
  have Bound := Proposal.congr_identDistrib CenteredLaw
  rw [StepScoreIntegral]
  simpa only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Function.comp_def, id_eq, f, P] using Bound

/-- A closed upper tail around the actual selected-score expectation. -/
theorem StepScoreBoundedDifferencesUpperTail {n : ℕ}
    (PositiveLength : 0 < n) (Parent : Bits n) (threshold : ℝ)
    (Nonnegative : 0 ≤ threshold) :
    (Step PositiveLength Parent).toMeasure.real
      {Next | (∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure) +
        threshold ≤ (OneMax Next : ℝ)} ≤ Real.exp (-2 * threshold ^ 2 / n) := by
  have Bound := (StepScoreBoundedDifferencesSubGaussian PositiveLength Parent).measure_ge_le Nonnegative
  have Event : {Next : Bits n | threshold ≤ (OneMax Next : ℝ) -
      ∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure} =
      {Next | (∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure) +
        threshold ≤ (OneMax Next : ℝ)} := by
    ext Next
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  rw [Event] at Bound
  have Exponent : -threshold ^ 2 / (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ)) =
      -2 * threshold ^ 2 / n := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    rw [show (2 : ℝ) * ((n : ℝ) / 4) = (n : ℝ) / 2 by ring, div_div_eq_mul_div]
    ring
  rwa [Exponent] at Bound

/-- A closed lower tail for the same actual selected score and expectation. -/
theorem StepScoreBoundedDifferencesLowerTail {n : ℕ}
    (PositiveLength : 0 < n) (Parent : Bits n) (threshold : ℝ)
    (Nonnegative : 0 ≤ threshold) :
    (Step PositiveLength Parent).toMeasure.real
      {Next | (OneMax Next : ℝ) ≤
        (∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure) - threshold} ≤
      Real.exp (-2 * threshold ^ 2 / n) := by
  have Bound := (StepScoreBoundedDifferencesSubGaussian PositiveLength Parent).neg.measure_ge_le Nonnegative
  have Event : {Next : Bits n | threshold ≤ -((OneMax Next : ℝ) -
      ∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure)} =
      {Next | (OneMax Next : ℝ) ≤
        (∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure) - threshold} := by
    ext Next
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro H <;> linarith
  change (Step PositiveLength Parent).toMeasure.real
    {Next | threshold ≤ -((OneMax Next : ℝ) -
      ∫ State, (OneMax State : ℝ) ∂(Step PositiveLength Parent).toMeasure)} ≤ _ at Bound
  rw [Event] at Bound
  have Exponent : -threshold ^ 2 / (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ)) =
      -2 * threshold ^ 2 / n := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    rw [show (2 : ℝ) * ((n : ℝ) / 4) = (n : ℝ) / 2 by ring, div_div_eq_mul_div]
    ring
  rwa [Exponent] at Bound

end
end ECTheoryLib.Analysis.EAOneMax

