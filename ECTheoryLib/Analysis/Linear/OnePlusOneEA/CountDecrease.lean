import ECTheoryLib.Analysis.Linear.MutationVariance
import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Problems.Comparison

/-! Parent-one removals under the actual independent mutation law.
Exact moments reuse signed linear-score moments with the parent mask. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open ECTheoryLib.Analysis.LinearMutation ECTheoryLib.Analysis.OneMaxMutation
open scoped unitInterval
noncomputable section

def ParentMask {n : ℕ} (Parent : Bits n) : Fin n → ℝ :=
  fun i => if Parent i then 1 else 0

def FlippedOnes {n : ℕ} (Parent Candidate : Bits n) : ℕ :=
  ∑ i : Fin n, if Parent i then (if Candidate i then 0 else 1) else 0

theorem ParentMaskSum {n : ℕ} (Parent : Bits n) :
    (∑ i, ParentMask Parent i) = (OneMax Parent : ℝ) := by
  simp [ParentMask, OneMax]

theorem ParentMaskSquareSum {n : ℕ} (Parent : Bits n) :
    (∑ i, (ParentMask Parent i)^2) = (OneMax Parent : ℝ) := by
  rw [← ParentMaskSum]
  apply Finset.sum_congr rfl
  intro i _
  cases Parent i <;> norm_num [ParentMask]

theorem ParentMaskScore {n : ℕ} (Parent : Bits n) :
    Score (ParentMask Parent) Parent = (OneMax Parent : ℝ) := by
  rw [← ParentMaskSum]
  unfold Score
  apply Finset.sum_congr rfl
  intro i _
  cases h : Parent i <;> norm_num [ParentMask, h]

theorem FlippedOnesReal {n : ℕ} (Parent Candidate : Bits n) :
    (FlippedOnes Parent Candidate : ℝ) = (OneMax Parent : ℝ)-Score (ParentMask Parent) Candidate := by
  unfold FlippedOnes OneMax Score ParentMask
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases Parent i <;> cases Candidate i <;> norm_num

theorem FlippedOnesLeCount {n : ℕ} (Parent Candidate : Bits n) :
    FlippedOnes Parent Candidate ≤ OneMax Parent := by
  unfold FlippedOnes OneMax
  apply Finset.sum_le_sum
  intro i _
  cases Parent i <;> cases Candidate i <;> norm_num

theorem ParentMaskScoreLeCount {n : ℕ} (Parent Candidate : Bits n) :
    Score (ParentMask Parent) Candidate ≤ (OneMax Candidate : ℝ) := by
  unfold Score ParentMask OneMax
  push_cast
  apply Finset.sum_le_sum
  intro i _
  cases Parent i <;> cases Candidate i <;> norm_num

/-- Net positive one-count decrease never exceeds removed parent-one bits. -/
theorem CountPositiveDecreaseLeFlippedOnes {n : ℕ} (Parent Candidate : Bits n) :
    max ((OneMax Parent : ℝ)-(OneMax Candidate : ℝ)) 0 ≤ (FlippedOnes Parent Candidate : ℝ) := by
  apply max_le
  · rw [FlippedOnesReal]
    linarith [ParentMaskScoreLeCount Parent Candidate]
  · exact Nat.cast_nonneg _

/-- Selection either retains the parent or accepts this actual candidate;
no objective-specific monotonicity of one-count is assumed. -/
theorem SelectedCountPositiveDecreaseLeFlippedOnes {n : ℕ}
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse] (Parent Candidate : Bits n) :
    max ((OneMax Parent : ℝ)-(OneMax (ElitistSelect NotWorse Parent Candidate) : ℝ)) 0 ≤
      (FlippedOnes Parent Candidate : ℝ) := by
  unfold ElitistSelect
  split_ifs
  · exact CountPositiveDecreaseLeFlippedOnes Parent Candidate
  · simpa only [sub_self, max_self] using (Nat.cast_nonneg (FlippedOnes Parent Candidate) :
      (0 : ℝ) ≤ (FlippedOnes Parent Candidate : ℝ))

theorem FlippedOnesExpectation {n : ℕ} (p : I) (Parent : Bits n) :
    (∫ Candidate, (FlippedOnes Parent Candidate : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
        (p : ℝ)*(OneMax Parent : ℝ) := by
  simp_rw [FlippedOnesReal]
  rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const,
    probReal_univ, one_smul, ScoreExpectation, ParentMaskSum, ParentMaskScore]
  ring

theorem FlippedOnesVariance {n : ℕ} (p : I) (Parent : Bits n) :
    variance (fun Candidate => (FlippedOnes Parent Candidate : ℝ))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure =
        (p : ℝ)*(1-(p : ℝ))*(OneMax Parent : ℝ) := by
  simp_rw [FlippedOnesReal]
  rw [variance_const_sub (measurable_of_finite _).aestronglyMeasurable,
    ScoreVariance, ParentMaskSquareSum]

/-- The second factorial moment is exact, including zero/one parent count. -/
theorem FlippedOnesFactorialMoment {n : ℕ} (p : I) (Parent : Bits n) :
    (∫ Candidate, (FlippedOnes Parent Candidate : ℝ)*((FlippedOnes Parent Candidate : ℝ)-1)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
        (p : ℝ)^2*(OneMax Parent : ℝ)*((OneMax Parent : ℝ)-1) := by
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let Z : Bits n → ℝ := fun Candidate => FlippedOnes Parent Candidate
  have SquareIntegrable : MemLp Z 2 μ := by
    apply memLp_of_bounded (a := (0 : ℝ)) (b := (OneMax Parent : ℝ)) _
      (measurable_of_finite _).aestronglyMeasurable
    exact ae_of_all μ (fun Candidate => ⟨Nat.cast_nonneg _, by
      change (FlippedOnes Parent Candidate : ℝ) ≤ (OneMax Parent : ℝ)
      exact_mod_cast FlippedOnesLeCount Parent Candidate⟩)
  have Raw := variance_eq_sub SquareIntegrable
  change variance (fun Candidate => (FlippedOnes Parent Candidate : ℝ)) μ =
    (∫ Candidate, (FlippedOnes Parent Candidate : ℝ)^2 ∂μ) -
      (∫ Candidate, (FlippedOnes Parent Candidate : ℝ) ∂μ)^2 at Raw
  rw [FlippedOnesVariance, FlippedOnesExpectation] at Raw
  have Formula (Candidate : Bits n) :
      (FlippedOnes Parent Candidate : ℝ)*((FlippedOnes Parent Candidate : ℝ)-1) =
        (FlippedOnes Parent Candidate : ℝ)^2-(FlippedOnes Parent Candidate : ℝ) := by ring
  simp_rw [Formula]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, FlippedOnesExpectation]
  change (∫ Candidate, (FlippedOnes Parent Candidate : ℝ)^2 ∂μ) -
    (p : ℝ)*(OneMax Parent : ℝ) = _
  nlinarith [Raw]

theorem FlippedOnesAtLeastOneProbability {n : ℕ} (p : I) (Parent : Bits n) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {Candidate | 1 ≤ (FlippedOnes Parent Candidate : ℝ)} ≤ (p : ℝ)*(OneMax Parent : ℝ) := by
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let A : Set (Bits n) := {Candidate | 1 ≤ (FlippedOnes Parent Candidate : ℝ)}
  have Comparison (Candidate : Bits n) :
      A.indicator (fun _ => (1 : ℝ)) Candidate ≤ (FlippedOnes Parent Candidate : ℝ) := by
    by_cases Member : Candidate ∈ A
    · rw [Set.indicator_of_mem Member]
      exact Member
    · rw [Set.indicator_of_notMem Member]
      exact Nat.cast_nonneg _
  have Bound := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite Comparison
  rw [integral_indicator_const _ (Set.to_countable _).measurableSet,
    smul_eq_mul, mul_one, FlippedOnesExpectation] at Bound
  exact Bound

/-- A second-factorial-moment bound on the same mutation law. Integrality
of the number of flips is used at parent count three, not approximated away. -/
theorem FlippedOnesHalfProbability {n : ℕ} (p : I) (Parent : Bits n)
    (AtLeastThree : 3 ≤ OneMax Parent) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {Candidate | (OneMax Parent : ℝ)/2 ≤ (FlippedOnes Parent Candidate : ℝ)} ≤ 8*(p : ℝ)^2 := by
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let s : ℝ := OneMax Parent
  let Z : Bits n → ℝ := fun Candidate => FlippedOnes Parent Candidate
  let W : Bits n → ℝ := fun Candidate => Z Candidate*(Z Candidate-1)
  let A : Set (Bits n) := {Candidate | s/2 ≤ Z Candidate}
  have Three : (3 : ℝ) ≤ s := by dsimp [s]; exact_mod_cast AtLeastThree
  have PositiveS : 0 < s := by linarith
  have PositiveSquare : 0 < s^2 := sq_pos_of_pos PositiveS
  have NonnegativeW (Candidate : Bits n) : 0 ≤ W Candidate := by
    by_cases Zero : FlippedOnes Parent Candidate = 0
    · simp [W, Z, Zero]
    · have One : 1 ≤ Z Candidate := by
        dsimp [Z]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero
      exact mul_nonneg (by dsimp [Z]; exact Nat.cast_nonneg _) (sub_nonneg.mpr One)
  have Comparison (Candidate : Bits n) :
      A.indicator (fun _ => (1 : ℝ)) Candidate ≤ (8/s^2)*W Candidate := by
    by_cases Member : Candidate ∈ A
    · rw [Set.indicator_of_mem Member]
      change s/2 ≤ Z Candidate at Member
      have TwoNat : 2 ≤ FlippedOnes Parent Candidate := by
        by_contra NotTwo
        have AtMostOne : FlippedOnes Parent Candidate ≤ 1 := by omega
        have Upper : Z Candidate ≤ 1 := by dsimp [Z]; exact_mod_cast AtMostOne
        linarith
      have Two : (2 : ℝ) ≤ Z Candidate := by dsimp [Z]; exact_mod_cast TwoNat
      have NonnegativeZ : 0 ≤ Z Candidate := by dsimp [Z]; exact Nat.cast_nonneg _
      have CompareSquare : 0 ≤ (2*Z Candidate-s)*(2*Z Candidate+s) :=
        mul_nonneg (by linarith) (by positivity)
      have IntegerProduct : 0 ≤ Z Candidate*(Z Candidate-2) :=
        mul_nonneg NonnegativeZ (by linarith)
      have FactorialBound : s^2 ≤ 8*W Candidate := by
        dsimp [W]
        nlinarith [CompareSquare, IntegerProduct]
      calc
        (1 : ℝ) ≤ (8*W Candidate)/(s^2) :=
          (le_div_iff₀ PositiveSquare).mpr (by simpa only [one_mul] using FactorialBound)
        _ = (8/s^2)*W Candidate := by ring
    · rw [Set.indicator_of_notMem Member]
      exact mul_nonneg (by positivity) (NonnegativeW Candidate)
  have Bound := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite Comparison
  rw [integral_indicator_const _ (Set.to_countable _).measurableSet,
    smul_eq_mul, mul_one, integral_const_mul] at Bound
  have Moment : (∫ Candidate, W Candidate ∂μ) = (p : ℝ)^2*s*(s-1) :=
    FlippedOnesFactorialMoment p Parent
  rw [Moment] at Bound
  apply Bound.trans
  calc
    (8/s^2)*((p : ℝ)^2*s*(s-1)) = (8*(p : ℝ)^2*s*(s-1))/(s^2) := by ring
    _ ≤ 8*(p : ℝ)^2 := by
      apply (div_le_iff₀ PositiveSquare).mpr
      nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) PositiveS.le]

end
end ECTheoryLib.Analysis.EALinearMinimization

