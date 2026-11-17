import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Operators.Mutation.IndependentBitBounds
import ECTheoryLib.Analysis.OneMax.ElitistBitFlip

/-! Local multiplicative progress of the actual (1+1) EA maximizing OneMax.
The mutation is the existing independent-bit PMF, with rate 1/n, and fitness ties
are accepted. The potential is the number of zero coordinates. -/
namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- The number of zero coordinates, defined by the problem independently of algorithms. -/
abbrev ZeroCount {n : Nat} (x : Bits n) : Nat := Problems.OneMax.ZeroCount x
/-- The zero count embedded in the reals for signed drift calculations. -/
abbrev Potential {n : Nat} (x : Bits n) : ℝ := OneMax.ZeroPotential x
/-- Elitist OneMax maximization, accepting equal-fitness offspring. -/
abbrev Update {n : Nat} (x y : Bits n) : Bits n :=
  ElitistSelect (Problems.MaxNotWorse OneMax) x y
/-- The actual library EA kernel with mutation rate `1/n` and OneMax selection. -/
def Step {n : Nat} (hn : 0 < n) : Transition (Bits n) :=
  OnePlusOneEAStep hn (Problems.MaxNotWorse OneMax)

/-- Zero potential characterizes the unique optimum, including the empty bit string. -/
theorem ZeroIffTarget {n : Nat} (x : Bits n) :
    ZeroCount x = 0 ↔ x = AllOnes n := by
  exact Problems.OneMax.ZeroCountEqZeroIffAllOnes x

/-- Every candidate produces a nonnegative potential decrease after elitist selection. -/
theorem UpdateDecreaseNonnegative {n : Nat} (x y : Bits n) :
    0 ≤ Potential x - Potential (Update x y) := by
  have FitnessNondecreasing : OneMax x ≤ OneMax (Update x y) := by
    unfold Update ElitistSelect Problems.MaxNotWorse
    split_ifs with Accepted
    · exact Accepted
    · exact le_rfl
  change 0 ≤ OneMax.ZeroPotential x - OneMax.ZeroPotential (Update x y)
  unfold OneMax.ZeroPotential
  rw [Problems.OneMax.ZeroCountAsRealDifference, Problems.OneMax.ZeroCountAsRealDifference]
  have RealFitness : (OneMax x : ℝ) ≤ (OneMax (Update x y) : ℝ) := by
    exact_mod_cast FitnessNondecreasing
  linarith

/-- Elitist selection cannot leave zero potential, regardless of the proposed child. -/
theorem UpdatePreservesZero {n : Nat} (x y : Bits n) (Zero : ZeroCount x = 0) :
    ZeroCount (Update x y) = 0 := by
  have Decrease := UpdateDecreaseNonnegative x y
  change 0 ≤ (ZeroCount x : ℝ) - (ZeroCount (Update x y) : ℝ) at Decrease
  rw [Zero, Nat.cast_zero, zero_sub] at Decrease
  have Nonnegative : 0 ≤ (ZeroCount (Update x y) : ℝ) := Nat.cast_nonneg _
  exact Nat.cast_eq_zero.mp (le_antisymm (by linarith) Nonnegative)

/-- The path's absorbing-target premise is proved from the actual map kernel. -/
theorem StepPreservesZero {n : Nat} (hn : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step hn x).toMeasure, ZeroCount x = 0 → ZeroCount y = 0 := by
  have CandidateProperty : ∀ᵐ y ∂(StandardBitMutation hn x).toMeasure,
      ZeroCount x = 0 → ZeroCount (Update x y) = 0 := by
    exact ae_of_all _ (fun y => UpdatePreservesZero x y)
  change ∀ᵐ y ∂((StandardBitMutation hn x).map (Update x)).toMeasure, _
  rw [← PMF.toMeasure_map (Update x) (StandardBitMutation hn x) (measurable_of_finite _)]
  exact (ae_map_iff (measurable_of_finite (Update x)).aemeasurable
    (Set.to_countable _).measurableSet).mpr CandidateProperty

/-- Only single-bit events are counted; all other accepted updates contribute
nonnegative progress. No equality of the actual drift is assumed. -/
theorem OneStepDriftLowerBound {n : Nat} (hn : 0 < n) (x : Bits n) :
    StandardOneBitProbability n * Potential x ≤
      ∫ y, Potential x - Potential y ∂(Step hn x).toMeasure := by
  classical
  rw [Step, OnePlusOneEAStep]
  change _ ≤ ∫ y, Potential x - Potential y
    ∂((StandardBitMutation hn x).map (Update x)).toMeasure
  rw [← PMF.toMeasure_map (Update x) (StandardBitMutation hn x) (measurable_of_finite _),
    integral_map_of_stronglyMeasurable (measurable_of_finite (Update x))
      (measurable_of_finite (fun y : Bits n => Potential x - Potential y)).stronglyMeasurable,
    PMF.integral_eq_sum]
  let Offspring := Finset.univ.image (OnebitMutation x)
  -- These mutually exclusive offspring account for one-bit progress; every omitted
  -- mutation contributes a nonnegative amount after elitist selection.
  have NonnegativeTerms : ∀ y : Bits n,
      0 ≤ (StandardBitMutation hn x y).toReal * (Potential x - Potential (Update x y)) := by
    intro y
    exact mul_nonneg ENNReal.toReal_nonneg (UpdateDecreaseNonnegative x y)
  have PartialSumBound :
      (∑ y ∈ Offspring, (StandardBitMutation hn x y).toReal *
        (Potential x - Potential (Update x y))) ≤
      ∑ y : Bits n, (StandardBitMutation hn x y).toReal *
        (Potential x - Potential (Update x y)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Offspring)
    intro y _InUniv _Outside
    exact NonnegativeTerms y
  have PartialSum :
      (∑ y ∈ Offspring, (StandardBitMutation hn x y).toReal *
        (Potential x - Potential (Update x y))) = StandardOneBitProbability n * Potential x := by
    rw [Finset.sum_image (fun i _ j _ Equal => OnebitMutationInjective x Equal)]
    have AtCoordinate : ∀ i : Fin n,
        (StandardBitMutation hn x (OnebitMutation x i)).toReal *
          (Potential x - Potential (Update x (OnebitMutation x i))) =
        StandardOneBitProbability n * (if x i then (0 : ℝ) else 1) := by
      intro i
      rw [StandardBitMutationOneBitReal]
      exact congrArg (fun d => StandardOneBitProbability n * d) (OneMax.ElitistBitFlipDecrease x i)
    simp_rw [AtCoordinate]
    rw [← Finset.mul_sum, Problems.OneMax.ZeroBitCountAsReal]
  rw [PartialSum] at PartialSumBound
  exact PartialSumBound

end
end ECTheoryLib.Analysis.EAOneMax

namespace ECTheoryLib.Analysis.EAOneMax
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A uniform additive mean decrease before half progress, obtained from the
existing actual-EA one-bit drift lower bound rather than an assumed drift law. -/
theorem HalfProgressAdditiveDrift (m : ℕ) (PositiveM : 0 < m)
    (Parent : Bits (2*m)) (Above : (m : ℝ) < Potential Parent) :
    1 / (2 * Real.exp 1) ≤
      ∫ Next, Potential Parent - Potential Next
        ∂(Step (Nat.mul_pos (by decide : 0 < 2) PositiveM) Parent).toMeasure := by
  let PositiveLength : 0 < 2*m := Nat.mul_pos (by decide) PositiveM
  have PositiveProbability := StandardOneBitProbabilityPositive PositiveLength
  have ScaledInverse := (div_le_iff₀ PositiveProbability).mp
    (StandardOneBitProbabilityInverseBound PositiveLength)
  have HalfScale : 1 / (2 * Real.exp 1) ≤
      StandardOneBitProbability (2*m) * (m : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos 1))).mpr
    push_cast at ScaledInverse
    nlinarith only [ScaledInverse]
  exact HalfScale.trans ((mul_le_mul_of_nonneg_left Above.le PositiveProbability.le).trans
    (OneStepDriftLowerBound PositiveLength Parent))

end
end ECTheoryLib.Analysis.EAOneMax
