import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RankPotential
import ECTheoryLib.Analysis.Linear.OnePlusOneEA.AcceptedMutation
import ECTheoryLib.Problems.Linear.BinVal
import Mathlib.Probability.Independence.Integration

/-! Exact signed OneMax drift at BinVal's highest-one-only state.
The library's BinVal stores the most significant coordinate first. A tail
length k therefore describes k+1 actual bits and standard rate1/(k+1). -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open scoped BigOperators unitInterval
noncomputable section

/-- One most-significant bit and otherwise zeros, in the existing BinVal order. -/
def BinValHighestOne (TailLength : ℕ) : Bits (TailLength+1) :=
  fun j => decide (j = (0 : Fin (TailLength+1)))

theorem BinValHighestOneCount (TailLength : ℕ) : OneMax (BinValHighestOne TailLength) = 1 :=
  Problems.Linear.BinVal.OneCountSingleOne (0 : Fin (TailLength+1))

theorem BinValHighestOneScore (TailLength : ℕ) :
    Problems.Linear.BinVal.Score (BinValHighestOne TailLength) = (2 : ℝ)^TailLength := by
  unfold BinValHighestOne
  rw [Problems.Linear.BinVal.ScoreSingleOne, Problems.Linear.BinVal.FirstWeight]

/-- Removing the highest one accepts every lower-bit pattern, on the real BinVal objective. -/
theorem BinValWithoutHighestStrictlyBetter (TailLength : ℕ) (Candidate : Bits (TailLength+1))
    (HeadZero : Candidate (0 : Fin (TailLength+1)) = false) :
    Problems.Linear.BinVal.Score Candidate < Problems.Linear.BinVal.Score (BinValHighestOne TailLength) := by
  classical
  let W := Problems.Linear.BinVal.Weights (n := TailLength+1)
  have ScoreUpper : Problems.Linear.BinVal.Score Candidate ≤
      ∑ j ∈ (Finset.univ : Finset (Fin (TailLength+1))).erase 0, W j := by
    change (∑ j : Fin (TailLength+1), W j*(if Candidate j then (1 : ℝ) else 0)) ≤ _
    rw [← Finset.add_sum_erase Finset.univ (fun j => W j*(if Candidate j then (1 : ℝ) else 0)) (Finset.mem_univ 0)]
    simp only [HeadZero, Bool.false_eq_true, if_false, mul_zero, zero_add]
    apply Finset.sum_le_sum
    intro j _
    cases Candidate j with
    | false =>
      simp only [Bool.false_eq_true, if_false, mul_zero]
      exact (Problems.Linear.BinVal.WeightPositive j).le
    | true => simp
  have SumOthers : (∑ j ∈ (Finset.univ : Finset (Fin (TailLength+1))).erase 0, W j) = (2 : ℝ)^TailLength-1 := by
    have Split := Finset.add_sum_erase (Finset.univ : Finset (Fin (TailLength+1))) W (Finset.mem_univ 0)
    change Problems.Linear.BinVal.Weights (0 : Fin (TailLength+1))+
      (∑ j ∈ (Finset.univ : Finset (Fin (TailLength+1))).erase 0, W j) =
      ∑ j : Fin (TailLength+1), Problems.Linear.BinVal.Weights j at Split
    rw [Problems.Linear.BinVal.FirstWeight, Problems.Linear.BinVal.WeightsSum, pow_succ] at Split
    linarith
  rw [BinValHighestOneScore]
  exact ScoreUpper.trans_lt (by rw [SumOthers]; linarith)

theorem BinValHighestRemovedSelected (TailLength : ℕ) (Candidate : Bits (TailLength+1))
    (HeadZero : Candidate (0 : Fin (TailLength+1)) = false) :
    ElitistSelect (Problems.MinNotWorse (Score Problems.Linear.BinVal.Weights))
      (BinValHighestOne TailLength) Candidate = Candidate :=
  ElitistSelectAccept _ _ _ (BinValWithoutHighestStrictlyBetter TailLength Candidate HeadZero).le

/-- Exact selected-count decrement before integration. The retained-head branch
has no downward removal and hence selects the parent under positive weights. -/
theorem BinValHighestOneSelectedCountDifference (TailLength : ℕ) (Candidate : Bits (TailLength+1)) :
    (OneMax (BinValHighestOne TailLength) : ℝ)-
      (OneMax (ElitistSelect (Problems.MinNotWorse (Score Problems.Linear.BinVal.Weights))
        (BinValHighestOne TailLength) Candidate) : ℝ) =
    (1-(if Candidate (0 : Fin (TailLength+1)) then (1 : ℝ) else 0))-
      ∑ j ∈ (Finset.univ : Finset (Fin (TailLength+1))).erase 0,
        (1-(if Candidate (0 : Fin (TailLength+1)) then (1 : ℝ) else 0))*
          (if Candidate j then (1 : ℝ) else 0) := by
  classical
  cases Head : Candidate (0 : Fin (TailLength+1)) with
  | false =>
    rw [BinValHighestRemovedSelected TailLength Candidate Head, BinValHighestOneCount]
    simp only [Nat.cast_one, Bool.false_eq_true, if_false, sub_zero, one_mul]
    congr 1
    rw [← ScoreUnitWeights Candidate]
    simp only [Score, one_mul]
    rw [← Finset.add_sum_erase Finset.univ
      (fun j : Fin (TailLength+1) => if Candidate j then (1 : ℝ) else 0) (Finset.mem_univ 0)]
    simp [Head]
  | true =>
    have NoRemoval : FlippedOnes (BinValHighestOne TailLength) Candidate = 0 := by
      unfold FlippedOnes
      apply Finset.sum_eq_zero
      intro j _
      by_cases AtHead : j = (0 : Fin (TailLength+1))
      · subst j
        simp [BinValHighestOne, Head]
      · simp [BinValHighestOne, AtHead]
    rw [SelectWithoutRemovalEqParent Problems.Linear.BinVal.Weights Problems.Linear.BinVal.WeightPositive
      (BinValHighestOne TailLength) Candidate NoRemoval]
    simp

/-- Exact signed mean for every independent mutation rate p, under actual BinVal selection. -/
theorem BinValHighestOneCountMean (TailLength : ℕ) (p : I) :
    (∫ Candidate, (OneMax (BinValHighestOne TailLength) : ℝ)-
      (OneMax (ElitistSelect (Problems.MinNotWorse (Score Problems.Linear.BinVal.Weights))
        (BinValHighestOne TailLength) Candidate) : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p)
        (BinValHighestOne TailLength)).toMeasure) =
      (p : ℝ)*(1-(TailLength : ℝ)*(p : ℝ)) := by
  classical
  let Parent := BinValHighestOne TailLength
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let Y := fun (j : Fin (TailLength+1)) (Candidate : Bits (TailLength+1)) => if Candidate j then (1 : ℝ) else 0
  let S := (Finset.univ : Finset (Fin (TailLength+1))).erase 0
  have HeadMean : (∫ y, Y 0 y ∂μ) = 1-(p : ℝ) := by
    simpa [Y, Parent, BinValHighestOne, MutationOneProbability] using
      OneMaxMutation.MutationOneCoordinateExpectation p Parent (0 : Fin (TailLength+1))
  have TailMean (j : Fin (TailLength+1)) (Member : j ∈ S) : (∫ y, Y j y ∂μ) = (p : ℝ) := by
    have ParentZero : Parent j = false := by
      simp [Parent, BinValHighestOne, (Finset.mem_erase.mp Member).1]
    simpa only [Y, ParentZero, MutationOneProbability, Bool.false_eq_true, if_false] using
      OneMaxMutation.MutationOneCoordinateExpectation p Parent j
  have DownMean : (∫ y, 1-Y 0 y ∂μ) = (p : ℝ) := by
    rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const, probReal_univ, one_smul, HeadMean]
    ring
  have PairMean (j : Fin (TailLength+1)) (Member : j ∈ S) :
      (∫ y, (1-Y 0 y)*Y j y ∂μ) = (p : ℝ)^2 := by
    have Different : (0 : Fin (TailLength+1)) ≠ j := (Finset.mem_erase.mp Member).1.symm
    have Independent := (OneMaxMutation.MutationOneCoordinatesIndependent p Parent).indepFun Different
    have Product := Independent.integral_fun_mul_eq_mul_integral
      (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable
    change (∫ y, Y 0 y*Y j y ∂μ) = (∫ y, Y 0 y ∂μ)*(∫ y, Y j y ∂μ) at Product
    rw [HeadMean, TailMean j Member] at Product
    have Functions : (fun y => (1-Y 0 y)*Y j y) = fun y => Y j y-Y 0 y*Y j y := by
      funext y
      ring
    rw [Functions, integral_sub Integrable.of_finite Integrable.of_finite, TailMean j Member, Product]
    ring
  have SumMean : (∫ y, ∑ j ∈ S, (1-Y 0 y)*Y j y ∂μ) = (TailLength : ℝ)*(p : ℝ)^2 := by
    rw [integral_finsetSum S (fun _ _ => Integrable.of_finite)]
    calc
      _ = ∑ _j ∈ S, (p : ℝ)^2 := Finset.sum_congr rfl (fun j Member => PairMean j Member)
      _ = _ := by simp [S]
  have Functions : (fun Candidate => (OneMax (BinValHighestOne TailLength) : ℝ)-
        (OneMax (ElitistSelect (Problems.MinNotWorse (Score Problems.Linear.BinVal.Weights))
          (BinValHighestOne TailLength) Candidate) : ℝ)) =
      fun y => (1-Y 0 y)-∑ j ∈ S, (1-Y 0 y)*Y j y := by
    funext y
    exact BinValHighestOneSelectedCountDifference TailLength y
  rw [Functions]
  change (∫ y, (1-Y 0 y)-∑ j ∈ S, (1-Y 0 y)*Y j y ∂μ) = _
  rw [integral_sub Integrable.of_finite Integrable.of_finite, DownMean, SumMean]
  ring

/-- At standard rate the actual signed OneMax drift is positive1/n^2, for every n>0. -/
theorem BinValHighestOneStandardCountDrift (TailLength : ℕ) :
    (∫ Next, (OneMax (BinValHighestOne TailLength) : ℝ)-(OneMax Next : ℝ)
      ∂(Step (by omega : 0 < TailLength+1) Problems.Linear.BinVal.Weights
        (BinValHighestOne TailLength)).toMeasure) = 1/((TailLength : ℝ)+1)^2 := by
  have NPositive : (0 : ℝ) < (TailLength : ℝ)+1 := by positivity
  let p : I := ⟨1/((TailLength : ℝ)+1), ⟨by positivity,
    (div_le_one NPositive).mpr (by linarith [(Nat.cast_nonneg TailLength : (0 : ℝ) ≤ TailLength)])⟩⟩
  have Mean := BinValHighestOneCountMean TailLength p
  have Rate : ENNReal.ofReal (p : ℝ) = ((TailLength+1 : ℕ) : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/((TailLength : ℝ)+1)) = ((TailLength+1 : ℕ) : ENNReal)⁻¹
    have Denominator : ((TailLength+1 : ℕ) : ℝ) = (TailLength : ℝ)+1 := by simp
    rw [← Denominator, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (by omega : 0 < TailLength+1)),
      ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  simp only [Rate] at Mean
  unfold Step OnePlusOneEAStep
  rw [PMFIntegralMap]
  change (∫ Candidate, (OneMax (BinValHighestOne TailLength) : ℝ)-
    (OneMax (ElitistSelect (Problems.MinNotWorse (Score Problems.Linear.BinVal.Weights))
      (BinValHighestOne TailLength) Candidate) : ℝ)
    ∂(IndependentBitMutation ((TailLength+1 : ℕ) : ENNReal)⁻¹
      (StandardBitMutationRateBound (TailLength+1) (by omega)) (BinValHighestOne TailLength)).toMeasure) = _
  rw [Mean]
  change (1/((TailLength : ℝ)+1))*(1-(TailLength : ℝ)*(1/((TailLength : ℝ)+1))) = 1/((TailLength : ℝ)+1)^2
  have Nonzero := ne_of_gt NPositive
  field_simp
  ring

end
end ECTheoryLib.Analysis.EALinearMinimization

