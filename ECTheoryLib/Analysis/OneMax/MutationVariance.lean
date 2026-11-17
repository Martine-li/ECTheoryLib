import ECTheoryLib.Probability.Concentration.Bennett
import ECTheoryLib.Analysis.OneMax.MutationExpectation
import ECTheoryLib.Analysis.BitMutation.CoordinateMoments

/-!
# Actual mutation OneMax mean, variance and concentration

The shared CoordinateMoments module supplies independence and marginal moments.
The existing independent-bit PMF has mean
np+(1-2p)OneMax(parent) and score variance np(1-p). Both Bennett and Bernstein
tails include all rates in[0,1] and empty strings. These are candidate laws.
-/

namespace ECTheoryLib.Analysis.OneMaxMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- The objective of the actual candidate has mean np+(1-2p)OneMax(parent). -/
theorem MutationOneMaxExpectation {n : ℕ} (p : I) (Parent : Bits n) :
    (∫ y, (OneMax y : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)=
      (n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ) := by
  have Mean := MutationZeroCountExpectation p Parent
  simp_rw [Problems.OneMax.ZeroCountAsRealDifference] at Mean
  rw [integral_sub (integrable_const _) Integrable.of_finite,integral_const,probReal_univ,one_smul] at Mean
  linarith

/-- The sum of actual marginal variances is n*p*(1-p). -/
theorem MutationOneMaxMarginalVariance {n : ℕ} (p : I) (Parent : Bits n) :
    (∑ i : Fin n, variance (fun y : Bits n => if y i then (1 : ℝ) else 0)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)=
      (n : ℝ)*(p : ℝ)*(1-(p : ℝ)) := by
  simp only [MutationOneCoordinateVariance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Mathlib's independent variance sum identifies the actual candidate-score variance. -/
theorem MutationOneMaxVariance {n : ℕ} (p : I) (Parent : Bits n) :
    variance (fun y => (OneMax y : ℝ))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure=
      (n : ℝ)*(p : ℝ)*(1-(p : ℝ)) := by
  have Bound := IndepFun.variance_sum (s := Finset.univ)
    (fun i _ => MutationOneCoordinateMemLp p Parent i)
    (fun _ _ _ _ Different => (MutationOneCoordinatesIndependent p Parent).indepFun Different)
  have Sum : (∑ i : Fin n, fun y : Bits n => if y i then (1 : ℝ) else 0) = fun y => (OneMax y : ℝ) := by
    funext y
    simp only [Finset.sum_apply,OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Sum,MutationOneMaxMarginalVariance] at Bound
  exact Bound

/-- Both centered one-sided bounds follow from the actual Bernoulli coordinate means. -/
theorem MutationOneCoordinateCenteredBounds {n : ℕ} (p : I) (Parent : Bits n) (i : Fin n) :
    ∀ᵐ y ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure,
      (if y i then (1 : ℝ) else 0)∈Icc
        ((∫ z, (if z i then (1 : ℝ) else 0)
          ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)-1)
        ((∫ z, (if z i then (1 : ℝ) else 0)
          ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)+1) := by
  rw [MutationOneCoordinateExpectation]
  have Bounds := (MutationOneProbability p (Parent i)).2
  apply ae_of_all
  intro y
  cases y i <;> simp only [ite_true,Bool.false_eq_true,ite_false,mem_Icc] <;> constructor <;> linarith [Bounds.1,Bounds.2]

/-- Variance-sensitive upper tail of the actual candidate OneMax value. -/
theorem MutationOneMaxBennettUpper {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)+d≤(OneMax y : ℝ)}≤
      BennettUpperBound ((n : ℝ)*(p : ℝ)*(1-(p : ℝ))) d := by
  have Bound := IndependentSumBennettUpperAll _ (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (MutationOneCoordinateMemLp p Parent) (MutationOneCoordinatesIndependent p Parent)
    (fun i => (MutationOneCoordinateCenteredBounds p Parent i).mono (fun _ h => h.2)) d Nonnegative
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0)=(OneMax y : ℝ) := by
    simp only [OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [Sum,MutationOneMaxExpectation,MutationOneMaxMarginalVariance] at Bound
  exact Bound

theorem MutationOneMaxBennettLower {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ)≤(n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)-d}≤
      BennettUpperBound ((n : ℝ)*(p : ℝ)*(1-(p : ℝ))) d := by
  have Bound := IndependentSumBennettLower _ (fun (i : Fin n) (y : Bits n) => if y i then (1 : ℝ) else 0)
    (MutationOneCoordinateMemLp p Parent) (MutationOneCoordinatesIndependent p Parent)
    (fun i => (MutationOneCoordinateCenteredBounds p Parent i).mono (fun _ h => h.1)) d Nonnegative
  have Sum (y : Bits n) : (∑ i : Fin n, if y i then (1 : ℝ) else 0)=(OneMax y : ℝ) := by
    simp only [OneMax,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [Sum,MutationOneMaxExpectation,MutationOneMaxMarginalVariance] at Bound
  exact Bound

theorem MutationOneMaxBernsteinUpper {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)+d≤(OneMax y : ℝ)}≤
      Real.exp (-d^2/(2*((n : ℝ)*(p : ℝ)*(1-(p : ℝ)))+2*d/3)) :=
  (MutationOneMaxBennettUpper p Parent d Nonnegative).trans
    (BennettUpperBoundLeBernstein _ d
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) p.2.1) (sub_nonneg.mpr p.2.2)) Nonnegative)

theorem MutationOneMaxBernsteinLower {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (OneMax y : ℝ)≤(n : ℝ)*(p : ℝ)+(1-2*(p : ℝ))*(OneMax Parent : ℝ)-d}≤
      Real.exp (-d^2/(2*((n : ℝ)*(p : ℝ)*(1-(p : ℝ)))+2*d/3)) :=
  (MutationOneMaxBennettLower p Parent d Nonnegative).trans
    (BennettUpperBoundLeBernstein _ d
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) p.2.1) (sub_nonneg.mpr p.2.2)) Nonnegative)

end
end ECTheoryLib.Analysis.OneMaxMutation
