import ECTheoryLib.Probability.Concentration.ScaledVarianceChernoff
import ECTheoryLib.Problems.Linear
import ECTheoryLib.Analysis.BitMutation.CoordinateMoments

/-!
# Actual independent-bit mutation for signed linear scores

Candidate mean is p*sum(weights)+(1-2p)*parentScore; actual variance is
p*(1-p)*sum(weights^2). Coordinate independence and marginal moments reuse
the existing mutation law. Absolute weights supply both centered bounds.
Both finite-size tails are consequences for the actual candidate PMF.
-/

namespace ECTheoryLib.Analysis.LinearMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Analysis.OneMaxMutation ECTheoryLib.Problems.Linear
open scoped unitInterval
noncomputable section

theorem WeightedCoordinatesIndependent {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n) :
    iIndepFun (fun (i : Fin n) (y : Bits n) => Weights i*(if y i then (1 : ℝ) else 0))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure :=
  (MutationOneCoordinatesIndependent p Parent).comp (fun i x => Weights i*x) (fun _ => by fun_prop)

theorem WeightedCoordinateMemLp {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n) (i : Fin n) :
    MemLp (fun y : Bits n => Weights i*(if y i then (1 : ℝ) else 0)) 2
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure :=
  (MutationOneCoordinateMemLp p Parent i).const_mul (Weights i)

/-- The exact mean depends on the parent through its actual linear score. -/
theorem ScoreExpectation {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n) :
    (∫ y, Score Weights y
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)=
      (p : ℝ)*(∑ i, Weights i)+(1-2*(p : ℝ))*Score Weights Parent := by
  unfold Score
  rw [integral_finsetSum _ (fun i _ => (WeightedCoordinateMemLp p Weights Parent i).integrable (by norm_num))]
  simp_rw [integral_const_mul,MutationOneCoordinateExpectation]
  have Coordinate (i : Fin n) : (MutationOneProbability p (Parent i) : ℝ)=
      (p : ℝ)+(1-2*(p : ℝ))*(if Parent i then 1 else 0) := by
    cases Parent i <;> simp [MutationOneProbability]
    ring
  simp_rw [Coordinate,mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_comm (Weights _) (p : ℝ),← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem MarginalVarianceSum {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n) :
    (∑ i : Fin n, variance (fun y : Bits n => Weights i*(if y i then (1 : ℝ) else 0))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)=
      (p : ℝ)*(1-(p : ℝ))*(∑ i, (Weights i)^2) := by
  simp only [variance_const_mul,MutationOneCoordinateVariance]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ScoreVariance {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n) :
    variance (Score Weights)
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure=
      (p : ℝ)*(1-(p : ℝ))*(∑ i, (Weights i)^2) := by
  have Identity := IndepFun.variance_sum (s := Finset.univ)
    (fun i _ => WeightedCoordinateMemLp p Weights Parent i)
    (fun _ _ _ _ Different => (WeightedCoordinatesIndependent p Weights Parent).indepFun Different)
  have Sum : (∑ i : Fin n, fun y : Bits n => Weights i*(if y i then (1 : ℝ) else 0))=Score Weights := by
    funext y
    exact Finset.sum_apply _ _ _
  rw [Sum,MarginalVarianceSum] at Identity
  exact Identity

/-- Absolute weights control both centered sides, including signed objectives. -/
theorem WeightedCoordinateCenteredBounds {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n)
    (b : ℝ) (WeightBound : ∀ i, |Weights i|≤b) (i : Fin n) :
    ∀ᵐ y ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure,
      Weights i*(if y i then (1 : ℝ) else 0)∈Icc
        ((∫ z, Weights i*(if z i then (1 : ℝ) else 0)
          ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)-b)
        ((∫ z, Weights i*(if z i then (1 : ℝ) else 0)
          ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)+b) := by
  rw [integral_const_mul,MutationOneCoordinateExpectation]
  have Prob := (MutationOneProbability p (Parent i)).2
  apply ae_of_all
  intro y
  have Unit : |(if y i then (1 : ℝ) else 0)-(MutationOneProbability p (Parent i) : ℝ)|≤1 := by
    rw [abs_le]
    cases y i <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> constructor <;> linarith [Prob.1,Prob.2]
  have Bound : |Weights i*((if y i then (1 : ℝ) else 0)-(MutationOneProbability p (Parent i) : ℝ))|≤b := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left Unit (abs_nonneg _)).trans (by simpa only [mul_one] using WeightBound i)
  rw [abs_le] at Bound
  simp only [mem_Icc]
  constructor <;> nlinarith [Bound.1,Bound.2]

theorem ScoreFiniteVarianceUpper {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n)
    (b : ℝ) (PositiveScale : 0<b) (WeightBound : ∀ i, |Weights i|≤b)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (p : ℝ)*(∑ i, Weights i)+(1-2*(p : ℝ))*Score Weights Parent+d≤Score Weights y}≤
      ScaledVarianceFiniteUpperBound n b ((p : ℝ)*(1-(p : ℝ))*(∑ i, (Weights i)^2)) d := by
  have Bound := IndependentSumFiniteVarianceUpperScaled _
    (fun (i : Fin n) (y : Bits n) => Weights i*(if y i then (1 : ℝ) else 0))
    (WeightedCoordinateMemLp p Weights Parent) (WeightedCoordinatesIndependent p Weights Parent)
    b PositiveScale (fun i => (WeightedCoordinateCenteredBounds p Weights Parent b WeightBound i).mono (fun _ h => h.2))
    d Nonnegative
  change Measure.real _ {y | (∫ z, Score Weights z ∂_)+d≤Score Weights y}≤ScaledVarianceFiniteUpperBound n b _ d at Bound
  simpa only [ScoreExpectation,MarginalVarianceSum] using Bound

theorem ScoreFiniteVarianceLower {n : ℕ} (p : I) (Weights : Fin n → ℝ) (Parent : Bits n)
    (b : ℝ) (PositiveScale : 0<b) (WeightBound : ∀ i, |Weights i|≤b)
    (d : ℝ) (Nonnegative : 0≤d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | Score Weights y≤(p : ℝ)*(∑ i, Weights i)+(1-2*(p : ℝ))*Score Weights Parent-d}≤
      ScaledVarianceFiniteUpperBound n b ((p : ℝ)*(1-(p : ℝ))*(∑ i, (Weights i)^2)) d := by
  have Bound := IndependentSumFiniteVarianceLowerScaled _
    (fun (i : Fin n) (y : Bits n) => Weights i*(if y i then (1 : ℝ) else 0))
    (WeightedCoordinateMemLp p Weights Parent) (WeightedCoordinatesIndependent p Weights Parent)
    b PositiveScale (fun i => (WeightedCoordinateCenteredBounds p Weights Parent b WeightBound i).mono (fun _ h => h.1))
    d Nonnegative
  change Measure.real _ {y | Score Weights y≤(∫ z, Score Weights z ∂_)-d}≤ScaledVarianceFiniteUpperBound n b _ d at Bound
  simpa only [ScoreExpectation,MarginalVarianceSum] using Bound

end
end ECTheoryLib.Analysis.LinearMutation
