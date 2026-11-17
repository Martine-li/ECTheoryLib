import ECTheoryLib.Probability.Concentration.LowerChernoff
import ECTheoryLib.Probability.Concentration.FiniteChernoff
import ECTheoryLib.Probability.Concentration.Chernoff
import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Problems.TargetOneMax
import Mathlib.Tactic.Positivity

/-!
# Hamming concentration of actual independent bit mutation

The existing coordinate-product identity supplies independent mismatch
indicators on the actual mutation PMF. Their exact expectation is n*p.
All rates in [0,1] and empty strings are allowed; standard mutation requires
positive length and specializes the mean to one. No probability or
independence assumption about the operator is left to the caller.
-/

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- Each coordinate of actual independent bit mutation changes with probability p. -/
theorem MutationMismatchIntegral (p : I) (Parent : Bool) :
    (∫ b, (if b = Parent then (0 : ℝ) else 1)
      ∂bernoulliMeasure true false (MutationOneProbability p Parent)) = (p : ℝ) := by
  rw [integral_bernoulliMeasure]
  cases Parent with
  | false => simp only [MutationOneProbability, Bool.false_eq_true, ite_false,
      Bool.true_eq_false, ite_true, smul_eq_mul, mul_one, mul_zero, add_zero]
  | true =>
      simp only [MutationOneProbability, ite_true, Bool.false_eq_true, ite_false,
        smul_eq_mul, mul_zero, mul_one, zero_add, unitInterval.coe_symm_eq]
      ring

/-- The actual independent-mutation Hamming distance has mean n*p, including p=0 and p=1. -/
theorem MutationHammingExpectation {n : ℕ} (p : I) (Parent : Bits n) :
    (∫ y, (Hamming Parent y : ℝ)
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) =
      (n : ℝ)*(p : ℝ) := by
  classical
  rw [← IndependentBitMutationProductLaw p Parent]
  let P := Measure.pi (fun i => bernoulliMeasure true false (MutationOneProbability p (Parent i)))
  have CoordinateMean (i : Fin n) :
      (∫ y, (if y i = Parent i then (0 : ℝ) else 1) ∂P) = (p : ℝ) := by
    have Map := (measurePreserving_eval
      (fun j : Fin n => bernoulliMeasure true false (MutationOneProbability p (Parent j))) i).map_eq
    have IntegralMap := integral_map_of_stronglyMeasurable (measurable_pi_apply i)
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).stronglyMeasurable
      (μ := P)
    rw [Map] at IntegralMap
    rw [← IntegralMap, MutationMismatchIntegral]
  simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  change (∑ i : Fin n, ∫ y, (if y i = Parent i then (0 : ℝ) else 1) ∂P) = (n : ℝ)*(p : ℝ)
  simp only [CoordinateMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The actual mutation product law supplies all Chernoff assumptions for the Hamming distance. -/
theorem MutationHammingChernoff {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1+d)*((n : ℝ)*(p : ℝ)) ≤ (Hamming Parent y : ℝ)} ≤
      Real.exp (-((1+d)*Real.log (1+d)-d)*((n : ℝ)*(p : ℝ))) := by
  classical
  let P := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let X := fun (i : Fin n) (y : Bits n) => if y i = Parent i then (0 : ℝ) else 1
  have Independent : iIndepFun X P := by
    change iIndepFun X (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
    rw [← IndependentBitMutationProductLaw]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).aemeasurable)
  have InUnit (i : Fin n) : ∀ᵐ y ∂P, X i y ∈ Icc 0 1 := by
    apply ae_of_all
    intro y
    dsimp only [X]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have SumHamming (y : Bits n) : (∑ i, X i y) = (Hamming Parent y : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumChernoffUpper P X
    (fun _ => (measurable_of_finite _).aemeasurable) Independent InUnit d Nonnegative
  simp only [SumHamming] at Bound
  change (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1+d)*(∫ z, (Hamming Parent z : ℝ) ∂P) ≤ (Hamming Parent y : ℝ)} ≤ _ at Bound
  have Mean : (∫ z, (Hamming Parent z : ℝ) ∂P) = (n : ℝ)*(p : ℝ) :=
    MutationHammingExpectation p Parent
  rw [Mean] at Bound
  exact Bound

/-- Standard bit mutation has mean-one distance and this upper tail for every positive length. -/
theorem StandardMutationHammingChernoff {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | 1+d ≤ (Hamming Parent y : ℝ)} ≤
      Real.exp (-((1+d)*Real.log (1+d)-d)) := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have AtLeastOne : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨by positivity, (div_le_one PositiveReal).mpr AtLeastOne⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Mean : (n : ℝ)*(p : ℝ) = 1 := by
    change (n : ℝ)*(1/(n : ℝ)) = 1
    exact mul_one_div_cancel PositiveReal.ne'
  have Bound := MutationHammingChernoff p Parent d Nonnegative
  rw [Mean, mul_one, mul_one] at Bound
  unfold StandardBitMutation
  simpa only [Rate] using Bound

end
end ECTheoryLib.Analysis.BitMutation

/-!
## MGF and base-two large-jump bounds

The actual product law also supplies an MGF certificate for any tilt.
The base-two tail includes both mutation-rate endpoints and empty strings.
-/

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- The actual independent-mutation Hamming distance has the exponential MGF estimate for every real tilt. -/
theorem MutationHammingMGFBound {n : ℕ} (p : I) (Parent : Bits n) (t : ℝ) :
    mgf (fun y => (Hamming Parent y : ℝ))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure t ≤
      Real.exp (((n : ℝ)*(p : ℝ))*(Real.exp t-1)) := by
  classical
  let P := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let X := fun (i : Fin n) (y : Bits n) => if y i = Parent i then (0 : ℝ) else 1
  have Independent : iIndepFun X P := by
    change iIndepFun X (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
    rw [← IndependentBitMutationProductLaw]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).aemeasurable)
  have InUnit (i : Fin n) : ∀ᵐ y ∂P, X i y ∈ Icc 0 1 := by
    apply ae_of_all
    intro y
    dsimp only [X]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have SumHamming (y : Bits n) : (∑ i, X i y) = (Hamming Parent y : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumMGFBound P X
    (fun _ => (measurable_of_finite _).aemeasurable) Independent InUnit t
  simp only [SumHamming] at Bound
  change mgf (fun y => (Hamming Parent y : ℝ))
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure t ≤
      Real.exp ((∫ z, (Hamming Parent z : ℝ) ∂P)*(Real.exp t-1)) at Bound
  have Mean : (∫ z, (Hamming Parent z : ℝ) ∂P) = (n : ℝ)*(p : ℝ) :=
    MutationHammingExpectation p Parent
  rw [Mean] at Bound
  exact Bound

/-- The actual independent-mutation distance has the base-two tail beyond 2*e*n*p. -/
theorem MutationHammingBaseTwoTail {n : ℕ} (p : I) (Parent : Bits n)
    (k : ℝ) (LargeThreshold : 2*Real.exp 1*((n : ℝ)*(p : ℝ)) ≤ k) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤ (2 : ℝ)^(-k) := by
  exact MGFBaseTwoUpperTail _ _ _ k (mul_nonneg (Nat.cast_nonneg n) p.2.1)
    Integrable.of_finite (MutationHammingMGFBound p Parent _) LargeThreshold

/-- Standard bit mutation has the base-two tail beyond the constant threshold 2*e. -/
theorem StandardMutationHammingBaseTwoTail {n : ℕ}
    (PositiveLength : 0 < n) (Parent : Bits n)
    (k : ℝ) (LargeThreshold : 2*Real.exp 1 ≤ k) :
    (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | k ≤ (Hamming Parent y : ℝ)} ≤ (2 : ℝ)^(-k) := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have AtLeastOne : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨by positivity, (div_le_one PositiveReal).mpr AtLeastOne⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Mean : (n : ℝ)*(p : ℝ) = 1 := by
    change (n : ℝ)*(1/(n : ℝ)) = 1
    exact mul_one_div_cancel PositiveReal.ne'
  have Threshold : 2*Real.exp 1*((n : ℝ)*(p : ℝ)) ≤ k := by
    rw [Mean, mul_one]
    exact LargeThreshold
  have Bound := MutationHammingBaseTwoTail p Parent k Threshold
  unfold StandardBitMutation
  simpa only [Rate] using Bound

end
end ECTheoryLib.Analysis.BitMutation

/-!
## Finite-size mutation concentration

The actual coordinate product law and exact mean also instantiate the
strongest finite-size expression, with all mutation-rate and length boundaries.
-/

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- The actual mutation product law instantiates the full finite-size Chernoff bound for every rate in [0,1]. -/
theorem MutationHammingFiniteChernoff {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1+d)*((n : ℝ)*(p : ℝ)) ≤ (Hamming Parent y : ℝ)} ≤
      FiniteChernoffUpperBound n ((n : ℝ)*(p : ℝ)) d := by
  classical
  let P := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let X := fun (i : Fin n) (y : Bits n) => if y i = Parent i then (0 : ℝ) else 1
  have Independent : iIndepFun X P := by
    change iIndepFun X (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
    rw [← IndependentBitMutationProductLaw]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).aemeasurable)
  have InUnit (i : Fin n) : ∀ᵐ y ∂P, X i y ∈ Icc 0 1 := by
    apply ae_of_all
    intro y
    dsimp only [X]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have SumHamming (y : Bits n) : (∑ i, X i y) = (Hamming Parent y : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumFiniteChernoffUpper P X
    (fun _ => (measurable_of_finite _).aemeasurable) Independent InUnit d Nonnegative
  simp only [SumHamming] at Bound
  change (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (1+d)*(∫ z, (Hamming Parent z : ℝ) ∂P) ≤ (Hamming Parent y : ℝ)} ≤ _ at Bound
  have Mean : (∫ z, (Hamming Parent z : ℝ) ∂P) = (n : ℝ)*(p : ℝ) :=
    MutationHammingExpectation p Parent
  rw [Mean] at Bound
  exact Bound

/-- Standard mutation has mean one and inherits the finite-size bound for every nonnegative deviation. -/
theorem StandardMutationHammingFiniteChernoff {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (Nonnegative : 0 ≤ d) :
    (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | 1+d ≤ (Hamming Parent y : ℝ)} ≤
      FiniteChernoffUpperBound n 1 d := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have AtLeastOne : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨by positivity, (div_le_one PositiveReal).mpr AtLeastOne⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Mean : (n : ℝ)*(p : ℝ) = 1 := by
    change (n : ℝ)*(1/(n : ℝ)) = 1
    exact mul_one_div_cancel PositiveReal.ne'
  have Bound := MutationHammingFiniteChernoff p Parent d Nonnegative
  rw [Mean, mul_one] at Bound
  unfold StandardBitMutation
  simpa only [Rate] using Bound

end
end ECTheoryLib.Analysis.BitMutation

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- The standard mutation Hamming MGF has a dimension-independent bound. -/
theorem StandardMutationHammingMGFBound {n : ℕ} (PositiveLength : 0<n) (Parent : Bits n) (t : ℝ) :
    mgf (fun y => (Problems.TargetOneMax.Hamming Parent y : ℝ))
      (StandardBitMutation PositiveLength Parent).toMeasure t ≤ Real.exp (Real.exp t-1) := by
  have PositiveN : (0 : ℝ)<n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨by positivity, (div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ)=(n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ))=(n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Bound := MutationHammingMGFBound p Parent t
  simp only [Rate] at Bound
  have Mean : (n : ℝ)*(p : ℝ)=1 := mul_one_div_cancel PositiveN.ne'
  rw [Mean, one_mul] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.BitMutation

namespace ECTheoryLib.Analysis.BitMutation
open MeasureTheory ProbabilityTheory Set ECTheoryLib.Probability
open ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

/-- The actual mutation product law instantiates the full finite-size Chernoff bound for every rate in [0,1]. -/
theorem MutationHammingFiniteChernoffLower {n : ℕ} (p : I) (Parent : Bits n)
    (d : ℝ) (InUnitDeviation : d ∈ Icc 0 1) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (Hamming Parent y : ℝ) ≤ (1-d)*((n : ℝ)*(p : ℝ))} ≤
      FiniteChernoffLowerBound n ((n : ℝ)*(p : ℝ)) d := by
  classical
  let P := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let X := fun (i : Fin n) (y : Bits n) => if y i = Parent i then (0 : ℝ) else 1
  have Independent : iIndepFun X P := by
    change iIndepFun X (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
    rw [← IndependentBitMutationProductLaw]
    exact iIndepFun_pi (fun i =>
      (measurable_of_finite (fun b : Bool => if b = Parent i then (0 : ℝ) else 1)).aemeasurable)
  have InUnit (i : Fin n) : ∀ᵐ y ∂P, X i y ∈ Icc 0 1 := by
    apply ae_of_all
    intro y
    dsimp only [X]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have SumHamming (y : Bits n) : (∑ i, X i y) = (Hamming Parent y : ℝ) := by
    simp only [Hamming, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, X]
  have Bound := UnitIndependentSumFiniteChernoffLower P X
    (fun _ => (measurable_of_finite _).aemeasurable) Independent InUnit d InUnitDeviation
  simp only [SumHamming] at Bound
  change (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | (Hamming Parent y : ℝ) ≤ (1-d)*(∫ z, (Hamming Parent z : ℝ) ∂P)} ≤ _ at Bound
  have Mean : (∫ z, (Hamming Parent z : ℝ) ∂P) = (n : ℝ)*(p : ℝ) :=
    MutationHammingExpectation p Parent
  rw [Mean] at Bound
  exact Bound

/-- Standard mutation has mean one and inherits the finite-size lower bound for every deviation in [0,1]. -/
theorem StandardMutationHammingFiniteChernoffLower {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (d : ℝ) (InUnitDeviation : d ∈ Icc 0 1) :
    (StandardBitMutation PositiveLength Parent).toMeasure.real
      {y | (Hamming Parent y : ℝ) ≤ 1-d} ≤
      FiniteChernoffLowerBound n 1 d := by
  have PositiveReal : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have AtLeastOne : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨by positivity, (div_le_one PositiveReal).mpr AtLeastOne⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveReal, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  have Mean : (n : ℝ)*(p : ℝ) = 1 := by
    change (n : ℝ)*(1/(n : ℝ)) = 1
    exact mul_one_div_cancel PositiveReal.ne'
  have Bound := MutationHammingFiniteChernoffLower p Parent d InUnitDeviation
  rw [Mean, mul_one] at Bound
  unfold StandardBitMutation
  simpa only [Rate] using Bound


end
end ECTheoryLib.Analysis.BitMutation
