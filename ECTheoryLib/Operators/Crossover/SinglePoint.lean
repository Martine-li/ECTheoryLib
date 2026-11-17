import ECTheoryLib.SearchSpaces.BitString
import ECTheoryLib.Probability.PMF.FinitePMF
import Mathlib.Probability.Distributions.Uniform

namespace ECTheoryLib

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- True takes the first parent's prefix; false reverses the parents.
The cut ranges over all n+1 positions, including both endpoints. -/
def SinglePointChild {n : Nat} (Parent Other : Bits n)
    (Cut : Fin (n + 1)) (Orientation : Bool) : Bits n :=
  fun i => if Orientation then
    (if i.val < Cut.val then Parent i else Other i)
  else (if i.val < Cut.val then Other i else Parent i)

/-- The full joint law of the uniform cut and independent fair orientation. -/
def SinglePointChoice (n : Nat) : PMF (Fin (n + 1) × Bool) :=
  PMF.uniformOfFintype _

/-- Actual 1-point crossover, accumulating all sample pairs with the same offspring. -/
def SinglePointCrossover {n : Nat} (Parent Other : Bits n) : PMF (Bits n) :=
  (SinglePointChoice n).map (fun Choice => SinglePointChild Parent Other Choice.1 Choice.2)

/-- Every cut/orientation pair has the same mass, also at n = 0. -/
theorem SinglePointChoiceProbability (n : Nat) (Choice : Fin (n + 1) × Bool) :
    SinglePointChoice n Choice = (((2 * (n + 1) : Nat) : ENNReal))⁻¹ := by
  simp [SinglePointChoice, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.mul_comm]

/-- The exact offspring law sums the two orientations at every cut. -/
theorem SinglePointProbability {n : Nat} (Parent Other Candidate : Bits n) :
    SinglePointCrossover Parent Other Candidate =
      ∑ Cut : Fin (n + 1),
        ((if Candidate = SinglePointChild Parent Other Cut true then
          (((2 * (n + 1) : Nat) : ENNReal))⁻¹ else 0) +
         (if Candidate = SinglePointChild Parent Other Cut false then
          (((2 * (n + 1) : Nat) : ENNReal))⁻¹ else 0)) := by
  classical
  rw [SinglePointCrossover, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, SinglePointChoiceProbability]

/-- The whole distribution is unchanged when the unordered parents are swapped. -/
theorem SinglePointParentOrder {n : Nat} (Parent Other : Bits n) :
    SinglePointCrossover Parent Other = SinglePointCrossover Other Parent := by
  apply PMF.ext
  intro Candidate
  rw [SinglePointProbability, SinglePointProbability]
  apply Finset.sum_congr rfl
  intro Cut _
  have Forward : SinglePointChild Other Parent Cut true =
      SinglePointChild Parent Other Cut false := rfl
  have Reverse : SinglePointChild Other Parent Cut false =
      SinglePointChild Parent Other Cut true := rfl
  rw [Forward, Reverse, add_comm]

/-- Identical parents produce the same string with certainty. -/
theorem SinglePointIdenticalParents {n : Nat} (Parent : Bits n) :
    SinglePointCrossover Parent Parent = PMF.pure Parent := by
  have Same (Choice : Fin (n + 1) × Bool) :
      SinglePointChild Parent Parent Choice.1 Choice.2 = Parent := by
    funext i
    simp [SinglePointChild]
  unfold SinglePointCrossover
  simp_rw [Same]
  exact PMF.map_const _ _

/-- A coordinate statistic has the mean parental value; coordinate independence is unnecessary. -/
theorem SinglePointCoordinateIntegral {n : Nat} (Parent Other : Bits n)
    (i : Fin n) (f : Bool → ℝ) :
    (∫ Candidate, f (Candidate i) ∂(SinglePointCrossover Parent Other).toMeasure) =
      (f (Parent i) + f (Other i)) / 2 := by
  have Pair (Cut : Fin (n + 1)) :
      f (SinglePointChild Parent Other Cut true i) +
        f (SinglePointChild Parent Other Cut false i) = f (Parent i) + f (Other i) := by
    by_cases Left : i.val < Cut.val <;> simp [SinglePointChild, Left, add_comm]
  rw [SinglePointCrossover, PMFIntegralMap, PMF.integral_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, SinglePointChoiceProbability, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← mul_add, Pair]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  have Nonzero : ((n + 1 : Nat) : ℝ) ≠ 0 := by positivity
  field_simp

end
end ECTheoryLib

