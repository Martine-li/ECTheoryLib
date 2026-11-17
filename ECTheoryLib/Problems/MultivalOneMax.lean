import ECTheoryLib.SearchSpaces.MultiValue
import ECTheoryLib.Problems.Comparison
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Interval-distance OneMax over a finite alphabet

The objective minimized by the algorithm is the sum of interval distances.
Hamming counts incorrect coordinates only; it is a potential, not the fitness.
Both functions have the prescribed target as their unique zero.
-/

namespace ECTheoryLib.Problems.MultivalOneMax

/-- The paper's interval-distance objective, minimized by the real algorithm. -/
def Distance {n r : Nat} (Target State : MultiValues n r) : Nat :=
  ∑ i : Fin n, Nat.dist (State i).val (Target i).val

/-- The potential counts coordinates which disagree with the target. -/
def Hamming {n r : Nat} (Target State : MultiValues n r) : Nat :=
  ∑ i : Fin n, if State i = Target i then 0 else 1

theorem HammingEqZeroIffEq {n r : Nat} (Target State : MultiValues n r) :
    Hamming Target State = 0 ↔ State = Target := by
  constructor
  · intro CountZero
    have ContributionsZero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (if State i = Target i then 0 else 1 : Nat) = 0 := by
      apply Finset.sum_eq_zero_iff.mp
      exact CountZero
    funext i
    have ContributionZero := ContributionsZero i (Finset.mem_univ i)
    by_contra Disagreement
    rw [if_neg Disagreement] at ContributionZero
    exact Nat.one_ne_zero ContributionZero
  · intro StateEqualsTarget
    subst State
    unfold Hamming
    simp only [if_true, Finset.sum_const_zero]

theorem DistanceEqZeroIffEq {n r : Nat} (Target State : MultiValues n r) :
    Distance Target State = 0 ↔ State = Target := by
  constructor
  · intro DistanceZero
    have ContributionsZero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Nat.dist (State i).val (Target i).val = 0 := by
      apply Finset.sum_eq_zero_iff.mp
      exact DistanceZero
    funext i
    apply Fin.ext
    exact Nat.eq_of_dist_eq_zero (ContributionsZero i (Finset.mem_univ i))
  · intro StateEqualsTarget
    subst State
    unfold Distance
    simp only [Nat.dist_self, Finset.sum_const_zero]

theorem DistanceEqZeroIffHammingEqZero {n r : Nat}
    (Target State : MultiValues n r) :
    Distance Target State = 0 ↔ Hamming Target State = 0 := by
  rw [DistanceEqZeroIffEq, HammingEqZeroIffEq]

theorem HammingLeLength {n r : Nat} (Target State : MultiValues n r) :
    Hamming Target State ≤ n := by
  unfold Hamming
  have EachAtMostOne : ∀ i : Fin n,
      (if State i = Target i then 0 else 1 : Nat) ≤ 1 := by
    intro i
    split
    · exact Nat.zero_le 1
    · exact Nat.le_refl 1
  have SumBound := Finset.sum_le_sum (fun i (_Membership : i ∈ Finset.univ) =>
    EachAtMostOne i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, Nat.mul_one] using SumBound

/-- A coordinate replacement leaves every other contribution unchanged. -/
private theorem CoordinateSumUpdateBalance {n r : Nat}
    (Contribution : Fin n → Fin r → Nat) (State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    (∑ j : Fin n, Contribution j (Function.update State i v j)) + Contribution i (State i) =
      (∑ j : Fin n, Contribution j (State j)) + Contribution i v := by
  classical
  let Rest := ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, Contribution j (State j)
  have ParentDecomposition :
      (∑ j : Fin n, Contribution j (State j)) = Rest + Contribution i (State i) := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have UpdatedRest :
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        Contribution j (Function.update State i v j)) = Rest := by
    apply Finset.sum_congr rfl
    intro j InRest
    have DifferentPosition : j ≠ i := (Finset.mem_erase.mp InRest).1
    rw [Function.update_of_ne DifferentPosition]
  have UpdatedDecomposition :
      (∑ j : Fin n, Contribution j (Function.update State i v j)) =
        Rest + Contribution i v := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [UpdatedRest, Function.update_self]
  rw [ParentDecomposition, UpdatedDecomposition]
  omega

/-- The exact fitness balance for one candidate-coordinate replacement. -/
theorem DistanceUpdate {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    Distance Target (Function.update State i v) + Nat.dist (State i).val (Target i).val =
      Distance Target State + Nat.dist v.val (Target i).val := by
  exact CoordinateSumUpdateBalance (fun j w => Nat.dist w.val (Target j).val) State i v

/-- Selecting an interval-distance candidate reduces to the changed coordinate. -/
theorem DistanceUpdateComparison {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    MinNotWorse (Distance Target) (Function.update State i v) State ↔
      Nat.dist v.val (Target i).val ≤ Nat.dist (State i).val (Target i).val := by
  unfold MinNotWorse
  have Balance := DistanceUpdate Target State i v
  omega

/-- The Hamming balance applies to a candidate before selection. -/
theorem HammingUpdate {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    Hamming Target (Function.update State i v) +
        (if State i = Target i then 0 else 1) =
      Hamming Target State + (if v = Target i then 0 else 1) := by
  exact CoordinateSumUpdateBalance
    (fun j w => if w = Target j then 0 else 1) State i v

end ECTheoryLib.Problems.MultivalOneMax
