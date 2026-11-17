import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RuntimeLowerBounds
import Mathlib.Algebra.BigOperators.Intervals

/-! Rank potential for the original positive-linear minimizing EA.
Fin indices represent source ranks1,...,n. These are geometric facts;
the actual accepted-event drift and original-path runtime upper use these
facts in the corresponding analysis modules. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open ECTheoryLib.Problems.Linear
open scoped BigOperators
noncomputable section

def RankWeight {n : ℕ} (i : Fin n) : ℝ :=
  1+((i.val : ℝ)+1)/(n : ℝ)

def RankPotential {n : ℕ} (x : Bits n) : ℝ := Score RankWeight x

theorem RankWeightOneLe {n : ℕ} (i : Fin n) : 1 ≤ RankWeight i := by
  unfold RankWeight
  have Nonnegative : 0 ≤ ((i.val : ℝ)+1)/(n : ℝ) := div_nonneg (by positivity) (by positivity)
  linarith

theorem RankWeightPositive {n : ℕ} (i : Fin n) : 0 < RankWeight i :=
  lt_of_lt_of_le zero_lt_one (RankWeightOneLe i)

theorem RankWeightLeTwo {n : ℕ} (i : Fin n) : RankWeight i ≤ 2 := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have NumeratorLe : (i.val : ℝ)+1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have RatioLe : ((i.val : ℝ)+1)/(n : ℝ) ≤ 1 := (div_le_one PositiveN).mpr NumeratorLe
  unfold RankWeight
  linarith

theorem RankWeightMonotone (n : ℕ) : Monotone (RankWeight (n := n)) := by
  intro i j Ordered
  have Values : (i.val : ℝ) ≤ (j.val : ℝ) := Nat.cast_le.mpr (show i.val ≤ j.val from Ordered)
  change 1+((i.val : ℝ)+1)/(n : ℝ) ≤ 1+((j.val : ℝ)+1)/(n : ℝ)
  have Numerators : (i.val : ℝ)+1 ≤ (j.val : ℝ)+1 := by linarith
  have Ratios := div_le_div_of_nonneg_right Numerators (Nat.cast_nonneg n)
  linarith

theorem RankWeightDifference {n : ℕ} (i j : Fin n) :
    RankWeight i-RankWeight j = ((i.val : ℝ)-(j.val : ℝ))/(n : ℝ) := by
  unfold RankWeight
  ring

theorem OneCountLeRankPotential {n : ℕ} (x : Bits n) : (OneMax x : ℝ) ≤ RankPotential x := by
  rw [← ScoreUnitWeights x]
  unfold RankPotential Score
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp [RankWeightOneLe]

theorem RankPotentialLeTwoCount {n : ℕ} (x : Bits n) :
    RankPotential x ≤ 2*(OneMax x : ℝ) := by
  calc
    RankPotential x ≤ ∑ i : Fin n, (2 : ℝ)*(if x i then 1 else 0) := by
      unfold RankPotential Score
      apply Finset.sum_le_sum
      intro i _
      cases x i <;> simp [RankWeightLeTwo]
    _ = 2*(OneMax x : ℝ) := by
      rw [← ScoreUnitWeights x]
      simp only [Score, one_mul, Finset.mul_sum]

theorem RankPotentialNonnegative {n : ℕ} (x : Bits n) : 0 ≤ RankPotential x :=
  (Nat.cast_nonneg (OneMax x)).trans (OneCountLeRankPotential x)

theorem RankPotentialLeTwoN {n : ℕ} (x : Bits n) : RankPotential x ≤ 2*(n : ℝ) := by
  apply (RankPotentialLeTwoCount x).trans
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Problems.OneMax.OneMaxLeN x)) (by norm_num)

theorem RankPotentialZeroIff {n : ℕ} (x : Bits n) :
    RankPotential x = 0 ↔ x = fun _ => false :=
  RLSLinear.ScoreZeroIff RankWeight RankWeightPositive x

theorem RankPotentialZeroIffCount {n : ℕ} (x : Bits n) :
    RankPotential x = 0 ↔ (OneMax x : ℝ) = 0 :=
  (CountZeroIffScoreZero RankWeight RankWeightPositive x).symm

theorem RankPotentialZeroIffScore {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (x : Bits n) :
    RankPotential x = 0 ↔ Score Weights x = 0 := by
  rw [RankPotentialZeroIff, RLSLinear.ScoreZeroIff Weights Positive]

theorem RankPotentialGap {n : ℕ} (x : Bits n) :
    RankPotential x = 0 ∨ 1 ≤ RankPotential x := by
  by_cases Zero : OneMax x = 0
  · left
    apply (RankPotentialZeroIffCount x).mpr
    exact_mod_cast Zero
  · right
    have CountOne : (1 : ℝ) ≤ (OneMax x : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr Zero)
    exact CountOne.trans (OneCountLeRankPotential x)

theorem RankPotentialEmpty (x : Bits 0) : RankPotential x = 0 := by
  simp [RankPotential, Score]

def RankRange (n : ℕ) : Finset ℝ :=
  Finset.univ.image (RankPotential (n := n))

theorem RankPotentialInRange {n : ℕ} (x : Bits n) : RankPotential x ∈ RankRange n :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

theorem RankRangeZero (n : ℕ) : 0 ∈ RankRange n := by
  apply Finset.mem_image.mpr
  exact ⟨fun _ => false, Finset.mem_univ _, by simp [RankPotential, ScoreAllZeros]⟩

theorem RankRangeLower (n : ℕ) (s : ℝ) (Member : s ∈ RankRange n) : s = 0 ∨ 1 ≤ s := by
  rcases Finset.mem_image.mp Member with ⟨x, _, rfl⟩
  exact RankPotentialGap x

theorem RankRangeUpper (n : ℕ) (s : ℝ) (Member : s ∈ RankRange n) : s ≤ 2*(n : ℝ) := by
  rcases Finset.mem_image.mp Member with ⟨x, _, rfl⟩
  exact RankPotentialLeTwoN x

theorem RankPrefixWeightSum {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j < i then RankWeight j else 0) =
      (i.val : ℝ)+(i.val : ℝ)*((i.val : ℝ)+1)/(2*(n : ℝ)) := by
  have Shift : (∑ k ∈ Finset.range (i.val+1), k) = ∑ k ∈ Finset.range i.val, (k+1) := by
    rw [Finset.sum_range_succ' (fun k : ℕ => k) i.val, add_zero]
  have NatFormula : (∑ k ∈ Finset.range i.val, (k+1))*2 = i.val*(i.val+1) := by
    have Original := Finset.sum_range_id_mul_two (i.val+1)
    rw [Shift] at Original
    simpa only [Nat.add_sub_cancel, mul_comm] using Original
  have RealFormula : (∑ k ∈ Finset.range i.val, ((k : ℝ)+1))*2 =
      (i.val : ℝ)*((i.val : ℝ)+1) := by exact_mod_cast NatFormula
  have RealSum : (∑ k ∈ Finset.range i.val, ((k : ℝ)+1)) =
      (i.val : ℝ)*((i.val : ℝ)+1)/2 := by linarith
  have Filter : (Finset.range n).filter (fun k => k < i.val) = Finset.range i.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨h.trans i.isLt, h⟩⟩
  change (∑ j : Fin n, if j.val < i.val then (1 : ℝ)+((j.val : ℝ)+1)/(n : ℝ) else 0) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k < i.val then (1 : ℝ)+((k : ℝ)+1)/(n : ℝ) else 0) n,
    ← Finset.sum_filter, Filter, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, RealSum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The source's a-2 is real subtraction, including a=0/1. -/
theorem RankPrefixDriftCoefficientLower {n : ℕ} (i : Fin n) :
    1-((i.val : ℝ)-2)/(2*(n : ℝ)) ≤
      RankWeight i-(1/(n : ℝ))*(∑ j : Fin n, if j < i then RankWeight j else 0) := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have IndexBound : (i.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have ProductBound := mul_le_mul_of_nonneg_left IndexBound (Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)
  have QuotientBound : (i.val : ℝ)*((i.val : ℝ)+1)/(2*(n : ℝ)*(n : ℝ)) ≤
      (i.val : ℝ)/(2*(n : ℝ)) := by
    calc
      _ ≤ (i.val : ℝ)*(n : ℝ)/(2*(n : ℝ)*(n : ℝ)) :=
        div_le_div_of_nonneg_right ProductBound (by positivity)
      _ = _ := by
        apply (div_eq_div_iff (by positivity) (by positivity)).mpr
        ring
  have Formula : RankWeight i-(1/(n : ℝ))*(∑ j : Fin n, if j < i then RankWeight j else 0) =
      1+1/(n : ℝ)-(i.val : ℝ)*((i.val : ℝ)+1)/(2*(n : ℝ)*(n : ℝ)) := by
    rw [RankPrefixWeightSum]
    unfold RankWeight
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [Formula]
  calc
    _ = 1+1/(n : ℝ)-(i.val : ℝ)/(2*(n : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := sub_le_sub_left QuotientBound _

theorem RankPrefixDriftCoefficientPositive {n : ℕ} (i : Fin n) :
    0 < 1-((i.val : ℝ)-2)/(2*(n : ℝ)) := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have IndexBound : (i.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have Numerator : (i.val : ℝ)-2 < 2*(n : ℝ) := by linarith
  have Ratio := (div_lt_one (by positivity : (0 : ℝ) < 2*(n : ℝ))).mpr Numerator
  linarith

/-- Sum of all higher-rank distances from a fixed coordinate, including the empty suffix. -/
theorem RankSuffixDistanceSum {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if i < j then ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ) else 0) =
      ((n : ℝ)-(i.val : ℝ)-1)*((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)) := by
  classical
  let m := n-(i.val+1)
  have Decomposition : i.val+1+m = n := Nat.add_sub_of_le (Nat.succ_le_of_lt i.isLt)
  let f := fun k : ℕ => if i.val < k then ((k : ℝ)-(i.val : ℝ))/(n : ℝ) else 0
  have Prefix : (∑ k ∈ Finset.range (i.val+1), f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k Member
    have Bound := Finset.mem_range.mp Member
    exact if_neg (by omega)
  have Total : (∑ k ∈ Finset.range n, f k) =
      ∑ k ∈ Finset.range m, ((k : ℝ)+1)/(n : ℝ) := by
    calc
      _ = ∑ k ∈ Finset.range (i.val+1+m), f k := by rw [Decomposition]
      _ = _ := by
        rw [Finset.sum_range_add, Prefix, zero_add]
        apply Finset.sum_congr rfl
        intro k _
        have Above : i.val < i.val+1+k := by omega
        simp only [f, if_pos Above, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
  have Shift : (∑ k ∈ Finset.range (m+1), k) = ∑ k ∈ Finset.range m, (k+1) := by
    rw [Finset.sum_range_succ' (fun k : ℕ => k) m, add_zero]
  have NatFormula : (∑ k ∈ Finset.range m, (k+1))*2 = m*(m+1) := by
    have Original := Finset.sum_range_id_mul_two (m+1)
    rw [Shift] at Original
    simpa only [Nat.add_sub_cancel, mul_comm] using Original
  have RealFormula : (∑ k ∈ Finset.range m, ((k : ℝ)+1))*2 = (m : ℝ)*((m : ℝ)+1) := by
    exact_mod_cast NatFormula
  have RealSum : (∑ k ∈ Finset.range m, ((k : ℝ)+1)) = (m : ℝ)*((m : ℝ)+1)/2 := by
    linarith
  have RealM : (m : ℝ) = (n : ℝ)-(i.val : ℝ)-1 := by
    have CastDecomposition : (i.val : ℝ)+1+(m : ℝ) = (n : ℝ) := by exact_mod_cast Decomposition
    linarith
  change (∑ j : Fin n, f j.val) = _
  rw [Fin.sum_univ_eq_sum_range f n, Total]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, RealSum, RealM]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Pessimistic suffix cost after dividing the two-flip mass by the one-flip mass. -/
theorem RankSuffixSwapCostBound {n : ℕ} (AtLeastTwo : 2 ≤ n) (i : Fin n) :
    (∑ j : Fin n, if i < j then ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ) else 0)/((n : ℝ)-1) ≤
      ((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)) := by
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have NMinusPositive : (0 : ℝ) < (n : ℝ)-1 := by
    have RealAtLeastTwo : (2 : ℝ) ≤ n := Nat.cast_le.mpr AtLeastTwo
    linarith
  have IndexBound : (i.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have Ratio : ((n : ℝ)-(i.val : ℝ)-1)/((n : ℝ)-1) ≤ 1 :=
    (div_le_one NMinusPositive).mpr (by linarith [(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)])
  have Nonnegative : 0 ≤ ((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  rw [RankSuffixDistanceSum]
  calc
    _ = (((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)))*
        (((n : ℝ)-(i.val : ℝ)-1)/((n : ℝ)-1)) := by ring
    _ ≤ (((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)))*1 :=
      mul_le_mul_of_nonneg_left Ratio Nonnegative
    _ = _ := mul_one _

end
end ECTheoryLib.Analysis.EALinearMinimization

