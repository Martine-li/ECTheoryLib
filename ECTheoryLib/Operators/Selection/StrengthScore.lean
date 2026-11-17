import ECTheoryLib.Operators.Selection.Strength
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Why exact squared-distance comparisons implement SPEA2 fitness ordering

The original SPEA2 score is `RawFitness + 1 / (sigma_k + 2)`. Raw fitness is an
integer, while density lies in `(0, 1/2]`; distinct raw scores therefore determine
the ordering. At equal raw scores, larger squared distance gives smaller density.
These statements justify the rational comparator used by `Strength.lean`.

Source: Zitzler, Laumanns and Thiele, TIK Report 103 (2001). The author's official
PISA documentation explicitly distinguishes paper `k = sqrt(M)` from code `k = 1`:
https://sop.tik.ee.ethz.ch/pisa/selectors/spea2/spea2_documentation.txt .
-/

namespace ECTheoryLib.Operators.Selection

noncomputable section

/-- The real density term 1/(sqrt(SquaredDistance)+2). Objective squared distances are nonnegative; the total function uses Lean's real square root on all inputs. -/
def SPEA2Density (SquaredDistance : ℚ) : ℝ :=
  1 / (Real.sqrt (SquaredDistance : ℝ) + 2)

/-- Integer raw fitness plus the real density contribution; the ordering bridge relates this numerical score to the exact rational comparison. -/
def SPEA2RealFitness (Raw : Nat) (SquaredDistance : ℚ) : ℝ :=
  (Raw : ℝ) + SPEA2Density SquaredDistance

theorem SPEA2DensityBounds (SquaredDistance : ℚ) :
    0 < SPEA2Density SquaredDistance ∧ SPEA2Density SquaredDistance ≤ 1 / 2 := by
  have RootNonnegative : 0 ≤ Real.sqrt (SquaredDistance : ℝ) := Real.sqrt_nonneg _
  have DenominatorPositive : 0 < Real.sqrt (SquaredDistance : ℝ) + 2 := by
    linarith
  constructor
  · exact one_div_pos.mpr DenominatorPositive
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    linarith

theorem SPEA2DensityOrdering (DistanceX DistanceY : ℚ)
    (NonnegativeX : 0 ≤ DistanceX) (_NonnegativeY : 0 ≤ DistanceY) :
    SPEA2Density DistanceX ≤ SPEA2Density DistanceY ↔ DistanceY ≤ DistanceX := by
  have DenominatorXPositive : 0 < Real.sqrt (DistanceX : ℝ) + 2 := by
    have := Real.sqrt_nonneg (DistanceX : ℝ)
    linarith
  have DenominatorYPositive : 0 < Real.sqrt (DistanceY : ℝ) + 2 := by
    have := Real.sqrt_nonneg (DistanceY : ℝ)
    linarith
  have RealNonnegativeX : 0 ≤ (DistanceX : ℝ) := by exact_mod_cast NonnegativeX
  unfold SPEA2Density
  rw [one_div_le_one_div DenominatorXPositive DenominatorYPositive]
  rw [add_le_add_iff_right]
  rw [Real.sqrt_le_sqrt_iff RealNonnegativeX]
  norm_cast

theorem SPEA2RawLessGivesSmallerScore (RawX RawY : Nat) (DistanceX DistanceY : ℚ)
    (RawLess : RawX < RawY) :
    SPEA2RealFitness RawX DistanceX < SPEA2RealFitness RawY DistanceY := by
  have IntegerGap : (RawX : ℝ) + 1 ≤ (RawY : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt RawLess
  have DensityXUpper := (SPEA2DensityBounds DistanceX).2
  have DensityYPositive := (SPEA2DensityBounds DistanceY).1
  unfold SPEA2RealFitness
  linarith

/-- The full real-valued fitness order equals the raw-first / distance-descending order. -/
theorem SPEA2RealFitnessOrdering (RawX RawY : Nat) (DistanceX DistanceY : ℚ)
    (NonnegativeX : 0 ≤ DistanceX) (NonnegativeY : 0 ≤ DistanceY) :
    SPEA2RealFitness RawX DistanceX ≤ SPEA2RealFitness RawY DistanceY ↔
      RawX < RawY ∨ (RawX = RawY ∧ DistanceY ≤ DistanceX) := by
  constructor
  · intro ScoreLE
    by_cases EqualRaw : RawX = RawY
    · right
      refine ⟨EqualRaw, ?_⟩
      have DensityLE : SPEA2Density DistanceX ≤ SPEA2Density DistanceY := by
        unfold SPEA2RealFitness at ScoreLE
        rw [EqualRaw] at ScoreLE
        exact (add_le_add_iff_left (RawY : ℝ)).mp ScoreLE
      exact (SPEA2DensityOrdering DistanceX DistanceY NonnegativeX NonnegativeY).mp DensityLE
    · left
      by_contra NotRawLess
      have ReverseRawLess : RawY < RawX := by omega
      have ReverseScoreLess := SPEA2RawLessGivesSmallerScore RawY RawX
        DistanceY DistanceX ReverseRawLess
      exact (not_le_of_gt ReverseScoreLess) ScoreLE
  · intro ExactOrder
    rcases ExactOrder with RawLess | EqualAndDistance
    · exact le_of_lt (SPEA2RawLessGivesSmallerScore RawX RawY DistanceX DistanceY RawLess)
    · have DensityLE := (SPEA2DensityOrdering DistanceX DistanceY NonnegativeX NonnegativeY).mpr
        EqualAndDistance.2
      unfold SPEA2RealFitness
      rw [EqualAndDistance.1]
      exact add_le_add (le_refl (RawY : ℝ)) DensityLE

theorem SquaredObjectiveDistanceNonnegative {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (x y : α) : 0 ≤ SquaredObjectiveDistance Fitness x y := by
  unfold SquaredObjectiveDistance
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

theorem KthSquaredDistanceAtNonnegative {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (NeighborIndex : Nat) (x : α) :
    0 ≤ KthSquaredDistanceAt Fitness Pool NeighborIndex x := by
  let Sorted := (Pool.map (SquaredObjectiveDistance Fitness x)).mergeSort
    (fun a b => decide (a ≤ b))
  by_cases HasNeighbor : NeighborIndex < Sorted.length
  · change 0 ≤ Sorted.getD NeighborIndex 0
    rw [List.getD_eq_getElem Sorted 0 HasNeighbor]
    have InSorted : Sorted[NeighborIndex] ∈ Sorted := List.getElem_mem HasNeighbor
    have InMapped : Sorted[NeighborIndex] ∈ Pool.map (SquaredObjectiveDistance Fitness x) :=
      List.mem_mergeSort.mp InSorted
    obtain ⟨y, _yMem, ValueEquals⟩ := List.mem_map.mp InMapped
    rw [← ValueEquals]
    exact SquaredObjectiveDistanceNonnegative Fitness x y
  · change 0 ≤ Sorted.getD NeighborIndex 0
    rw [List.getD_eq_default Sorted 0 (Nat.le_of_not_gt HasNeighbor)]

theorem KthSquaredDistanceNonnegative {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) :
    0 ≤ KthSquaredDistance Fitness Pool x := by
  exact KthSquaredDistanceAtNonnegative Fitness Pool (Nat.sqrt Pool.length) x

/-- Shared conversion from an exact Boolean integer/distance comparator to the real score. -/
theorem SPEA2IntegerDistanceComparatorCorrect (RawX RawY : Nat) (DistanceX DistanceY : ℚ)
    (NonnegativeX : 0 ≤ DistanceX) (NonnegativeY : 0 ≤ DistanceY) :
    (if RawX ≠ RawY then decide (RawX ≤ RawY) else decide (DistanceY ≤ DistanceX)) = true ↔
      SPEA2RealFitness RawX DistanceX ≤ SPEA2RealFitness RawY DistanceY := by
  rw [SPEA2RealFitnessOrdering RawX RawY DistanceX DistanceY NonnegativeX NonnegativeY]
  by_cases EqualRaw : RawX = RawY
  · rw [if_neg (not_not.mpr EqualRaw)]
    rw [decide_eq_true_eq]
    constructor
    · intro DistanceLE
      exact Or.inr ⟨EqualRaw, DistanceLE⟩
    · intro Order
      rcases Order with RawLess | EqualAndDistance
      · exact False.elim ((Nat.ne_of_lt RawLess) EqualRaw)
      · exact EqualAndDistance.2
  · rw [if_pos EqualRaw, decide_eq_true_eq]
    constructor
    · intro RawLE
      exact Or.inl (lt_of_le_of_ne RawLE EqualRaw)
    · intro Order
      rcases Order with RawLess | EqualAndDistance
      · exact Nat.le_of_lt RawLess
      · exact False.elim (EqualRaw EqualAndDistance.1)

/-- The executable Boolean comparator is faithful to the original real score. -/
theorem SPEA2FitnessBetterCorrect {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x y : α) :
    SPEA2FitnessBetter Fitness Pool x y = true ↔
      SPEA2RealFitness (RawFitness Fitness Pool x) (KthSquaredDistance Fitness Pool x) ≤
        SPEA2RealFitness (RawFitness Fitness Pool y) (KthSquaredDistance Fitness Pool y) := by
  exact SPEA2IntegerDistanceComparatorCorrect _ _ _ _
    (KthSquaredDistanceNonnegative Fitness Pool x) (KthSquaredDistanceNonnegative Fitness Pool y)

/-- Explicit configured neighbor indices use the same original SPEA2 score ordering. -/
theorem SPEA2FitnessBetterAtCorrect {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (NeighborIndex : Nat) (x y : α) :
    SPEA2FitnessBetterAt Fitness Pool NeighborIndex x y = true ↔
      SPEA2RealFitness (RawFitness Fitness Pool x) (KthSquaredDistanceAt Fitness Pool NeighborIndex x) ≤
        SPEA2RealFitness (RawFitness Fitness Pool y)
          (KthSquaredDistanceAt Fitness Pool NeighborIndex y) := by
  exact SPEA2IntegerDistanceComparatorCorrect _ _ _ _
    (KthSquaredDistanceAtNonnegative Fitness Pool NeighborIndex x)
    (KthSquaredDistanceAtNonnegative Fitness Pool NeighborIndex y)

/-- In-pool raw score zero is equivalent to being nondominated in the pool. -/
theorem RawFitnessZeroIffNondominated {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : Fin Pool.length) :
    RawFitness Fitness Pool Pool[x] = 0 ↔
      ∀ j : Fin Pool.length, ¬ StrictlyDominates Fitness Pool[j] Pool[x] := by
  constructor
  · intro RawZero j Dominated
    have RawPositive := RawFitnessPositiveOfDominated Fitness Pool x j Dominated
    rw [RawZero] at RawPositive
    exact (Nat.lt_irrefl 0) RawPositive
  · exact RawFitnessOfNondominated Fitness Pool Pool[x]

end
end ECTheoryLib.Operators.Selection
