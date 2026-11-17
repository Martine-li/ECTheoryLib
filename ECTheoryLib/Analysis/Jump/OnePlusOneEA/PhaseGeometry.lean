import ECTheoryLib.Problems.Jump
import ECTheoryLib.Analysis.OneMax.BitFlip
import ECTheoryLib.Problems.Comparison
import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Tools.Runtime.Harmonic
import ECTheoryLib.Probability.PMF.FinitePMF

/-!
# Fitness geometry for the (1+1) EA on Jump

For 1 ≤ k ≤ n, the second-phase region consists of the local-optimum plateau
of weight n-k and the global optimum. The first-phase level is the fitness
deficit below n. It decreases under the actual elitist update, including ties.
Outside the region, at least as many coordinates as this deficit strictly
improve the level. The resulting harmonic certificate handles both sides of
the fitness valley without assuming initialization below the plateau.
-/
namespace ECTheoryLib.Analysis.EAJump
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
noncomputable section

/-- The actual maximizing Jump update, accepting fitness ties. -/
abbrev Update {n : ℕ} (k : ℕ) (x y : Bits n) : Bits n :=
  ElitistSelect (Problems.MaxNotWorse (Jump k)) x y

/-- Actual independent-bit (1+1) EA kernel, with mutation rate 1/n. -/
def Step {n : ℕ} (hn : 0 < n) (k : ℕ) : Transition (Bits n) :=
  OnePlusOneEAStep hn (Problems.MaxNotWorse (Jump k))

/-- States at the local-optimum fitness threshold or above. For 1 ≤ k ≤ n,
these are exactly the plateau and the global optimum. -/
def Region {n : ℕ} (k : ℕ) (x : Bits n) : Prop := n ≤ Jump k x

/-- Fitness deficit before the plateau, truncated to zero in the second phase. -/
def Level {n : ℕ} (k : ℕ) (x : Bits n) : ℕ := n - Jump k x

/-- The phase boundary has the intended geometric meaning, including k=n. -/
theorem RegionIff {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (x : Bits n) :
    Region k x ↔ OneMax x = n - k ∨ x = AllOnes n := by
  have Bound := Problems.OneMax.OneMaxLeN x
  rw [← Problems.OneMax.OneMaxEqNIffEqAllOnes]
  unfold Region Jump JumpValue
  split_ifs <;> omega

/-- Zero first-phase level means entry into the region, not final optimization. -/
theorem LevelZeroIff {n : ℕ} (k : ℕ) (x : Bits n) : Level k x = 0 ↔ Region k x := by
  exact Nat.sub_eq_zero_iff_le

/-- Elitism preserves or increases the actual Jump fitness. -/
theorem UpdateFitness {n : ℕ} (k : ℕ) (x y : Bits n) :
    Jump k x ≤ Jump k (Update k x y) := by
  unfold Update ElitistSelect Problems.MaxNotWorse
  split_ifs with Accepted
  · exact Accepted
  · exact le_rfl

/-- The first-phase level is nonincreasing for every candidate, not just for
the elementary one-bit events used in the progress estimate. -/
theorem UpdateLevel {n : ℕ} (k : ℕ) (x y : Bits n) :
    Level k (Update k x y) ≤ Level k x := by
  exact Nat.sub_le_sub_left (UpdateFitness k x y) n

/-- Once the plateau or optimum has been reached, elitism keeps the process
in that region even if a later accepted offspring changes its Hamming weight. -/
theorem UpdateRegion {n : ℕ} (k : ℕ) (x y : Bits n) (Inside : Region k x) :
    Region k (Update k x y) := Inside.trans (UpdateFitness k x y)

/-- The unique global optimum is absorbing under elitist Jump selection. -/
theorem UpdateGoal {n : ℕ} (k : ℕ) (x y : Bits n) (AtGoal : x = AllOnes n) :
    Update k x y = AllOnes n := by
  subst x
  apply (Problems.Jump.JumpEqMaxIffEqAllOnes _).mp
  have Nondecrease := UpdateFitness k (AllOnes n) y
  rw [Problems.Jump.JumpAllOnes] at Nondecrease
  exact le_antisymm (Problems.Jump.JumpLeMax _) Nondecrease

/-- Coordinates pointing towards the plateau: flip a zero on the increasing
side, or a one while inside the fitness valley. -/
def GoodCoordinate {n : ℕ} (k : ℕ) (x : Bits n) (i : Fin n) : Prop :=
  if OneMax x ≤ n - k then x i = false else x i = true

instance {n : ℕ} (k : ℕ) (x : Bits n) : DecidablePred (GoodCoordinate k x) := by
  intro i
  unfold GoodCoordinate
  infer_instance

/-- Every designated coordinate strictly lowers the first-phase level outside
the region. At the valley boundary the improvement may be larger than one. -/
theorem GoodCoordinateProgress {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Bits n) (Outside : ¬ Region k x) (i : Fin n) (Good : GoodCoordinate k x i) :
    Level k (Update k x (OnebitMutation x i)) < Level k x := by
  have WeightBound := Problems.OneMax.OneMaxLeN x
  have ChildBound := Problems.OneMax.OneMaxLeN (OnebitMutation x i)
  have FitnessBelow : Jump k x < n := Nat.lt_of_not_ge Outside
  have Better : Jump k x < Jump k (OnebitMutation x i) := by
    by_cases Low : OneMax x ≤ n - k
    · have Bit : x i = false := by simpa only [GoodCoordinate, if_pos Low] using Good
      have Changed := OneMax.OneMaxMutationAtZero x i Bit
      unfold Jump JumpValue at FitnessBelow ⊢
      rw [if_pos (Or.inl Low)] at FitnessBelow ⊢
      have ChildLow : OneMax (OnebitMutation x i) ≤ n - k := by omega
      rw [if_pos (Or.inl ChildLow)]
      omega
    · have Bit : x i = true := by simpa only [GoodCoordinate, if_neg Low] using Good
      have Changed := OneMax.OneMaxMutationAtOne x i Bit
      have NotOpt : OneMax x ≠ n := by
        intro Equal
        have Fitness : Jump k x = n + k := by
          unfold Jump
          rw [Equal, Problems.Jump.JumpValueAtN]
        omega
      unfold Jump JumpValue
      rw [if_neg (not_or.mpr ⟨Low, NotOpt⟩)]
      split_ifs <;> omega
  have Accepted : Update k x (OnebitMutation x i) = OnebitMutation x i := by
    exact ElitistSelectAccept _ _ _ Better.le
  rw [Accepted]
  unfold Level
  omega

/-- There are at least Level(x) useful coordinates. The count changes from
zeros to ones across the valley, which is why the full state is retained. -/
theorem GoodCoordinateCount {n k : ℕ} (x : Bits n) (Outside : ¬ Region k x) :
    Level k x ≤ (Finset.univ.filter (GoodCoordinate k x)).card := by
  classical
  have Below : Jump k x < n := Nat.lt_of_not_ge Outside
  by_cases Low : OneMax x ≤ n - k
  · have Count : (Finset.univ.filter (fun i => x i = false)).card = n - OneMax x := by
      rw [← Problems.OneMax.ZeroBitCount x, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      cases x i <;> rfl
    have GoodEq : GoodCoordinate k x = (fun i => x i = false) := by
      funext i
      exact if_pos Low
    simp only [GoodEq]
    rw [Count]
    unfold Level Jump JumpValue
    rw [if_pos (Or.inl Low)]
    omega
  · have NotOpt : OneMax x ≠ n := by
      intro Equal
      have Fitness : Jump k x = n + k := by
        unfold Jump
        rw [Equal, Problems.Jump.JumpValueAtN]
      omega
    have Count : (Finset.univ.filter (fun i => x i = true)).card = OneMax x := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rfl
    have GoodEq : GoodCoordinate k x = (fun i => x i = true) := by
      funext i
      exact if_neg Low
    simp only [GoodEq]
    rw [Count]
    unfold Level Jump JumpValue
    rw [if_neg (not_or.mpr ⟨Low, NotOpt⟩)]
    omega

/-- Summing harmonic progress over the n distinct one-bit offspring gives at
least one before region entry. Other possible offspring remain nonnegative. -/
theorem HarmonicOneBitProgress {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (x : Bits n) (Outside : ¬ Region k x) :
    1 ≤ ∑ i : Fin n, ((harmonic (Level k x) : ℝ) -
      (harmonic (Level k (Update k x (OnebitMutation x i))) : ℝ)) := by
  classical
  exact HarmonicProgressCount _ _ (GoodCoordinate k x)
    (Nat.pos_of_ne_zero (fun Zero => Outside ((LevelZeroIff k x).mp Zero)))
    (fun i => UpdateLevel k x (OnebitMutation x i))
    (GoodCoordinateProgress hk hkn x Outside) (GoodCoordinateCount x Outside)

end
end ECTheoryLib.Analysis.EAJump
