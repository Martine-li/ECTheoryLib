import ECTheoryLib.Analysis.OneMax.BitFlip
import ECTheoryLib.Operators.Selection.Elitist
import ECTheoryLib.Problems.Comparison
import Mathlib.Tactic.Ring

/-!
# OneMax under elitist single-bit selection

These deterministic facts combine OneMax with mutation and selection operators.
They impose no coordinate-selection policy and are independent of RLS proofs.
-/
namespace ECTheoryLib.Analysis.OneMax

/-- Real zero count for signed potential differences. -/
abbrev ZeroPotential {n : Nat} (x : Bits n) : ℝ := (Problems.OneMax.ZeroCount x : ℝ)

/-- Propose a specified bit flip and accept it if OneMax does not decrease. -/
def ElitistBitFlip {n : Nat} (x : Bits n) (i : Fin n) : Bits n :=
  ElitistSelect (Problems.MaxNotWorse OneMax) x (OnebitMutation x i)

/-- OneMax-maximizing elitist selection accepts a zero-to-one flip. -/
theorem ElitistAcceptsZeroFlip {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsZero : x i = false) :
    ElitistBitFlip x i = OnebitMutation x i := by
  have ScoreIncreases : OneMax (OnebitMutation x i) = OneMax x + 1 := by
    exact OneMaxMutationAtZero x i BitIsZero
  have Accept : OneMax x ≤ OneMax (OnebitMutation x i) := by
    rw [ScoreIncreases]
    exact Nat.le_add_right (OneMax x) 1
  unfold ElitistBitFlip ElitistSelect Problems.MaxNotWorse
  rw [if_pos Accept]

/-- OneMax-maximizing elitist selection rejects a one-to-zero flip. -/
theorem ElitistRejectsOneFlip {n : Nat}
    (x : Bits n) (i : Fin n) (BitIsOne : x i = true) :
    ElitistBitFlip x i = x := by
  have ScoreDecreases : OneMax (OnebitMutation x i) + 1 = OneMax x := by
    exact OneMaxMutationAtOne x i BitIsOne
  have Reject : ¬ OneMax x ≤ OneMax (OnebitMutation x i) := by
    omega
  unfold ElitistBitFlip ElitistSelect Problems.MaxNotWorse
  rw [if_neg Reject]

/-- Each deterministic elitist update preserves zero potential. -/
theorem ElitistBitFlipPreservesZero {n : Nat} (x : Bits n) (i : Fin n)
    (ParentZero : ZeroPotential x = 0) :
    ZeroPotential (ElitistBitFlip x i) = 0 := by
  unfold ElitistBitFlip ElitistSelect Problems.MaxNotWorse
  by_cases Accept : OneMax x ≤ OneMax (OnebitMutation x i)
  · rw [if_pos Accept]
    unfold ZeroPotential Problems.OneMax.ZeroCount at ParentZero ⊢
    apply Nat.cast_eq_zero.mpr
    apply Nat.sub_eq_zero_of_le
    have ParentAtLeastN : n ≤ OneMax x := by
      apply Nat.le_of_sub_eq_zero
      exact Nat.cast_eq_zero.mp ParentZero
    exact Nat.le_trans ParentAtLeastN Accept
  · rw [if_neg Accept]
    exact ParentZero

/-- A complete update decreases potential by one for a zero coordinate
and by zero for a one coordinate. -/
theorem ElitistBitFlipDecrease {n : Nat} (x : Bits n) (i : Fin n) :
    ZeroPotential x - ZeroPotential (ElitistBitFlip x i) =
      if x i then 0 else 1 := by
  cases BitValue : x i with
  | false =>
      rw [ElitistAcceptsZeroFlip x i BitValue]
      unfold ZeroPotential
      rw [Problems.OneMax.ZeroCountAsRealDifference, Problems.OneMax.ZeroCountAsRealDifference]
      rw [OneMaxMutationAtZero x i BitValue, Nat.cast_add, Nat.cast_one]
      change (n : ℝ) - (OneMax x : ℝ) -
        ((n : ℝ) - ((OneMax x : ℝ) + 1)) = 1
      ring
  | true =>
      rw [ElitistRejectsOneFlip x i BitValue]
      rw [sub_self]
      rfl

end ECTheoryLib.Analysis.OneMax
