import ECTheoryLib.Algorithms.MultivalRLS
import ECTheoryLib.Problems.MultivalOneMax
import Mathlib.Tactic.Linarith

/-!
# Deterministic Hamming changes for interval-distance RLS

Selection uses the paper's interval-distance objective.  The Hamming count is
only a potential.  Correct coordinates cannot become incorrect after selection;
an incorrect coordinate is repaired precisely when its target value is proposed.
-/

namespace ECTheoryLib.Analysis.RLSMultival

open ECTheoryLib.Problems.MultivalOneMax

/-- The existing actual update, with interval-distance minimization as fitness. -/
abbrev Update {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) : MultiValues n r :=
  MultivalRLSUpdate (Problems.MinNotWorse (Distance Target)) State i v

/-- Proposing the target value is always accepted under interval-distance fitness. -/
theorem UpdateAcceptsTarget {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) :
    Update Target State i (Target i) = Function.update State i (Target i) := by
  have Acceptable : Problems.MinNotWorse (Distance Target)
      (Function.update State i (Target i)) State := by
    apply (DistanceUpdateComparison Target State i (Target i)).mpr
    rw [Nat.dist_self]
    exact Nat.zero_le _
  unfold Update
  exact MultivalRLSUpdateAccept _ _ _ _ Acceptable

/-- Exact natural-number count balance for the actual mutation and selection. -/
theorem HammingUpdateDecrease {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    Hamming Target (Update Target State i v) +
        (if State i ≠ Target i ∧ v = Target i then 1 else 0) =
      Hamming Target State := by
  by_cases Acceptable : Problems.MinNotWorse (Distance Target)
      (Function.update State i v) State
  · have UpdateIsCandidate : Update Target State i v = Function.update State i v := by
      unfold Update
      exact MultivalRLSUpdateAccept _ _ _ _ Acceptable
    rw [UpdateIsCandidate]
    have CountBalance := HammingUpdate Target State i v
    by_cases CurrentCorrect : State i = Target i
    · have LocalDistanceComparison :=
        (DistanceUpdateComparison Target State i v).mp Acceptable
      rw [CurrentCorrect, Nat.dist_self] at LocalDistanceComparison
      have NewDistanceZero : Nat.dist v.val (Target i).val = 0 := by
        exact Nat.eq_zero_of_le_zero LocalDistanceComparison
      have NewCorrect : v = Target i := by
        apply Fin.ext
        exact Nat.eq_of_dist_eq_zero NewDistanceZero
      rw [if_pos CurrentCorrect, if_pos NewCorrect] at CountBalance
      rw [if_neg (fun Repair => Repair.1 CurrentCorrect)]
      omega
    · by_cases NewCorrect : v = Target i
      · rw [if_neg CurrentCorrect, if_pos NewCorrect] at CountBalance
        rw [if_pos ⟨CurrentCorrect, NewCorrect⟩]
        omega
      · rw [if_neg CurrentCorrect, if_neg NewCorrect] at CountBalance
        rw [if_neg (fun Repair => NewCorrect Repair.2)]
        omega
  · have UpdateIsParent : Update Target State i v = State := by
      unfold Update
      exact MultivalRLSUpdateReject _ _ _ _ Acceptable
    have NoRepair : ¬ (State i ≠ Target i ∧ v = Target i) := by
      intro Repair
      apply Acceptable
      apply (DistanceUpdateComparison Target State i v).mpr
      rw [Repair.2, Nat.dist_self]
      exact Nat.zero_le _
    rw [UpdateIsParent, if_neg NoRepair, Nat.add_zero]

/-- The pointwise signed change used when averaging over the actual choices. -/
theorem HammingDecrease {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) :
    (Hamming Target State : ℝ) -
        (Hamming Target (Update Target State i v) : ℝ) =
      if State i ≠ Target i ∧ v = Target i then 1 else 0 := by
  have CountBalance := HammingUpdateDecrease Target State i v
  by_cases Repair : State i ≠ Target i ∧ v = Target i
  · rw [if_pos Repair] at CountBalance ⊢
    have RealBalance :
        (Hamming Target (Update Target State i v) : ℝ) + 1 =
          (Hamming Target State : ℝ) := by
      exact_mod_cast CountBalance
    linarith
  · rw [if_neg Repair] at CountBalance ⊢
    have CountsEqual : Hamming Target (Update Target State i v) =
        Hamming Target State := by
      omega
    rw [CountsEqual, sub_self]

/-- Correct target states remain target states under every deterministic proposal. -/
theorem UpdatePreservesZeroHamming {n r : Nat} (Target State : MultiValues n r)
    (i : Fin n) (v : Fin r) (ParentZero : Hamming Target State = 0) :
    Hamming Target (Update Target State i v) = 0 := by
  have CountBalance := HammingUpdateDecrease Target State i v
  rw [ParentZero] at CountBalance
  omega

end ECTheoryLib.Analysis.RLSMultival
