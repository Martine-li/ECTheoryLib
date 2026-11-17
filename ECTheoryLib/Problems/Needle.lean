import ECTheoryLib.Problems.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Needle maximization

A specified isolated optimum has value one; the plateau has value zero.
The unique-maximizer statement also covers singleton search spaces.
-/

namespace ECTheoryLib.Problems

/-- Needle maximization gives value one at a specified target and zero elsewhere.
Every non-target solution lies on the same fitness plateau. -/
def Needle {State : Type*} [DecidableEq State] (Target x : State) : ℕ :=
  if x = Target then 1 else 0

namespace Needle

theorem AtTarget {State : Type*} [DecidableEq State] (Target : State) :
    Needle Target Target = 1 := by
  rw [Needle, if_pos rfl]

theorem AwayFromTarget {State : Type*} [DecidableEq State] (Target x : State)
    (Away : x ≠ Target) : Needle Target x = 0 := by
  rw [Needle, if_neg Away]

/-- The isolated target is the unique global maximizer, including singleton spaces. -/
theorem IsOptimalIffEqTarget {State : Type*} [DecidableEq State] (Target x : State) :
    IsMaximizer (Needle Target) x ↔ x = Target := by
  constructor
  · intro Optimal
    by_contra Away
    have Compare := Optimal Target
    rw [AtTarget, AwayFromTarget Target x Away] at Compare
    omega
  · intro Equal
    subst x
    intro y
    rw [AtTarget]
    unfold Needle
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le 1

end Needle
end ECTheoryLib.Problems
