import ECTheoryLib.SearchSpaces.BitString

/-!
Deterministic one-bit mutation and its involution property. Coordinate positions use Fin n; a mutation changes exactly the specified bit. No probability law or objective is part of this operator.
-/

namespace ECTheoryLib

/-- Flip exactly coordinate `i`, preserving all others. No random choice is made. -/
def OnebitMutation {n : Nat} (x : Bits n) (i : Fin n) : Bits n :=
  fun j =>
    if j = i then
      !(x j)
    else
      x j

/-- The chosen coordinate is complemented. -/
theorem OnebitMutationAt {n : Nat} (x : Bits n) (i : Fin n) :
    OnebitMutation x i i = !(x i) := by
  unfold OnebitMutation
  rw [if_pos rfl]

/-- Unchosen coordinates retain their values. -/
theorem OnebitMutationAway {n : Nat} (x : Bits n) (i j : Fin n)
    (DifferentPosition : j ≠ i) : OnebitMutation x i j = x j := by
  unfold OnebitMutation
  rw [if_neg DifferentPosition]

/-- A one-bit offspring differs from its parent at the chosen coordinate. -/
theorem OnebitMutationChanges {n : Nat} (x : Bits n) (i : Fin n) :
    OnebitMutation x i ≠ x := by
  intro SameString
  have SameSelectedBit : OnebitMutation x i i = x i := by
    
    exact congrArg (fun y : Bits n => y i) SameString
  rw [OnebitMutationAt] at SameSelectedBit
  cases BitValue : x i with
  | false =>
      rw [BitValue] at SameSelectedBit
      
      cases SameSelectedBit
  | true =>
      rw [BitValue] at SameSelectedBit
      cases SameSelectedBit

/-- Flipping the same coordinate twice recovers the parent, independently of selection. -/
theorem OnebitMutationTwice {n : Nat} (x : Bits n) (i : Fin n) :
    OnebitMutation (OnebitMutation x i) i = x := by
  funext j
  unfold OnebitMutation
  by_cases SamePosition : j = i
  · rw [if_pos SamePosition, if_pos SamePosition]
    exact Bool.not_not (x j)
  · rw [if_neg SamePosition, if_neg SamePosition]

end ECTheoryLib

namespace ECTheoryLib

/-- Single-coordinate flips commute, including two flips at the same coordinate. -/
theorem OnebitMutationCommute {n : Nat} (x : Bits n) (i j : Fin n) :
    OnebitMutation (OnebitMutation x i) j = OnebitMutation (OnebitMutation x j) i := by
  funext k
  unfold OnebitMutation
  by_cases AtI : k = i
  · by_cases AtJ : k = j
    · simp only [if_pos AtI, if_pos AtJ]
    · simp only [if_pos AtI, if_neg AtJ]
  · by_cases AtJ : k = j
    · simp only [if_neg AtI, if_pos AtJ]
    · simp only [if_neg AtI, if_neg AtJ]

end ECTheoryLib
