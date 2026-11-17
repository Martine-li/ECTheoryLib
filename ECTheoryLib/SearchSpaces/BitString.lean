/-!
# Binary search space

Bit strings have coordinates indexed by `Fin n`. This module specifies search
objects and the all-ones string, without objectives or mutation policies.
The empty string at `n = 0` is included.
-/

namespace ECTheoryLib

/-- A length-`n` binary string, indexed by positions `0, ..., n-1`. -/
abbrev Bits (n : Nat) := Fin n → Bool

/-- The binary string with every coordinate equal to true. -/
def AllOnes (n : Nat) : Bits n :=
  
  fun _ => true

end ECTheoryLib
