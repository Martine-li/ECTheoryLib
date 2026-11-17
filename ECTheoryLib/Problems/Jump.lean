import ECTheoryLib.Problems.OneMax
import Mathlib.Tactic

/-!
# Jump with the conventional additive offset

The primary definition is `k + |x|₁` for `|x|₁ ≤ n-k` or `|x|₁=n`,
and `n-|x|₁` otherwise. Literature normally assumes `1 ≤ k ≤ n`.
The definition is total; the generic bounds below also hold outside this domain.
Source: Doerr and Zheng, AAAI 2021, Definition 4 (preceding Jump definition),
https://cdn.aaai.org/ojs/17459/17459-13-20953-1-2-20210518.pdf
-/

namespace ECTheoryLib

/-- Jump objective as a function of Hamming weight: k+Weight at or below n-k and at n, and n-Weight in the gap. The total definition uses truncated natural subtraction; usual benchmark results state their restrictions on k explicitly. -/
def JumpValue (n k Weight : Nat) : Nat :=
  if Weight ≤ n - k ∨ Weight = n then k + Weight else n - Weight

/-- Apply JumpValue to a bit string's one count, with k as the gap parameter. This definition imposes no parameter restrictions by itself. -/
def Jump {n : Nat} (k : Nat) (x : Bits n) : Nat :=
  JumpValue n k (OneMax x)

namespace Problems.Jump

theorem JumpValueLeMax {n k Weight : Nat} (WeightBound : Weight ≤ n) :
    JumpValue n k Weight ≤ n + k := by
  unfold JumpValue
  split_ifs
  · omega
  · omega

theorem JumpValueAtN (n k : Nat) : JumpValue n k n = n + k := by
  unfold JumpValue
  rw [if_pos (Or.inr rfl)]
  exact Nat.add_comm k n

theorem JumpValueEqMaxIff {n k Weight : Nat} (WeightBound : Weight ≤ n) :
    JumpValue n k Weight = n + k ↔ Weight = n := by
  constructor
  · intro ValueIsMax
    unfold JumpValue at ValueIsMax
    split_ifs at ValueIsMax with OutsideValley
    · omega
    · have InsideValley : n - k < Weight ∧ Weight ≠ n := by
        push Not at OutsideValley
        exact OutsideValley
      omega
  · intro WeightIsN
    rw [WeightIsN]
    exact JumpValueAtN n k

theorem JumpLeMax {n k : Nat} (x : Bits n) : Jump k x ≤ n + k := by
  exact JumpValueLeMax (OneMax.OneMaxLeN x)

theorem JumpAllOnes {n k : Nat} : Jump k (AllOnes n) = n + k := by
  unfold Jump
  rw [OneMax.OneMaxAllOnes]
  exact JumpValueAtN n k

theorem JumpEqMaxIffEqAllOnes {n k : Nat} (x : Bits n) :
    Jump k x = n + k ↔ x = AllOnes n := by
  unfold Jump
  rw [JumpValueEqMaxIff (OneMax.OneMaxLeN x)]
  exact OneMax.OneMaxEqNIffEqAllOnes x

theorem IsOptimalIffEqAllOnes {n k : Nat} (x : Bits n) :
    IsMaximizer (Jump k) x ↔ x = AllOnes n := by
  constructor
  · intro Optimal
    have LowerBound := Optimal (AllOnes n)
    rw [JumpAllOnes] at LowerBound
    apply (JumpEqMaxIffEqAllOnes x).mp
    exact Nat.le_antisymm (JumpLeMax x) LowerBound
  · intro EqualsAllOnes y
    rw [EqualsAllOnes, JumpAllOnes]
    exact JumpLeMax y

end Problems.Jump
end ECTheoryLib
