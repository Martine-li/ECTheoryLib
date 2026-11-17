import ECTheoryLib.Tools.Coverage.Finite
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Coverage of an integer interval

The positive weight of level `j` in `0, ..., n` is
`1 / (j + 1) + 1 / (n - j + 1)`. Its total is `2 H_(n+1)`.
The two reciprocal terms compensate for progress rates proportional to the
distance from either endpoint. No interval assumption is made on the observed set:
every nonempty incomplete subset has a covered-to-missing adjacent pair.
-/
namespace ECTheoryLib.Tools.Coverage
noncomputable section

/-- Symmetric reciprocal weight for a target level of the integer interval. -/
def LineWeight (n j : Nat) : ℝ :=
  1 / ((j : ℝ) + 1) + 1 / ((n - j : Nat) + 1 : ℝ)

/-- Every target has positive weight, including the endpoints. -/
theorem LineWeightPositive (n j : Nat) : 0 < LineWeight n j := by
  unfold LineWeight
  positivity

/-- A downward move to `j` has `j+1` possible elementary causes. -/
theorem LineWeightDown (n j : Nat) : 1 ≤ ((j : ℝ) + 1) * LineWeight n j := by
  have Positive : 0 < (j : ℝ) + 1 := by positivity
  unfold LineWeight
  rw [mul_add, mul_one_div_cancel Positive.ne']
  have Nonnegative : 0 ≤ ((j : ℝ) + 1) * (1 / ((n - j : Nat) + 1 : ℝ)) := by positivity
  linarith

/-- An upward move to `j` has `n-j+1` possible elementary causes. -/
theorem LineWeightUp (n j : Nat) : 1 ≤ ((n - j : Nat) + 1 : ℝ) * LineWeight n j := by
  have Positive : 0 < ((n - j : Nat) + 1 : ℝ) := by positivity
  unfold LineWeight
  rw [mul_add, mul_one_div_cancel Positive.ne']
  have Nonnegative : 0 ≤ ((n - j : Nat) + 1 : ℝ) * (1 / ((j : ℝ) + 1)) := by positivity
  linarith

/-- The total interval weight is twice the `(n+1)`st harmonic number. -/
theorem LineWeightTotal (n : Nat) :
    (∑ j ∈ Finset.range (n + 1), LineWeight n j) = 2 * (harmonic (n + 1) : ℝ) := by
  have HarmonicSum : (∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + 1)) =
      (harmonic (n + 1) : ℝ) := by
    unfold harmonic
    simp only [Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one, one_div,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
  have Reflected := Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) (n + 1)
  simp only [Nat.add_sub_cancel] at Reflected
  unfold LineWeight
  rw [Finset.sum_add_distrib, Reflected, HarmonicSum]
  ring

/-- A nonempty, incomplete subset of `0, ..., n` has a present level adjacent to
an absent level. Holes and disconnected observed sets are allowed. -/
theorem AdjacentMissingLevel (n : Nat) (Observed : Finset Nat)
    (Within : Observed ⊆ Finset.range (n + 1)) (Nonempty : Observed.Nonempty)
    (Incomplete : ¬ Finset.range (n + 1) ⊆ Observed) :
    ∃ k ∈ Observed, ∃ j, j ≤ n ∧ j ∉ Observed ∧ (k + 1 = j ∨ j + 1 = k) := by
  by_contra NoBoundary
  have Adjacent (k : Nat) (Inside : k < n) : k ∈ Observed ↔ k + 1 ∈ Observed := by
    constructor
    · intro Present
      by_contra Missing
      exact NoBoundary ⟨k, Present, k + 1, by omega, Missing, Or.inl rfl⟩
    · intro Present
      by_contra Missing
      exact NoBoundary ⟨k + 1, Present, k, by omega, Missing, Or.inr rfl⟩
  -- If no boundary existed, membership would be constant along the whole line.
  have SameAsZero (k : Nat) (Inside : k ≤ n) : k ∈ Observed ↔ 0 ∈ Observed := by
    induction k with
    | zero => rfl
    | succ k Previous =>
        exact (Adjacent k (by omega)).symm.trans (Previous (by omega))
  obtain ⟨k, Present⟩ := Nonempty
  have ZeroPresent : 0 ∈ Observed :=
    (SameAsZero k (by have := Finset.mem_range.mp (Within Present); omega)).mp Present
  apply Incomplete
  intro j InRange
  exact (SameAsZero j (by have := Finset.mem_range.mp InRange; omega)).mpr ZeroPresent

end
end ECTheoryLib.Tools.Coverage
