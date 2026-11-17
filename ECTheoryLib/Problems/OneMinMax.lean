import ECTheoryLib.Problems.OneMax
import ECTheoryLib.Problems.Pareto
import ECTheoryLib.Problems.LeadingOnes

/-!
# OneMinMax

Both objectives are maximized: objective 0 counts ones, objective 1 counts zeroes.
Every search point is Pareto optimal; distinct Hamming weights are incomparable.
The objective order is explicitly (ones, zeroes); some papers swap the coordinates.
Source: Covantes Osuna et al., Definition 2.2,
https://arxiv.org/pdf/1805.01221
-/

namespace ECTheoryLib

/-- Number of zero bits, written as n minus OneMax; OneMaxLeN ensures the natural subtraction counts correctly. -/
def OneMin {n : Nat} (x : Bits n) : Nat := n - OneMax x

/-- The pair of maximized objectives (number of ones, number of zeros). Every bit string is Pareto optimal, but full front coverage requires every distinct objective vector. -/
def OneMinMax {n : Nat} (x : Bits n) : Fin 2 → Nat :=
  Problems.BiObjective (OneMax x) (OneMin x)

namespace Problems.OneMinMax

theorem OneMaxAddOneMin {n : Nat} (x : Bits n) : OneMax x + OneMin x = n := by
  unfold OneMin
  exact Nat.add_sub_of_le (OneMax.OneMaxLeN x)

theorem OneMinLeN {n : Nat} (x : Bits n) : OneMin x ≤ n := by
  exact Nat.sub_le n (OneMax x)

/-- Subtracting the number of ones really counts the zero bits. -/
theorem OneMinEqualsZeroCount {n : Nat} (x : Bits n) :
    OneMin x = ∑ i : Fin n, if x i then 0 else 1 := by
  have PerBitSum (i : Fin n) :
      (if x i then 1 else 0 : Nat) + (if x i then 0 else 1 : Nat) = 1 := by
    cases x i
    · rfl
    · rfl
  have CountSum : OneMax x + (∑ i : Fin n, if x i then 0 else 1) = n := by
    unfold OneMax
    rw [← Finset.sum_add_distrib]
    simp only [PerBitSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Nat.mul_one]
  unfold OneMin
  omega

theorem WeakDominanceIffEqualWeight {n : Nat} (x y : Bits n) :
    ParetoMaxNotWorse ECTheoryLib.OneMinMax y x ↔ OneMax x = OneMax y := by
  change (∀ i, BiObjective (OneMax x) (n - OneMax x) i ≤
    BiObjective (OneMax y) (n - OneMax y) i) ↔ _
  rw [BiObjectiveLeIff]
  have XBound := OneMax.OneMaxLeN x
  have YBound := OneMax.OneMaxLeN y
  omega

theorem EveryPointIsParetoMaximal {n : Nat} (x : Bits n) :
    IsParetoMaximal ECTheoryLib.OneMinMax x := by
  intro y Dominance
  have EqualWeight := (WeakDominanceIffEqualWeight x y).mp Dominance
  apply (WeakDominanceIffEqualWeight y x).mpr
  exact EqualWeight.symm

theorem DifferentWeightsIncomparable {n : Nat} (x y : Bits n)
    (DifferentWeights : OneMax x ≠ OneMax y) :
    ¬ ParetoMaxNotWorse ECTheoryLib.OneMinMax y x ∧
      ¬ ParetoMaxNotWorse ECTheoryLib.OneMinMax x y := by
  constructor
  · intro Dominance
    exact DifferentWeights ((WeakDominanceIffEqualWeight x y).mp Dominance)
  · intro Dominance
    exact DifferentWeights ((WeakDominanceIffEqualWeight y x).mp Dominance).symm

theorem EveryFrontValueRealized {n Weight : Nat} (WeightBound : Weight ≤ n) :
    ∃ x : Bits n, IsParetoMaximal ECTheoryLib.OneMinMax x ∧
      ECTheoryLib.OneMinMax x = BiObjective Weight (n - Weight) := by
  refine ⟨PrefixOnes n Weight, EveryPointIsParetoMaximal _, ?_⟩
  unfold ECTheoryLib.OneMinMax OneMin
  rw [LeadingOnes.OneMaxPrefixOnes WeightBound]

end Problems.OneMinMax
end ECTheoryLib
