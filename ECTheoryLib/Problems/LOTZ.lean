import ECTheoryLib.Problems.LeadingOnes
import ECTheoryLib.Problems.Pareto

/-!
# LeadingOnesTrailingZeroes (LOTZ)

Both objectives are maximized. The Pareto set consists exactly of strings
`1^Length 0^(n-Length)`; the Pareto front is `(Length,n-Length)`, `0 ≤ Length ≤ n`.
This includes the empty search space dimension `n=0`.
Source: Covantes Osuna et al., Definition 2.3,
https://arxiv.org/pdf/1805.01221
-/

namespace ECTheoryLib

/-- The two maximized objectives: leading-one prefix length and trailing-zero suffix length, in that order. -/
def LOTZ {n : Nat} (x : Bits n) : Fin 2 → Nat :=
  Problems.BiObjective (LeadingOnes x) (TrailingZeroes x)

namespace Problems.LOTZ

/-- The canonical string with Length leading ones realizes the front vector
(Length, n-Length), for every index between zero and n. -/
theorem PrefixOnesFitness {n Length : Nat} (LengthBound : Length ≤ n) :
    ECTheoryLib.LOTZ (PrefixOnes n Length) = BiObjective Length (n - Length) := by
  unfold ECTheoryLib.LOTZ
  rw [LeadingOnes.LeadingOnesPrefixOnes LengthBound]
  rw [LeadingOnes.TrailingZeroesPrefixOnes LengthBound]

/-- A single point is Pareto maximal exactly when its leading-one prefix and
trailing-zero suffix cover all coordinates. Here "FullCoverage" concerns that
one string's coordinates; it is not complete Pareto-front coverage by an archive. -/
theorem IsParetoMaximalIffFullCoverage {n : Nat} (x : Bits n) :
    IsParetoMaximal ECTheoryLib.LOTZ x ↔ LeadingOnes x + TrailingZeroes x = n := by
  constructor
  · intro Maximal
    have LeadingBound := LeadingOnes.LeadingOnesLeN x
    have SumBound := LeadingOnes.LeadingOnesAddTrailingZeroesLeN x
    let Candidate := PrefixOnes n (LeadingOnes x)
    have CandidateFitness : ECTheoryLib.LOTZ Candidate =
        BiObjective (LeadingOnes x) (n - LeadingOnes x) := PrefixOnesFitness LeadingBound
    have Dominance : ParetoMaxNotWorse ECTheoryLib.LOTZ Candidate x := by
      unfold ParetoMaxNotWorse
      rw [CandidateFitness]
      change (∀ i, BiObjective (LeadingOnes x) (TrailingZeroes x) i ≤
        BiObjective (LeadingOnes x) (n - LeadingOnes x) i)
      apply (BiObjectiveLeIff _ _ _ _).mpr
      constructor
      · exact Nat.le_refl _
      · omega
    have Reverse := Maximal Candidate Dominance
    have SuffixLowerBound : n - LeadingOnes x ≤ TrailingZeroes x := by
      have SecondCoordinate := Reverse 1
      rw [CandidateFitness] at SecondCoordinate
      exact SecondCoordinate
    omega
  · intro FullCoverage y Dominance
    have Bounds : LeadingOnes x ≤ LeadingOnes y ∧ TrailingZeroes x ≤ TrailingZeroes y := by
      exact (BiObjectiveLeIff _ _ _ _).mp Dominance
    have CandidateSumBound := LeadingOnes.LeadingOnesAddTrailingZeroesLeN y
    apply (BiObjectiveLeIff _ _ _ _).mpr
    constructor
    · omega
    · omega

/-- Prefix and suffix lengths sum to n exactly for canonical strings. This
identifies decision vectors, rather than merely their objective values. -/
theorem FullCoverageIffPrefixOnes {n : Nat} (x : Bits n) :
    LeadingOnes x + TrailingZeroes x = n ↔ x = PrefixOnes n (LeadingOnes x) := by
  constructor
  · intro FullCoverage
    funext i
    by_cases InPrefix : i.val < LeadingOnes x
    · have BitIsOne := LeadingOnes.HasLeadingOnesPrefix x i InPrefix
      have CanonicalBit : PrefixOnes n (LeadingOnes x) i = true := decide_eq_true InPrefix
      rw [BitIsOne, CanonicalBit]
    · have InSuffix : n - TrailingZeroes x ≤ i.val := by omega
      have BitIsZero := LeadingOnes.HasTrailingZeroesSuffix x i InSuffix
      have CanonicalBit : PrefixOnes n (LeadingOnes x) i = false := decide_eq_false InPrefix
      rw [BitIsZero, CanonicalBit]
  · intro Canonical
    have SuffixValue : TrailingZeroes (PrefixOnes n (LeadingOnes x)) = n - LeadingOnes x :=
      LeadingOnes.TrailingZeroesPrefixOnes (LeadingOnes.LeadingOnesLeN x)
    have TrailingValue : TrailingZeroes x = n - LeadingOnes x := by
      calc
        TrailingZeroes x = TrailingZeroes (PrefixOnes n (LeadingOnes x)) := congrArg TrailingZeroes Canonical
        _ = n - LeadingOnes x := SuffixValue
    rw [TrailingValue]
    exact Nat.add_sub_of_le (LeadingOnes.LeadingOnesLeN x)

/-- The Pareto set consists exactly of a leading-one prefix followed by zeroes. -/
theorem IsParetoMaximalIffPrefixOnes {n : Nat} (x : Bits n) :
    IsParetoMaximal ECTheoryLib.LOTZ x ↔ x = PrefixOnes n (LeadingOnes x) := by
  rw [IsParetoMaximalIffFullCoverage]
  exact FullCoverageIffPrefixOnes x

/-- Every vector (Length,n-Length), for 0 <= Length <= n, has a Pareto-optimal
representative. This is a problem property, not an algorithmic discovery claim. -/
theorem EveryFrontValueRealized {n Length : Nat} (LengthBound : Length ≤ n) :
    ∃ x : Bits n, IsParetoMaximal ECTheoryLib.LOTZ x ∧
      ECTheoryLib.LOTZ x = BiObjective Length (n - Length) := by
  refine ⟨PrefixOnes n Length, ?_, PrefixOnesFitness LengthBound⟩
  apply (IsParetoMaximalIffFullCoverage _).mpr
  rw [LeadingOnes.LeadingOnesPrefixOnes LengthBound]
  rw [LeadingOnes.TrailingZeroesPrefixOnes LengthBound]
  exact Nat.add_sub_of_le LengthBound

end Problems.LOTZ
end ECTheoryLib
