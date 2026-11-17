import ECTheoryLib.Problems.LOTZ
import ECTheoryLib.SearchSpaces.BitString

/-!
# Local geometry of the LOTZ Pareto front

Dominance compares the prefix and suffix lengths coordinatewise. A Pareto point
has a unique decision-space representative, and no distinct point can weakly
dominate it. Non-Pareto points admit an improvement by changing the first zero
after their leading prefix, without harming their trailing zero suffix.
This module states coordinate changes as functions; mutation kernels are supplied
by the analysis layer, preserving the problem/operator dependency boundary.
-/
namespace ECTheoryLib.Problems.LOTZ

/-- LOTZ dominance is exactly coordinatewise comparison of prefix and suffix lengths. -/
theorem DominanceIff {n : ℕ} (x y : Bits n) :
    ParetoMaxNotWorse ECTheoryLib.LOTZ x y ↔
      LeadingOnes y ≤ LeadingOnes x ∧ TrailingZeroes y ≤ TrailingZeroes x :=
  BiObjectiveLeIff _ _ _ _

/-- A canonical Pareto point can only be weakly dominated by itself.
This is decision-vector uniqueness, stronger than equality of objective values. -/
theorem DominatesPrefixIff {n j : ℕ} (Bound : j ≤ n) (y : Bits n) :
    ParetoMaxNotWorse ECTheoryLib.LOTZ y (PrefixOnes n j) ↔ y = PrefixOnes n j := by
  constructor
  · intro Dominates
    obtain ⟨Prefix, Suffix⟩ := (DominanceIff _ _).mp Dominates
    rw [LeadingOnes.LeadingOnesPrefixOnes Bound] at Prefix
    rw [LeadingOnes.TrailingZeroesPrefixOnes Bound] at Suffix
    have Sum := LeadingOnes.LeadingOnesAddTrailingZeroesLeN y
    have EqualPrefix : LeadingOnes y = j := by omega
    have Full : LeadingOnes y + TrailingZeroes y = n := by omega
    have Canonical := (FullCoverageIffPrefixOnes y).mp Full
    simpa only [EqualPrefix] using Canonical
  · intro Equal
    rw [Equal]
    exact fun _ => le_rfl

/-- If the longest one prefix does not fill the string, the next bit is zero. -/
theorem FirstZeroBit {n : ℕ} (x : Bits n) (Bound : LeadingOnes x < n) :
    x ⟨LeadingOnes x, Bound⟩ = false := by
  cases Bit : x ⟨LeadingOnes x, Bound⟩ with
  | false => rfl
  | true =>
    have Longer : HasOnePrefix x (LeadingOnes x + 1) := by
      intro i InPrefix
      by_cases Earlier : i.val < LeadingOnes x
      · exact LeadingOnes.HasLeadingOnesPrefix x i Earlier
      · have Equal : i = ⟨LeadingOnes x, Bound⟩ := Fin.ext (show i.val = LeadingOnes x by omega)
        rw [Equal]
        exact Bit
    have Impossible := LeadingOnes.PrefixLeLeadingOnes x Bound Longer
    omega

/-- Setting the first zero to one strictly increases the sum of prefix and
suffix lengths at every non-Pareto point. The original zero suffix is untouched. -/
theorem FirstZeroImproves {n : ℕ} (x : Bits n)
    (NotFront : LeadingOnes x + TrailingZeroes x < n) :
    ∃ i : Fin n, x i = false ∧
      LeadingOnes x + TrailingZeroes x + 1 ≤
        LeadingOnes (Function.update x i true) + TrailingZeroes (Function.update x i true) := by
  let i : Fin n := ⟨LeadingOnes x, by omega⟩
  refine ⟨i, FirstZeroBit x i.isLt, ?_⟩
  have NewPrefix : HasOnePrefix (Function.update x i true) (LeadingOnes x + 1) := by
    intro j InPrefix
    by_cases Equal : j = i
    · simp only [Equal, Function.update_self]
    · rw [Function.update_of_ne Equal]
      apply LeadingOnes.HasLeadingOnesPrefix
      have Different : j.val ≠ LeadingOnes x := fun Eq => Equal (Fin.ext Eq)
      omega
  have NewSuffix : HasZeroSuffix (Function.update x i true) (TrailingZeroes x) := by
    intro j InSuffix
    have Different : j ≠ i := by
      intro Equal
      have Position : j.val = LeadingOnes x := congrArg Fin.val Equal
      omega
    rw [Function.update_of_ne Different]
    exact LeadingOnes.HasTrailingZeroesSuffix x j InSuffix
  have PrefixBound := LeadingOnes.PrefixLeLeadingOnes (Function.update x i true)
    (show LeadingOnes x + 1 ≤ n by omega) NewPrefix
  have SuffixBound := LeadingOnes.SuffixLeTrailingZeroes (Function.update x i true)
    (LeadingOnes.TrailingZeroesLeN x) NewSuffix
  omega

end ECTheoryLib.Problems.LOTZ
