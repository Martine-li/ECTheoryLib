import ECTheoryLib.Algorithms.RLS
import ECTheoryLib.Probability.HittingTimes.Expectation
import ECTheoryLib.Problems.LeadingOnes
import ECTheoryLib.Problems.Comparison

/-!
# RLS on LeadingOnes: actual model and prefix deficit

The existing RLS kernel is specialized to weak LeadingOnes maximization.
Neutral suffix flips are accepted. The potential is n-LeadingOnes, not the
zero count. Time zero is initialization; hitting times count subsequent
mutation iterations and retain infinity. Mutation requires positive length.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- The actual one-bit RLS update, accepting equal LeadingOnes fitness. -/
abbrev Update {n : ℕ} (x : Bits n) (i : Fin n) : Bits n :=
  RLSUpdate (Problems.MaxNotWorse LeadingOnes) x i

/-- Prefix deficit, rather than the number of zero bits. -/
def Deficit {n : ℕ} (x : Bits n) : ℕ := n - LeadingOnes x

def Potential {n : ℕ} (x : Bits n) : ℝ := (Deficit x : ℝ)

def Step {n : ℕ} (PositiveLength : 0 < n) : Transition (Bits n) :=
  RLSStep PositiveLength (Problems.MaxNotWorse LeadingOnes)

def ExpectedRuntime {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) : ENNReal :=
  ExpectedHittingTime (Step PositiveLength) (fun x => x = AllOnes n) Initial

theorem PotentialNonnegative {n : ℕ} (x : Bits n) : 0 ≤ Potential x := Nat.cast_nonneg _

theorem PotentialZeroIffTarget {n : ℕ} (x : Bits n) :
    Potential x = 0 ↔ x = AllOnes n := by
  change (Deficit x : ℝ) = 0 ↔ x = AllOnes n
  rw [Nat.cast_eq_zero, Deficit, Nat.sub_eq_zero_iff_le]
  constructor
  · intro Lower
    apply (Problems.LeadingOnes.LeadingOnesEqNIffEqAllOnes x).mp
    exact le_antisymm (Problems.LeadingOnes.LeadingOnesLeN x) Lower
  · intro Target
    rw [Target, Problems.LeadingOnes.LeadingOnesAllOnes]


end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
