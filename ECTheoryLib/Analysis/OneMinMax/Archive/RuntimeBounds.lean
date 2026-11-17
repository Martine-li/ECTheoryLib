import ECTheoryLib.Analysis.OneMinMax.Archive.Drift
import ECTheoryLib.Tools.Runtime.LocalDrift

/-!
# A reusable OneMinMax coverage runtime bound

The actual archive-search trajectory reaches current complete front coverage
within expected time at most `2 H_(n+1) / (Theta * Delta)`, when every current
member has selection probability at least `Theta > 0` and every exact one-bit
offspring has mutation probability at least `Delta > 0`.

Initialization may be any PMF supported on valid nonempty archives. Time zero
is initialization; infinity represents failure to hit or divergent expected time.
Finite expectation is concluded from the bound. No connectedness of the initial
or later represented objective values is assumed.
-/
namespace ECTheoryLib.Analysis.OneMinMaxCoverage
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A valid archive remains valid under the actual parent/mutation/update kernel. -/
theorem StepPreservesValid {n : Nat}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (P : ParetoPopulation (Bits n)) :
    ∀ᵐ Q ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure, Valid P → Valid Q := by
  apply PMFAEOfSupport
  intro Q Possible IsValid
  obtain ⟨_x, _ParentPossible, y, _MutationPossible, rfl⟩ :=
    (ArchiveSearchStepSupport Parent Mutation Dominates P Q).mp Possible
  exact ParetoArchiveUpdateValid Dominates P.val y IsValid

/-- Current complete coverage is absorbing in objective space, even if equal-value
representatives continue to change in decision space. -/
theorem StepPreservesZero {n : Nat}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (P : ParetoPopulation (Bits n)) :
    ∀ᵐ Q ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure,
      Valid P → Potential P = 0 → Potential Q = 0 := by
  apply PMFAEOfSupport
  intro Q Possible _IsValid Zero
  obtain ⟨_x, _ParentPossible, y, _MutationPossible, rfl⟩ :=
    (ArchiveSearchStepSupport Parent Mutation Dominates P Q).mp Possible
  have Decrease := UpdateDecreaseNonnegative P y
  have Nonnegative := PotentialNonnegative (Update P y)
  change Potential (Update P y) = 0
  linarith

/-- Initial-distribution-dependent coverage bound. All local probability and
validity premises refer to the actual transition PMFs, not to a scalar surrogate. -/
theorem RuntimeUpperBound {n : Nat}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n))
    (Theta Delta : ℝ) (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (ParentFloor : ∀ P, Valid P → ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedHittingTime (ArchiveSearchStep Parent Mutation Dominates) Complete Initial ≤
      ENNReal.ofReal ((∫ P, Potential P ∂Initial.toMeasure) / (Theta * Delta)) := by
  classical
  apply Tools.Runtime.AdditiveRuntimeUpperBound
    (ArchiveSearchStep Parent Mutation Dominates) Initial Potential Complete Valid
    PotentialNonnegative PotentialZeroIffComplete
    (PMFAEOfSupport Initial Valid InitiallyValid)
    (StepPreservesValid Parent Mutation) (StepPreservesZero Parent Mutation)
    (Theta * Delta) (mul_pos PositiveTheta PositiveDelta)
  intro P IsValid Nonzero
  exact OneStepDriftLowerBound Parent Mutation Theta Delta PositiveDelta.le MutationFloor P
    (fun Covered => Nonzero ((PotentialZeroIffComplete P).mpr Covered))
    (ParentFloor P IsValid)

/-- Uniform harmonic coverage bound for every valid initial distribution.
This is the frozen interface reused by different mutation and parent policies. -/
theorem RuntimeHarmonicBound {n : Nat}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n))
    (Theta Delta : ℝ) (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (ParentFloor : ∀ P, Valid P → ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedHittingTime (ArchiveSearchStep Parent Mutation Dominates) Complete Initial ≤
      ENNReal.ofReal (2 * (harmonic (n + 1) : ℝ) / (Theta * Delta)) := by
  classical
  apply (RuntimeUpperBound Parent Mutation Theta Delta PositiveTheta PositiveDelta
    ParentFloor MutationFloor Initial InitiallyValid).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (mul_pos PositiveTheta PositiveDelta).le
  have MeanBound := integral_mono (μ := Initial.toMeasure)
    (Integrable.of_finite (f := fun P : ParetoPopulation (Bits n) => Potential P))
    (integrable_const (2 * (harmonic (n + 1) : ℝ))) PotentialBound
  simpa only [integral_const, probReal_univ, one_smul] using MeanBound

/-- Uniform parent selection has a probability floor of `1/(n+1)` on valid archives. -/
theorem UniformParentFloor {n : Nat} (P : ParetoPopulation (Bits n)) (IsValid : Valid P)
    (x : Bits n) (InP : x ∈ P.val) :
    1 / ((n : ℝ) + 1) ≤ (UniformParetoParent P x).toReal := by
  rw [UniformParetoParentProbability P x InP, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have CardPositive : (0 : ℝ) < P.val.card := Nat.cast_pos.mpr P.property.card_pos
  have CardBound : (P.val.card : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast ArchiveSizeBound P IsValid
  simpa only [one_div] using one_div_le_one_div_of_le CardPositive CardBound

end
end ECTheoryLib.Analysis.OneMinMaxCoverage
