import ECTheoryLib.Analysis.LOTZ.OneBitProgress
import ECTheoryLib.Algorithms.ArchiveSearch
import ECTheoryLib.Tools.Runtime.Phases

/-!
# LOTZ coverage with explicit archive-search policies

The geometric witnesses and pointwise update bounds do not depend on a mutation
policy. Two explicit probability floors therefore supply both phase drifts on
the original composed transition. Parent support need not be restricted to the
archive: every other offspring still has nonnegative potential progress.
-/
namespace ECTheoryLib.Analysis.LOTZCoverage
open MeasureTheory ECTheoryLib.Probability Tools.Runtime
noncomputable section

/-- Retain one useful parent-offspring event from the full archive transition. -/
theorem PolicyProgressFloor {n : ℕ}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (Theta Delta : ℝ) (NonnegativeDelta : 0 ≤ Delta)
    (V : ParetoPopulation (Bits n) → ℝ) (P : ParetoPopulation (Bits n))
    (Nonnegative : ∀ y, 0 ≤ V P - V (Update P y))
    (x : Bits n) (i : Fin n)
    (ParentFloor : Theta ≤ (Parent P x).toReal)
    (MutationFloor : Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Progress : 1 ≤ V P - V (Update P (OnebitMutation x i))) :
    Theta * Delta ≤ ∫ Q, V P - V Q
      ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure := by
  let Local : Bits n → ℝ := fun z =>
    ∫ y, V P - V (Update P y) ∂(Mutation z).toMeasure
  have LocalNonnegative (z : Bits n) : 0 ≤ Local z := integral_nonneg Nonnegative
  have MutationBound : Delta ≤ Local x := by
    have Bound := PMFIntegralLowerOfPoint (Mutation x)
      (fun y => V P - V (Update P y)) Nonnegative (OnebitMutation x i)
    calc
      Delta = Delta * 1 := (mul_one _).symm
      _ ≤ (Mutation x (OnebitMutation x i)).toReal *
          (V P - V (Update P (OnebitMutation x i))) :=
        mul_le_mul MutationFloor Progress (by norm_num) ENNReal.toReal_nonneg
      _ ≤ Local x := Bound
  have ParentBound := PMFIntegralLowerOfPoint (Parent P) Local LocalNonnegative x
  have Bound := (mul_le_mul ParentFloor MutationBound NonnegativeDelta
    ENNReal.toReal_nonneg).trans ParentBound
  rw [ArchiveSearchStep, PMFIntegralBind]
  simp_rw [PMFIntegralMap]
  rw [PMF.integral_eq_sum] at Bound
  exact Bound

/-- A useful one-bit event gives unit drift of the scaled first-front deficit. -/
theorem PolicyFirstDrift {n : ℕ}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (Theta Delta : ℝ)
    (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (P : ParetoPopulation (Bits n))
    (ParentFloor : ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal) (Outside : ¬ Region P) :
    1 ≤ ∫ Q, (FirstLevel P : ℝ) / (Theta * Delta) -
      (FirstLevel Q : ℝ) / (Theta * Delta)
      ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure := by
  obtain ⟨x, InP, i, Progress⟩ := UsefulFirstMutation P Outside
  have Nonnegative (y : Bits n) : 0 ≤ (FirstLevel P : ℝ) - FirstLevel (Update P y) :=
    sub_nonneg.mpr (Nat.cast_le.mpr (FirstLevelUpdate P y))
  have RealProgress : 1 ≤ (FirstLevel P : ℝ) - FirstLevel (Update P (OnebitMutation x i)) := by
    have Cast : (FirstLevel (Update P (OnebitMutation x i)) : ℝ) + 1 ≤ FirstLevel P := by
      exact_mod_cast Progress
    linarith
  have Bound := PolicyProgressFloor Parent Mutation Theta Delta PositiveDelta.le
    (fun Q => (FirstLevel Q : ℝ)) P Nonnegative x i (ParentFloor x InP)
    (MutationFloor x i) RealProgress
  simp only [← sub_div]
  rw [integral_div]
  exact (le_div_iff₀ (mul_pos PositiveTheta PositiveDelta)).mpr (by simpa only [one_mul] using Bound)

/-- A missing adjacent front point gives unit drift after entering the front. -/
theorem PolicySecondDrift {n : ℕ}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (Theta Delta : ℝ)
    (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (P : ParetoPopulation (Bits n))
    (ParentFloor : ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal)
    (Inside : Region P) (Incomplete : ¬ Complete P) :
    1 ≤ ∫ Q, Missing P / (Theta * Delta) - Missing Q / (Theta * Delta)
      ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure := by
  obtain ⟨x, InP, i, Progress⟩ := UsefulCoverageMutation P Inside Incomplete
  have Bound := PolicyProgressFloor Parent Mutation Theta Delta PositiveDelta.le Missing P
    (fun y => sub_nonneg.mpr (MissingUpdate P y)) x i (ParentFloor x InP)
    (MutationFloor x i) Progress
  simp only [← sub_div]
  rw [integral_div]
  exact (le_div_iff₀ (mul_pos PositiveTheta PositiveDelta)).mpr (by simpa only [one_mul] using Bound)

/-- The shared two-phase certificate on the full archive state, with both
policy floors discharged separately from deterministic LOTZ geometry. -/
def PolicyCertificate {n : ℕ}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (Theta Delta : ℝ)
    (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (ParentFloor : ∀ P, Valid P → ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal) :
    TwoPhaseCertificate (ArchiveSearchStep Parent Mutation Dominates) Complete Valid Region where
  First := fun P => (FirstLevel P : ℝ) / (Theta * Delta)
  Second := fun P => Missing P / (Theta * Delta)
  Budget := ((n : ℝ) + 1) / (Theta * Delta)
  BudgetPositive := div_pos (by positivity) (mul_pos PositiveTheta PositiveDelta)
  FirstNonnegative := fun P => div_nonneg (Nat.cast_nonneg _) (mul_pos PositiveTheta PositiveDelta).le
  SecondNonnegative := fun P => div_nonneg (MissingNonnegative P) (mul_pos PositiveTheta PositiveDelta).le
  SecondZeroIffGoal := by
    intro P
    rw [div_eq_zero_iff]
    simp only [(mul_pos PositiveTheta PositiveDelta).ne', or_false, MissingZeroIff]
  GoalInRegion := CompleteInRegion
  SecondBound := fun P _ => div_le_div_of_nonneg_right (MissingBound P)
    (mul_pos PositiveTheta PositiveDelta).le
  PreservesValid := by
    intro P
    apply PMFAEOfSupport
    intro Q Possible IsValid
    obtain ⟨_x, _ParentPossible, y, _MutationPossible, rfl⟩ :=
      (ArchiveSearchStepSupport Parent Mutation Dominates P Q).mp Possible
    exact ParetoArchiveUpdateValid Dominates P.val y IsValid
  PreservesRegion := by
    intro P
    apply PMFAEOfSupport
    intro Q Possible _IsValid Inside
    obtain ⟨_x, _ParentPossible, y, _MutationPossible, rfl⟩ :=
      (ArchiveSearchStepSupport Parent Mutation Dominates P Q).mp Possible
    exact Inside.mono (ObservedRetained P y)
  PreservesGoal := by
    intro P
    apply PMFAEOfSupport
    intro Q Possible _IsValid Covered
    obtain ⟨_x, _ParentPossible, y, _MutationPossible, rfl⟩ :=
      (ArchiveSearchStepSupport Parent Mutation Dominates P Q).mp Possible
    exact Covered.trans (ObservedRetained P y)
  FirstDrift := fun P IsValid => PolicyFirstDrift Parent Mutation Theta Delta
    PositiveTheta PositiveDelta MutationFloor P (ParentFloor P IsValid)
  SecondDrift := fun P IsValid => PolicySecondDrift Parent Mutation Theta Delta
    PositiveTheta PositiveDelta MutationFloor P (ParentFloor P IsValid)

/-- Arbitrary valid initialization reaches complete current-front coverage
within the combined phase budget in extended expectation. -/
theorem PolicyRuntimeBound {n : ℕ}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n)) (Theta Delta : ℝ)
    (PositiveTheta : 0 < Theta) (PositiveDelta : 0 < Delta)
    (ParentFloor : ∀ P, Valid P → ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (Initial : PMF (ParetoPopulation (Bits n)))
    (InitiallyValid : ∀ P ∈ Initial.support, Valid P) :
    ExpectedHittingTime (ArchiveSearchStep Parent Mutation Dominates) Complete Initial ≤
      ENNReal.ofReal ((2 * (n : ℝ) + 1) / (Theta * Delta)) := by
  have Bound := (PolicyCertificate Parent Mutation Theta Delta PositiveTheta PositiveDelta
    ParentFloor MutationFloor).RuntimeUniformBound Initial
    (PMFAEOfSupport Initial Valid InitiallyValid) ((n : ℝ) / (Theta * Delta))
    (fun P => div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le n (BestScore P)))
      (mul_pos PositiveTheta PositiveDelta).le)
  change ExpectedHittingTime (ArchiveSearchStep Parent Mutation Dominates) Complete Initial ≤
    ENNReal.ofReal ((n : ℝ) / (Theta * Delta) + ((n : ℝ) + 1) / (Theta * Delta)) at Bound
  have Normalize : (n : ℝ) / (Theta * Delta) + ((n : ℝ) + 1) / (Theta * Delta) =
      (2 * (n : ℝ) + 1) / (Theta * Delta) := by ring
  simpa only [Normalize] using Bound

end
end ECTheoryLib.Analysis.LOTZCoverage
