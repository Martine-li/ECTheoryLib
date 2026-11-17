import ECTheoryLib.Analysis.OneMinMax.Archive.Coverage
import ECTheoryLib.Analysis.OneMax.BitFlip
import ECTheoryLib.Operators.Mutation.IndependentBitBounds
import ECTheoryLib.Algorithms.ArchiveSearch
import ECTheoryLib.Probability.PMF.FinitePMF

/-!
# Local progress toward complete OneMinMax coverage

The proof separates three obligations: retention of objective values, selection
of a useful parent, and creation of a missing neighboring value. A common lower
bound on each exact one-bit offspring suffices even when the mutation can flip
several bits. All other offspring have nonnegative progress.

The parent policy can depend on the entire archive. The theorem only needs a
selection floor for archive members and does not require the scalar coverage
potential to be a Markov chain.
-/
namespace ECTheoryLib.Analysis.OneMinMaxCoverage
open MeasureTheory ECTheoryLib.Probability Tools.Coverage
noncomputable section

/-- The number of one coordinates, as a real finite sum. -/
theorem OneCountAsReal {n : Nat} (x : Bits n) :
    (∑ i : Fin n, if x i then (1 : ℝ) else 0) = (OneMax x : ℝ) := by
  unfold OneMax
  push_cast
  rfl

/-- A parent next to a missing target offers total elementary progress at least
one. The reciprocal target weight compensates for the number of useful bits. -/
theorem AdjacentParentProgress {n : Nat} (P : ParetoPopulation (Bits n)) (x : Bits n)
    (j : Nat) (Target : j ≤ n) (Missing : j ∉ Observed P)
    (Adjacent : OneMax x + 1 = j ∨ j + 1 = OneMax x) :
    (1 : ℝ) ≤ Finset.univ.sum
      (fun i : Fin n => Potential P - Potential (Update P (OnebitMutation x i))) := by
  rcases Adjacent with Up | Down
  · have CoordinateBound (i : Fin n) :
        (if x i then 0 else LineWeight n j) ≤
          Potential P - Potential (Update P (OnebitMutation x i)) := by
      cases Bit : x i with
      | false =>
          have Value : OneMax (OnebitMutation x i) = j :=
            (OneMax.OneMaxMutationAtZero x i Bit).trans Up
          have Progress := UpdateDecreaseOfMissing P (OnebitMutation x i) (by rw [Value]; exact Missing)
          rw [Value] at Progress
          exact Progress
      | true => exact UpdateDecreaseNonnegative P _
    have Count : (∑ i : Fin n, if x i then (0 : ℝ) else LineWeight n j) =
        (n - OneMax x : Nat) * LineWeight n j := by
      have Each (i : Fin n) : (if x i then (0 : ℝ) else LineWeight n j) =
          (if x i then (0 : ℝ) else 1) * LineWeight n j := by
        cases x i
        · exact (one_mul _).symm
        · exact (zero_mul _).symm
      simp_rw [Each]
      rw [← Finset.sum_mul, Problems.OneMax.ZeroBitCountAsReal]
      rfl
    have CountEq : n - OneMax x = n - j + 1 := by omega
    have Bound := LineWeightUp n j
    rw [CountEq, Nat.cast_add, Nat.cast_one] at Count
    rw [← Count] at Bound
    exact Bound.trans (Finset.sum_le_sum (fun i _ => CoordinateBound i))
  · have CoordinateBound (i : Fin n) :
        (if x i then LineWeight n j else 0) ≤
          Potential P - Potential (Update P (OnebitMutation x i)) := by
      cases Bit : x i with
      | false => exact UpdateDecreaseNonnegative P _
      | true =>
          have Value : OneMax (OnebitMutation x i) = j := by
            have Decrease := OneMax.OneMaxMutationAtOne x i Bit
            omega
          have Progress := UpdateDecreaseOfMissing P (OnebitMutation x i) (by rw [Value]; exact Missing)
          rw [Value] at Progress
          exact Progress
    have Count : (∑ i : Fin n, if x i then LineWeight n j else (0 : ℝ)) =
        (OneMax x : ℝ) * LineWeight n j := by
      have Each (i : Fin n) : (if x i then LineWeight n j else (0 : ℝ)) =
          (if x i then (1 : ℝ) else 0) * LineWeight n j := by
        cases x i
        · exact (zero_mul _).symm
        · exact (one_mul _).symm
      simp_rw [Each]
      rw [← Finset.sum_mul, OneCountAsReal]
    rw [← Down, Nat.cast_add, Nat.cast_one] at Count
    have Bound := LineWeightDown n j
    rw [← Count] at Bound
    exact Bound.trans (Finset.sum_le_sum (fun i _ => CoordinateBound i))

/-- Every incomplete archive has a supported parent whose expected mutation
progress is at least the common exact-one-bit probability floor. -/
theorem UsefulParent {n : Nat} (Mutation : Bits n → PMF (Bits n))
    (Delta : ℝ) (NonnegativeDelta : 0 ≤ Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (P : ParetoPopulation (Bits n)) (Incomplete : ¬ Complete P) :
    ∃ x ∈ P.val, Delta ≤
      ∫ y, Potential P - Potential (Update P y) ∂(Mutation x).toMeasure := by
  obtain ⟨k, Present, j, Target, Missing, Adjacent⟩ :=
    AdjacentMissingLevel n (Observed P) (ObservedWithin P) (ObservedNonempty P) Incomplete
  obtain ⟨x, InP, Value⟩ := Finset.mem_image.mp Present
  refine ⟨x, InP, ?_⟩
  have Elementary := AdjacentParentProgress P x j Target Missing (by rw [Value]; exact Adjacent)
  have Counted := PMFIntegralLowerOfInjection (Mutation x)
    (fun y => Potential P - Potential (Update P y))
    (OnebitMutation x) (OnebitMutationInjective x) (UpdateDecreaseNonnegative P)
    Delta (MutationFloor x)
  calc
    Delta = Delta * 1 := (mul_one _).symm
    _ ≤ Delta * (∑ i : Fin n, (Potential P - Potential (Update P (OnebitMutation x i)))) :=
      mul_le_mul_of_nonneg_left Elementary NonnegativeDelta
    _ ≤ _ := Counted

/-- The actual composed archive kernel has drift at least `Theta * Delta`.
`Theta` is a lower bound on each member's parent-selection probability;
`Delta` bounds the probability of every exact one-bit offspring. -/
theorem OneStepDriftLowerBound {n : Nat}
    (Parent : ParetoPopulation (Bits n) → PMF (Bits n))
    (Mutation : Bits n → PMF (Bits n))
    (Theta Delta : ℝ) (NonnegativeDelta : 0 ≤ Delta)
    (MutationFloor : ∀ x i, Delta ≤ (Mutation x (OnebitMutation x i)).toReal)
    (P : ParetoPopulation (Bits n)) (Incomplete : ¬ Complete P)
    (ParentFloor : ∀ x ∈ P.val, Theta ≤ (Parent P x).toReal) :
    Theta * Delta ≤ ∫ Q, Potential P - Potential Q
      ∂(ArchiveSearchStep Parent Mutation Dominates P).toMeasure := by
  classical
  obtain ⟨x, InP, Progress⟩ := UsefulParent Mutation Delta NonnegativeDelta MutationFloor P Incomplete
  rw [ArchiveSearchStep, PMFIntegralBind]
  simp_rw [PMFIntegralMap]
  have ExpectedNonnegative (z : Bits n) :
      0 ≤ ∫ y, Potential P - Potential (Update P y) ∂(Mutation z).toMeasure :=
    integral_nonneg (UpdateDecreaseNonnegative P)
  calc
    Theta * Delta ≤ (Parent P x).toReal *
        (∫ y, Potential P - Potential (Update P y) ∂(Mutation x).toMeasure) :=
      mul_le_mul (ParentFloor x InP) Progress NonnegativeDelta ENNReal.toReal_nonneg
    _ ≤ ∑ z : Bits n, (Parent P z).toReal *
        (∫ y, Potential P - Potential (Update P y) ∂(Mutation z).toMeasure) :=
      Finset.single_le_sum (fun z _ => mul_nonneg ENNReal.toReal_nonneg (ExpectedNonnegative z))
        (Finset.mem_univ x)

end
end ECTheoryLib.Analysis.OneMinMaxCoverage
