import ECTheoryLib.Analysis.LOTZ.ArchiveCoverage
import ECTheoryLib.Algorithms.SEMO
import ECTheoryLib.Operators.Mutation.OneBitBounds
import ECTheoryLib.Probability.PMF.FiniteProgress

/-!
# Useful mutations in the two LOTZ phases

Before the first front point, a member with maximum prefix-plus-suffix score
has a one-bit improvement that cannot be rejected. Afterwards, a present front
point adjacent to a missing one supplies a coverage event. Both arguments use
the same actual SEMO probability floor: 1/[n(n+1)], from uniform parent and
coordinate selection on a valid archive. No shape restriction on its front
subset is needed.
-/
namespace ECTheoryLib.Analysis.LOTZCoverage
open MeasureTheory ECTheoryLib.Probability Tools.Coverage
noncomputable section

/-- Flipping the first zero of a canonical front point reaches its successor. -/
theorem PrefixSuccessorMutation {n j : ℕ} (Bound : j < n) :
    OnebitMutation (PrefixOnes n j) ⟨j, Bound⟩ = PrefixOnes n (j + 1) := by
  funext i
  by_cases Equal : i = ⟨j, Bound⟩
  · subst i
    simp only [OnebitMutationAt, PrefixOnes, Nat.lt_irrefl, decide_false, Bool.not_false,
      Nat.lt_succ_self, decide_true]
  · rw [OnebitMutationAway (PrefixOnes n j) ⟨j, Bound⟩ i Equal]
    unfold PrefixOnes
    have Different : i.val ≠ j := fun Eq => Equal (Fin.ext Eq)
    have Compare : (i.val < j) = (i.val < j + 1) := propext (by omega)
    simp only [Compare]

/-- Adjacent canonical Pareto points differ at exactly one coordinate. -/
theorem PrefixAdjacentMutation {n a b : ℕ} (A : a ≤ n) (B : b ≤ n)
    (Adjacent : a + 1 = b ∨ b + 1 = a) :
    ∃ i : Fin n, OnebitMutation (PrefixOnes n a) i = PrefixOnes n b := by
  rcases Adjacent with Forward | Backward
  · have Bound : a < n := by omega
    refine ⟨⟨a, Bound⟩, ?_⟩
    rw [PrefixSuccessorMutation Bound, Forward]
  · have Bound : b < n := by omega
    refine ⟨⟨b, Bound⟩, ?_⟩
    have Forward := PrefixSuccessorMutation Bound
    rw [Backward] at Forward
    rw [← Forward, OnebitMutationTwice]

/-- Before the front is reached, one member and one coordinate lower the
natural first-phase deficit strictly under the actual archive update. -/
theorem UsefulFirstMutation {n : ℕ} (P : ParetoPopulation (Bits n)) (Outside : ¬ Region P) :
    ∃ x ∈ P.val, ∃ i : Fin n, FirstLevel (Update P (OnebitMutation x i)) < FirstLevel P := by
  obtain ⟨x, InP, Maximal⟩ := Finset.exists_mem_eq_sup P.val P.property Score
  have Positive : 0 < FirstLevel P := Nat.pos_of_ne_zero
    (fun Zero => Outside ((FirstLevelZeroIff P).mp Zero))
  have NotFront : LeadingOnes x + TrailingZeroes x < n := by
    change 0 < n - BestScore P at Positive
    change BestScore P = LeadingOnes x + TrailingZeroes x at Maximal
    omega
  obtain ⟨i, Bit, Progress⟩ := Problems.LOTZ.FirstZeroImproves x NotFront
  have MutationEq : OnebitMutation x i = Function.update x i true := by
    funext j
    by_cases Equal : j = i
    · subst j
      rw [OnebitMutationAt, Bit, Function.update_self]
      rfl
    · rw [OnebitMutationAway x i j Equal, Function.update_of_ne Equal]
  rw [← MutationEq] at Progress
  have Better : BestScore P < Score (OnebitMutation x i) := by
    change BestScore P = Score x at Maximal
    change Score x + 1 ≤ Score (OnebitMutation x i) at Progress
    omega
  have Accepted : ParetoArchiveAccepts Dominates P.val (OnebitMutation x i) := by
    intro y InY Strict
    have Compared := ScoreDominance (OnebitMutation x i) y Strict.1
    have OldBound : Score y ≤ BestScore P := Finset.le_sup InY
    omega
  have ChildBound : Score (OnebitMutation x i) ≤ BestScore (Update P (OnebitMutation x i)) :=
    Finset.le_sup (f := Score) (ParetoArchiveCandidateMem Dominates P.val _ Accepted)
  refine ⟨x, InP, i, ?_⟩
  unfold FirstLevel at Positive ⊢
  omega

/-- In phase two, a present front point has a one-bit neighbor missing from the
current archive. That actual update decreases the missing count by at least one. -/
theorem UsefulCoverageMutation {n : ℕ} (P : ParetoPopulation (Bits n))
    (Inside : Region P) (Incomplete : ¬ Complete P) :
    ∃ x ∈ P.val, ∃ i : Fin n, 1 ≤ Missing P - Missing (Update P (OnebitMutation x i)) := by
  have Within : Observed P ⊆ Finset.range (n + 1) := Finset.filter_subset _ _
  obtain ⟨a, Present, b, B, Absent, Adjacent⟩ := AdjacentMissingLevel n (Observed P) Within Inside Incomplete
  obtain ⟨A, InP⟩ := (ObservedIff P a).mp Present
  obtain ⟨i, MutationEq⟩ := PrefixAdjacentMutation A B Adjacent
  refine ⟨PrefixOnes n a, InP, i, ?_⟩
  rw [MutationEq]
  exact MissingProgress B P Absent

/-- Every member of a valid archive is selected with probability at least 1/(n+1). -/
theorem UniformParentFloor {n : ℕ} (P : ParetoPopulation (Bits n)) (IsValid : Valid P)
    (x : Bits n) (InP : x ∈ P.val) :
    1 / ((n : ℝ) + 1) ≤ (UniformParetoParent P x).toReal := by
  rw [UniformParetoParentProbability P x InP, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have CardPositive : (0 : ℝ) < P.val.card := Nat.cast_pos.mpr P.property.card_pos
  have CardBound : (P.val.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast ArchiveSizeBound P IsValid
  simpa only [one_div] using one_div_le_one_div_of_le CardPositive CardBound

/-- One useful parent-coordinate event gives a local progress floor on the
actual SEMO kernel. Both phase potentials share this probability calculation. -/
theorem ProgressFloor {n : ℕ} (hn : 0 < n) (V : ParetoPopulation (Bits n) → ℝ)
    (P : ParetoPopulation (Bits n)) (IsValid : Valid P)
    (Nonnegative : ∀ y, 0 ≤ V P - V (Update P y))
    (x : Bits n) (InP : x ∈ P.val) (i : Fin n)
    (Progress : 1 ≤ V P - V (Update P (OnebitMutation x i))) :
    1 / ((n : ℝ) + 1) * (1 / (n : ℝ)) ≤
      ∫ Q, V P - V Q ∂(SEMOStep hn Dominates P).toMeasure := by
  let Local : Bits n → ℝ := fun z =>
    ∫ y, V P - V (Update P y) ∂(RandomOneBitMutation hn z).toMeasure
  have LocalNonnegative (z : Bits n) : 0 ≤ Local z := integral_nonneg Nonnegative
  have MutationBound : 1 / (n : ℝ) ≤ Local x := by
    have Bound := PMFIntegralLowerOfPoint (RandomOneBitMutation hn x)
      (fun y => V P - V (Update P y)) Nonnegative (OnebitMutation x i)
    rw [RandomOneBitProbabilityReal] at Bound
    apply le_trans _ Bound
    simpa only [mul_one] using mul_le_mul_of_nonneg_left Progress (by positivity : 0 ≤ 1 / (n : ℝ))
  have ParentBound := PMFIntegralLowerOfPoint (UniformParetoParent P) Local LocalNonnegative x
  have Bound : 1 / ((n : ℝ) + 1) * (1 / (n : ℝ)) ≤ ∫ z, Local z ∂(UniformParetoParent P).toMeasure :=
    (mul_le_mul (UniformParentFloor P IsValid x InP) MutationBound (by positivity)
      ENNReal.toReal_nonneg).trans ParentBound
  rw [SEMOStep, PMFIntegralBind]
  simp_rw [PMFIntegralMap]
  rw [PMF.integral_eq_sum] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.LOTZCoverage
