import ECTheoryLib.Analysis.LeadingOnes.RLS.Drift
import ECTheoryLib.Probability.Processes.PathMarginal

/-!
# Preserved symmetry of the unseen suffix in actual RLS

At a state with LeadingOnes k, flipping coordinate j>k commutes with every
actual RLS update. Earlier prefix positions are rejected; the first zero and
all later positions are accepted. The transition probabilities therefore
respect this flip. Elitism prevents mass from entering the region LO<j from
its complement, so a law symmetric there remains symmetric after a step.

Uniform initialization has this symmetry. Induction and the trajectory marginal
bridge prove it at every time, including zero-mass states. This is a verified
distribution invariant used by `ConditionalLevelLaw.lean`. The exact n^2/2
runtime under uniform initialization is proved in `ExactRuntime.lean`.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open ECTheoryLib.Problems.LeadingOnes

/-- Mutating an already established prefix position terminates the prefix there. -/
theorem PrefixFlipValue {n : ℕ} (x : Bits n) (i : Fin n) (Before : i.val < LeadingOnes x) :
    LeadingOnes (OnebitMutation x i) = i.val := by
  apply LeadingOnesEqOfPrefixAndZero _ i
  · intro j Earlier
    have Different : j ≠ i := by intro Equal; subst j; omega
    rw [OnebitMutationAway x i j Different]
    exact HasLeadingOnesPrefix x j (by omega)
  · rw [OnebitMutationAt, HasLeadingOnesPrefix x i Before]
    rfl

/-- Every bit strictly behind the first zero is neutral for this objective. -/
theorem SuffixFlipValue {n : ℕ} (x : Bits n) (j : Fin n) (After : LeadingOnes x < j.val) :
    LeadingOnes (OnebitMutation x j) = LeadingOnes x := by
  have Within : LeadingOnes x < n := After.trans j.isLt
  let i : Fin n := ⟨LeadingOnes x, Within⟩
  apply LeadingOnesEqOfPrefixAndZero _ i
  · intro k Before
    have Different : k ≠ j := by intro Equal; subst k; change j.val < LeadingOnes x at Before; omega
    rw [OnebitMutationAway x j k Different]
    exact HasLeadingOnesPrefix x k Before
  · have Different : i ≠ j := by
      intro Equal
      have Position := congrArg Fin.val Equal
      change LeadingOnes x = j.val at Position
      omega
    rw [OnebitMutationAway x j i Different]
    exact Problems.LOTZ.FirstZeroBit x Within

/-- Actual weak selection rejects exactly the positions before the first zero. -/
theorem UpdateByPosition {n : ℕ} (x : Bits n) (i : Fin n) :
    Update x i = if i.val < LeadingOnes x then x else OnebitMutation x i := by
  by_cases Before : i.val < LeadingOnes x
  · rw [if_pos Before]
    apply ElitistSelectReject
    change ¬ LeadingOnes x ≤ LeadingOnes (OnebitMutation x i)
    rw [PrefixFlipValue x i Before]
    omega
  · rw [if_neg Before]
    apply ElitistSelectAccept
    change LeadingOnes x ≤ LeadingOnes (OnebitMutation x i)
    by_cases Equal : i.val = LeadingOnes x
    · have Within : LeadingOnes x < n := by rw [← Equal]; exact i.isLt
      have Same : i = ⟨LeadingOnes x, Within⟩ := Fin.ext Equal
      rw [Same]
      exact (Nat.le_succ _).trans (FirstZeroFlipProgress x Within)
    · rw [SuffixFlipValue x i (by omega)]

/-- Flipping an unobserved suffix coordinate commutes with every actual RLS update. -/
theorem SuffixFlipUpdateCommutes {n : ℕ} (x : Bits n) (i j : Fin n)
    (After : LeadingOnes x < j.val) :
    Update (OnebitMutation x j) i = OnebitMutation (Update x i) j := by
  rw [UpdateByPosition, SuffixFlipValue x j After, UpdateByPosition]
  by_cases Before : i.val < LeadingOnes x
  · simp only [if_pos Before]
  · simp only [if_neg Before]
    exact OnebitMutationCommute x j i

/-- Every accepted update weakly increases fitness. -/
theorem UpdateFitnessNondecreasing {n : ℕ} (x : Bits n) (i : Fin n) :
    LeadingOnes x ≤ LeadingOnes (Update x i) := by
  have PotentialBound := SelectedPotentialLe x (OnebitMutation x i)
  have DeficitBound : Deficit (Update x i) ≤ Deficit x := Nat.cast_le.mp PotentialBound
  unfold Deficit at DeficitBound
  have ParentBound := LeadingOnesLeN x
  have ChildBound := LeadingOnesLeN (Update x i)
  omega

/-- Flipping coordinate j preserves every one prefix strictly before j. -/
theorem FlipPreservesEarlierPrefix {n : ℕ} (x : Bits n) (j : Fin n)
    (Before : j.val ≤ LeadingOnes x) : j.val ≤ LeadingOnes (OnebitMutation x j) := by
  apply PrefixLeLeadingOnes _ j.isLt.le
  intro i Earlier
  have Different : i ≠ j := by intro Equal; subst i; omega
  rw [OnebitMutationAway x j i Different]
  exact HasLeadingOnesPrefix x i (Earlier.trans_le Before)

/-- Equivariance holds even when the candidate leaves the old fitness level. -/
theorem StepSuffixFlipEquivariant {n : ℕ} (PositiveLength : 0 < n) (x y : Bits n) (j : Fin n)
    (After : LeadingOnes x < j.val) :
    Step PositiveLength (OnebitMutation x j) (OnebitMutation y j) = Step PositiveLength x y := by
  simp only [Step, RLSStepProbability]
  apply Finset.sum_congr rfl
  intro i _InUniv
  change (if Update (OnebitMutation x j) i = OnebitMutation y j then _ else _) = _
  rw [SuffixFlipUpdateCommutes x i j After]
  have Equal : OnebitMutation (Update x i) j = OnebitMutation y j ↔ Update x i = y := by
    constructor
    · intro Same
      have Flipped := congrArg (fun z => OnebitMutation z j) Same
      rw [OnebitMutationTwice, OnebitMutationTwice] at Flipped
      exact Flipped
    · intro Same
      rw [Same]
  simp only [Equal]

/-- Elitism gives zero transition mass to every strictly worse prefix level. -/
theorem StepCannotDecreaseFitness {n : ℕ} (PositiveLength : 0 < n) (x y : Bits n)
    (Worse : LeadingOnes y < LeadingOnes x) : Step PositiveLength x y = 0 := by
  rw [Step, RLSStepProbability]
  apply Finset.sum_eq_zero
  intro i _InUniv
  have Different : Update x i ≠ y := by
    intro Equal
    have Progress := UpdateFitnessNondecreasing x i
    rw [Equal] at Progress
    omega
  exact if_neg Different

/-- A point-mass formulation of unbiasedness of every unseen suffix bit. -/
def SuffixSymmetricLaw {n : ℕ} (p : PMF (Bits n)) : Prop :=
  ∀ (j : Fin n) (x : Bits n), LeadingOnes x < j.val → p (OnebitMutation x j) = p x

/-- Actual RLS selection preserves suffix symmetry; no source outside the
unobserved region can enter it because fitness never decreases. -/
theorem StepPreservesSuffixSymmetry {n : ℕ} (PositiveLength : 0 < n) (p : PMF (Bits n))
    (Symmetric : SuffixSymmetricLaw p) : SuffixSymmetricLaw (p.bind (Step PositiveLength)) := by
  intro j y AfterY
  rw [PMF.bind_apply, PMF.bind_apply, tsum_fintype, tsum_fintype]
  have Involution : Function.Involutive (fun x : Bits n => OnebitMutation x j) :=
    fun x => OnebitMutationTwice x j
  have Reindex := Involution.bijective.sum_comp
    (fun x => p x * Step PositiveLength x (OnebitMutation y j))
  rw [← Reindex]
  apply Finset.sum_congr rfl
  intro x _InUniv
  by_cases AfterX : LeadingOnes x < j.val
  · rw [Symmetric j x AfterX, StepSuffixFlipEquivariant PositiveLength x y j AfterX]
  · have OriginalZero : Step PositiveLength x y = 0 :=
      StepCannotDecreaseFitness PositiveLength x y (by omega)
    have FlippedBound := FlipPreservesEarlierPrefix x j (by omega)
    have FlippedZero : Step PositiveLength (OnebitMutation x j) (OnebitMutation y j) = 0 := by
      apply StepCannotDecreaseFitness
      rw [SuffixFlipValue y j AfterY]
      omega
    rw [OriginalZero, FlippedZero, mul_zero, mul_zero]

/-- At every iteration from uniform initialization, unseen suffix bits retain
the exact flip symmetry needed for their conditional distribution. -/
theorem UniformRunSuffixSymmetric {n : ℕ} (PositiveLength : 0 < n) (t : ℕ) :
    SuffixSymmetricLaw (ECTheoryLib.Probability.Evolve (Step PositiveLength) (RLSInit n) t) := by
  induction t with
  | zero =>
    intro j x _After
    change RLSInit n (OnebitMutation x j) = RLSInit n x
    rw [RLSInitProbability, RLSInitProbability]
  | succ t Before => exact StepPreservesSuffixSymmetry PositiveLength _ Before

end ECTheoryLib.Analysis.RLSOnLeadingOnes


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Exact point-mass symmetry on the full path law, with no positive-atom assumption. -/
theorem UniformPathSuffixMass {n : ℕ} (PositiveLength : 0 < n) (t : ℕ)
    (j : Fin n) (x : Bits n) (After : LeadingOnes x < j.val) :
    (PathMeasure (Step PositiveLength) (RLSInit n)) {Path | Path t = OnebitMutation x j} =
      (PathMeasure (Step PositiveLength) (RLSInit n)) {Path | Path t = x} := by
  have Left := PathMeasureCoordinateEvent (Step PositiveLength) (RLSInit n) t
    ({OnebitMutation x j} : Set (Bits n))
  have Right := PathMeasureCoordinateEvent (Step PositiveLength) (RLSInit n) t
    ({x} : Set (Bits n))
  simp only [Set.mem_singleton_iff] at Left Right
  rw [Left, Right, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact UniformRunSuffixSymmetric PositiveLength t j x After

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

