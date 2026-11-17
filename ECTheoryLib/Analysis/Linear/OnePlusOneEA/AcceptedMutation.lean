import ECTheoryLib.Analysis.Linear.OnePlusOneEA.RankPotential
import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Operators.Mutation.BitFlip
import ECTheoryLib.Probability.PMF.FinitePMF

/-! A one-coordinate estimate under the actual independent mutation law.
Finite pairing by the existing bit-flip involution avoids conditional
expectations on zero-mass events. The real weighting may be signed. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open scoped BigOperators unitInterval
noncomputable section

theorem ZeroCoordinateWeightedMean {n : ℕ} (p : I) (Parent : Bits n)
    (i : Fin n) (ParentZero : Parent i = false) (F : Bits n → ℝ)
    (Downward : ∀ y, y i = false → F (OnebitMutation y i) ≤ F y) :
    (∫ y, (if y i then (1 : ℝ) else 0)*F y
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) ≤
      (p : ℝ)*(∫ y, F y
        ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure) := by
  classical
  let q := fun y : Bits n =>
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent y).toReal
  let R := fun y : Bits n => ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    (BitMutationProbability (ENNReal.ofReal (p : ℝ)) (Parent j) (y j)).toReal
  have BitReal (b : Bool) :
      (BitMutationProbability (ENNReal.ofReal (p : ℝ)) (Parent i) b).toReal =
        if b then (p : ℝ) else 1-(p : ℝ) := by
    rw [ParentZero]
    cases b with
    | false =>
      change (1-ENNReal.ofReal (p : ℝ)).toReal = 1-(p : ℝ)
      rw [ENNReal.toReal_sub_of_le (MutationProbabilityBound p) ENNReal.one_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_ofReal p.2.1]
    | true =>
      change (ENNReal.ofReal (p : ℝ)).toReal = (p : ℝ)
      exact ENNReal.toReal_ofReal p.2.1
  have Split (y : Bits n) : q y = (if y i then (p : ℝ) else 1-(p : ℝ))*R y := by
    change (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent y).toReal = _
    rw [IndependentBitMutationProbability, ENNReal.toReal_prod,
      ← Finset.mul_prod_erase Finset.univ
        (fun j => (BitMutationProbability (ENNReal.ofReal (p : ℝ)) (Parent j) (y j)).toReal)
        (Finset.mem_univ i), BitReal]
  have RestNonnegative (y : Bits n) : 0 ≤ R y :=
    Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have RestFlip (y : Bits n) : R (OnebitMutation y i) = R y := by
    apply Finset.prod_congr rfl
    intro j Member
    rw [OnebitMutationAway y i j (Finset.mem_erase.mp Member).1]
  let D := fun y : Bits n => q y*((if y i then (1 : ℝ) else 0)-(p : ℝ))*F y
  have PairNonpositive (y : Bits n) : D y+D (OnebitMutation y i) ≤ 0 := by
    have Coefficient : 0 ≤ (p : ℝ)*(1-(p : ℝ))*R y :=
      mul_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (RestNonnegative y)
    cases Bit : y i with
    | false =>
      have Flip : OnebitMutation y i i = true := by rw [OnebitMutationAt, Bit]; rfl
      have Ordered := Downward y Bit
      calc
        D y+D (OnebitMutation y i) =
            (p : ℝ)*(1-(p : ℝ))*R y*(F (OnebitMutation y i)-F y) := by
          dsimp only [D]
          rw [Split y, Split (OnebitMutation y i), RestFlip]
          simp only [Bit, Flip, Bool.false_eq_true, if_false, if_true]
          ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos Coefficient (sub_nonpos.mpr Ordered)
    | true =>
      have Flip : OnebitMutation y i i = false := by rw [OnebitMutationAt, Bit]; rfl
      have Ordered := Downward (OnebitMutation y i) Flip
      rw [OnebitMutationTwice] at Ordered
      calc
        D y+D (OnebitMutation y i) =
            (p : ℝ)*(1-(p : ℝ))*R y*(F y-F (OnebitMutation y i)) := by
          dsimp only [D]
          rw [Split y, Split (OnebitMutation y i), RestFlip]
          simp only [Bit, Flip, Bool.false_eq_true, if_false, if_true]
          ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos Coefficient (sub_nonpos.mpr Ordered)
  let Swap : Equiv.Perm (Bits n) :=
    { toFun := fun y => OnebitMutation y i
      invFun := fun y => OnebitMutation y i
      left_inv := fun y => OnebitMutationTwice y i
      right_inv := fun y => OnebitMutationTwice y i }
  have SameSum : (∑ y : Bits n, D (OnebitMutation y i)) = ∑ y : Bits n, D y :=
    Equiv.sum_comp Swap D
  have SumNonpositive : (∑ y : Bits n, D y) ≤ 0 := by
    have Bound := Finset.sum_nonpos (s := (Finset.univ : Finset (Bits n)))
      (fun y _ => PairNonpositive y)
    rw [Finset.sum_add_distrib, SameSum] at Bound
    linarith
  have Expand : (∑ y : Bits n, D y) =
      (∑ y : Bits n, q y*((if y i then (1 : ℝ) else 0)*F y))-
        (p : ℝ)*(∑ y : Bits n, q y*F y) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [D]
    ring
  rw [Expand] at SumNonpositive
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  change (∑ y : Bits n, q y*((if y i then (1 : ℝ) else 0)*F y)) ≤
    (p : ℝ)*(∑ y : Bits n, q y*F y)
  linarith

theorem ZeroCoordinateEventProbability {n : ℕ} (p : I) (Parent : Bits n)
    (i : Fin n) (ParentZero : Parent i = false) (A : Set (Bits n))
    (Downward : ∀ y, y i = false → OnebitMutation y i ∈ A → y ∈ A) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | y i = true ∧ y ∈ A} ≤
      (p : ℝ)*(IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) Parent).toMeasure.real A := by
  classical
  have Weighted := ZeroCoordinateWeightedMean p Parent i ParentZero (A.indicator (fun _ => (1 : ℝ))) (by
    intro y Zero
    by_cases InFlip : OnebitMutation y i ∈ A
    · rw [Set.indicator_of_mem InFlip, Set.indicator_of_mem (Downward y Zero InFlip)]
    · rw [Set.indicator_of_notMem InFlip]
      by_cases InA : y ∈ A
      · rw [Set.indicator_of_mem InA]
        norm_num
      · rw [Set.indicator_of_notMem InA])
  have Product : (fun y => (if y i then (1 : ℝ) else 0)*A.indicator (fun _ => (1 : ℝ)) y) =
      {y : Bits n | y i = true ∧ y ∈ A}.indicator (fun _ => (1 : ℝ)) := by
    funext y
    cases Bit : y i <;> simp [Set.indicator, Bit]
  rw [Product] at Weighted
  have Left := integral_indicator_const
    (μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)
    (1 : ℝ) (s := {y : Bits n | y i = true ∧ y ∈ A}) (Set.to_countable _).measurableSet
  have Right := integral_indicator_const
    (μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure)
    (1 : ℝ) (s := A) (Set.to_countable _).measurableSet
  rw [Left, Right] at Weighted
  simpa only [smul_eq_mul, mul_one] using Weighted

theorem AcceptanceDownwardAtZero {n : ℕ} (Weights : Fin n → ℝ)
    (Parent Candidate : Bits n) (i : Fin n) (WeightNonnegative : 0 ≤ Weights i)
    (CandidateZero : Candidate i = false)
    (AcceptedFlip : Score Weights (OnebitMutation Candidate i) ≤ Score Weights Parent) :
    Score Weights Candidate ≤ Score Weights Parent := by
  have Difference := RLSLinear.MutationScoreDifference Weights Candidate i
  rw [CandidateZero, if_neg Bool.false_ne_true] at Difference
  linarith

theorem FlippedOnesUnchangedAtParentZero {n : ℕ} (Parent Candidate : Bits n)
    (i : Fin n) (ParentZero : Parent i = false) :
    FlippedOnes Parent (OnebitMutation Candidate i) = FlippedOnes Parent Candidate := by
  unfold FlippedOnes
  apply Finset.sum_congr rfl
  intro j _
  by_cases Same : j = i
  · subst j
    simp only [ParentZero, Bool.false_eq_true, if_false]
  · rw [OnebitMutationAway Candidate i j Same]

/-- A concrete accepted downward-count branch discharges coordinate closure.
Taking k=2 gives the multiple-downward branch in the sorted-rank proof. -/
theorem AcceptedFlippedOnesCoordinateProbability {n : ℕ} (p : I) (Weights : Fin n → ℝ)
    (Parent : Bits n) (i : Fin n) (ParentZero : Parent i = false)
    (WeightNonnegative : 0 ≤ Weights i) (k : ℕ) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | y i = true ∧ Score Weights y ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent y} ≤
      (p : ℝ)*(IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) Parent).toMeasure.real
          {y | Score Weights y ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent y} := by
  apply ZeroCoordinateEventProbability p Parent i ParentZero
    {y | Score Weights y ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent y}
  intro Candidate Zero Member
  refine ⟨AcceptanceDownwardAtZero Weights Parent Candidate i WeightNonnegative Zero Member.1, ?_⟩
  have Count := Member.2
  rwa [FlippedOnesUnchangedAtParentZero Parent Candidate i ParentZero] at Count

/-- The existing removal count is the cardinality of its actual index set. -/
theorem FlippedOnesEqCard {n : ℕ} (Parent Candidate : Bits n) :
    FlippedOnes Parent Candidate =
      (Finset.univ.filter (fun i : Fin n => Parent i = true ∧ Candidate i = false)).card := by
  rw [Finset.card_filter]
  unfold FlippedOnes
  apply Finset.sum_congr rfl
  intro i _
  cases Parent i <;> cases Candidate i <;> simp

theorem FlippedOnesZeroIff {n : ℕ} (Parent Candidate : Bits n) :
    FlippedOnes Parent Candidate = 0 ↔ ∀ i, Parent i = true → Candidate i = true := by
  constructor
  · intro Zero i ParentOne
    unfold FlippedOnes at Zero
    have Term := (Finset.sum_eq_zero_iff.mp Zero) i (Finset.mem_univ i)
    rw [ParentOne] at Term
    change (if Candidate i then (0 : ℕ) else 1) = 0 at Term
    cases CandidateBit : Candidate i with
    | false => simp [CandidateBit] at Term
    | true => rfl
  · intro Preserves
    unfold FlippedOnes
    apply Finset.sum_eq_zero
    intro i _
    cases ParentBit : Parent i with
    | false => rfl
    | true => simp [Preserves i ParentBit]

theorem FlippedOnesOneIff {n : ℕ} (Parent Candidate : Bits n) :
    FlippedOnes Parent Candidate = 1 ↔
      ∃ i, Parent i = true ∧ Candidate i = false ∧
        ∀ j, j ≠ i → Parent j = true → Candidate j = true := by
  rw [FlippedOnesEqCard, Finset.card_eq_one]
  constructor
  · rintro ⟨i, Singleton⟩
    have Member : i ∈ Finset.univ.filter (fun j : Fin n => Parent j = true ∧ Candidate j = false) := by
      rw [Singleton]
      exact Finset.mem_singleton_self i
    have Bits := (Finset.mem_filter.mp Member).2
    refine ⟨i, Bits.1, Bits.2, ?_⟩
    intro j Different ParentOne
    cases CandidateBit : Candidate j with
    | true => rfl
    | false =>
      have MemberJ : j ∈ Finset.univ.filter (fun a : Fin n => Parent a = true ∧ Candidate a = false) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, ParentOne, CandidateBit⟩
      rw [Singleton, Finset.mem_singleton] at MemberJ
      exact False.elim (Different MemberJ)
  · rintro ⟨i, ParentOne, CandidateZero, Unique⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨ParentJ, CandidateJ⟩
      by_contra Different
      have Kept := Unique j Different ParentJ
      rw [CandidateJ] at Kept
      cases Kept
    · intro Equal
      subst j
      exact ⟨ParentOne, CandidateZero⟩

/-- With no parent-one removed, weak acceptance and strictly positive weights
force the original candidate to equal its parent. Score is not assumed injective. -/
theorem AcceptedWithoutRemovalEqParent {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (Parent Candidate : Bits n)
    (NoRemoval : FlippedOnes Parent Candidate = 0)
    (Accepted : Score Weights Candidate ≤ Score Weights Parent) : Candidate = Parent := by
  have Preserves := (FlippedOnesZeroIff Parent Candidate).mp NoRemoval
  have TermNonnegative (i : Fin n) :
      0 ≤ Weights i*(if Candidate i then (1 : ℝ) else 0)-
        Weights i*(if Parent i then (1 : ℝ) else 0) := by
    cases ParentBit : Parent i with
    | false => cases Candidate i <;> simp [(Positive i).le]
    | true => simp [Preserves i ParentBit]
  have SumZero : (∑ i : Fin n, (Weights i*(if Candidate i then (1 : ℝ) else 0)-
      Weights i*(if Parent i then (1 : ℝ) else 0))) = 0 := by
    apply le_antisymm
    · rw [Finset.sum_sub_distrib]
      exact sub_nonpos.mpr Accepted
    · exact Finset.sum_nonneg (fun i _ => TermNonnegative i)
  have TermsZero (i : Fin n) : Weights i*(if Candidate i then (1 : ℝ) else 0)-
      Weights i*(if Parent i then (1 : ℝ) else 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => TermNonnegative j)).mp SumZero i (Finset.mem_univ i)
  funext i
  cases ParentBit : Parent i with
  | true => exact Preserves i ParentBit
  | false =>
    cases CandidateBit : Candidate i with
    | false => rfl
    | true =>
      have Term := TermsZero i
      simp only [CandidateBit, ParentBit, if_true, Bool.false_eq_true, if_false,
        mul_one, mul_zero, sub_zero] at Term
      exact False.elim ((ne_of_gt (Positive i)) Term)

/-- Rejection also has zero displacement, so the complete zero-removal branch
of the actual weak selector retains the parent. -/
theorem SelectWithoutRemovalEqParent {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ i, 0 < Weights i) (Parent Candidate : Bits n)
    (NoRemoval : FlippedOnes Parent Candidate = 0) :
    ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate = Parent := by
  by_cases Accepted : Score Weights Candidate ≤ Score Weights Parent
  · rw [ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent Candidate Accepted]
    exact AcceptedWithoutRemovalEqParent Weights Positive Parent Candidate NoRemoval Accepted
  · exact ElitistSelectReject (Problems.MinNotWorse (Score Weights)) Parent Candidate Accepted

end
end ECTheoryLib.Analysis.EALinearMinimization

