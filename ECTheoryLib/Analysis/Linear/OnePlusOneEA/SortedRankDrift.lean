import ECTheoryLib.Analysis.Linear.OnePlusOneEA.AcceptedMutation

/-! Complete selected rank drift for sorted positive linear objectives.
The multiple-removal branch needs no ordering. Actual unique-removal
events include a possibly negative equal-weight swap branch. Their exact
partition proves the entire original kernel's G/(4en) lower drift bound. -/
namespace ECTheoryLib.Analysis.EALinearMinimization
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.Linear
open scoped BigOperators unitInterval
noncomputable section

def RemovedRank {n : ℕ} (Parent Candidate : Bits n) : ℝ :=
  ∑ i : Fin n, (if Parent i then RankWeight i else 0)*(if Candidate i then 0 else 1)

def AddedRank {n : ℕ} (Parent Candidate : Bits n) : ℝ :=
  ∑ i : Fin n, (if Parent i then 0 else RankWeight i)*(if Candidate i then 1 else 0)

theorem RankDifferenceByRemovedAdded {n : ℕ} (Parent Candidate : Bits n) :
    RankPotential Parent-RankPotential Candidate = RemovedRank Parent Candidate-AddedRank Parent Candidate := by
  unfold RankPotential Score RemovedRank AddedRank
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases Parent i <;> cases Candidate i <;> simp

theorem RemovedRankGeFlippedOnes {n : ℕ} (Parent Candidate : Bits n) :
    (FlippedOnes Parent Candidate : ℝ) ≤ RemovedRank Parent Candidate := by
  unfold FlippedOnes RemovedRank
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  cases Parent i <;> cases Candidate i <;> simp [RankWeightOneLe]

theorem ZeroRankWeightSumLeTwoN {n : ℕ} (Parent : Bits n) :
    (∑ i : Fin n, if Parent i then (0 : ℝ) else RankWeight i) ≤ 2*(n : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases Parent i <;> simp [RankWeightLeTwo]
    _ = 2*(n : ℝ) := by simp [mul_comm]

/-- Unnormalized contribution of the true accepted >=k-removal branch.
All coordinate closure conditions are proved from the objective/mutation. -/
theorem AcceptedManyDownwardContributionLowerBound {n : ℕ} (p : I)
    (Weights : Fin n → ℝ) (WeightsNonnegative : ∀ i, 0 ≤ Weights i) (Parent : Bits n) (k : ℕ) :
    ((k : ℝ)-(p : ℝ)*(∑ i : Fin n, if Parent i then (0 : ℝ) else RankWeight i))*
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
        {y | Score Weights y ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent y} ≤
    ∫ y, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent z}.indicator
      (fun z => RankPotential Parent-RankPotential z) y
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  classical
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let A : Set (Bits n) := {y | Score Weights y ≤ Score Weights Parent ∧ k ≤ FlippedOnes Parent y}
  let F := A.indicator (fun _ => (1 : ℝ))
  let Z := fun i : Fin n => if Parent i then (0 : ℝ) else RankWeight i
  have MeanCoordinate (i : Fin n) :
      (∫ y, (if y i then (1 : ℝ) else 0)*F y ∂μ) = μ.real {y | y i = true ∧ y ∈ A} := by
    have Product : (fun y => (if y i then (1 : ℝ) else 0)*F y) =
        {y : Bits n | y i = true ∧ y ∈ A}.indicator (fun _ => (1 : ℝ)) := by
      funext y
      cases Bit : y i <;> simp [F, Set.indicator, Bit]
    rw [Product]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := μ) (1 : ℝ)
        (s := {y : Bits n | y i = true ∧ y ∈ A}) (Set.to_countable _).measurableSet)
  have CoordinateBound (i : Fin n) :
      Z i*(∫ y, (if y i then (1 : ℝ) else 0)*F y ∂μ) ≤ (p : ℝ)*Z i*μ.real A := by
    rw [MeanCoordinate]
    cases ParentBit : Parent i with
    | false =>
      have ProbabilityBound : μ.real {y | y i = true ∧ y ∈ A} ≤ (p : ℝ)*μ.real A :=
        AcceptedFlippedOnesCoordinateProbability p Weights Parent i ParentBit (WeightsNonnegative i) k
      dsimp only [Z]
      rw [ParentBit]
      simp only [Bool.false_eq_true, if_false]
      calc
        _ ≤ RankWeight i*((p : ℝ)*μ.real A) :=
          mul_le_mul_of_nonneg_left ProbabilityBound (RankWeightPositive i).le
        _ = _ := by ring
    | true => simp [Z, ParentBit]
  have AddedMean : (∫ y, A.indicator (AddedRank Parent) y ∂μ) ≤
      (p : ℝ)*(∑ i : Fin n, Z i)*μ.real A := by
    have Functions : (fun y => A.indicator (AddedRank Parent) y) =
        fun y => ∑ i : Fin n, Z i*((if y i then (1 : ℝ) else 0)*F y) := by
      funext y
      by_cases Member : y ∈ A
      · simp only [F, Set.indicator_of_mem Member, mul_one, AddedRank, Z]
      · simp only [F, Set.indicator_of_notMem Member, mul_zero, Finset.sum_const_zero]
    calc
      _ = ∑ i : Fin n, Z i*(∫ y, (if y i then (1 : ℝ) else 0)*F y ∂μ) := by
        rw [Functions, integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
        simp_rw [integral_const_mul]
      _ ≤ ∑ i : Fin n, (p : ℝ)*Z i*μ.real A :=
        Finset.sum_le_sum (fun i _ => CoordinateBound i)
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  have Pointwise (y : Bits n) : (k : ℝ)*F y-A.indicator (AddedRank Parent) y ≤
      A.indicator (fun z => RankPotential Parent-RankPotential z) y := by
    by_cases Member : y ∈ A
    · simp only [F, Set.indicator_of_mem Member, mul_one]
      have Count : (k : ℝ) ≤ (FlippedOnes Parent y : ℝ) := Nat.cast_le.mpr Member.2
      have Removed := RemovedRankGeFlippedOnes Parent y
      have Difference := RankDifferenceByRemovedAdded Parent y
      linarith
    · simp [F, Set.indicator, Member]
  have IntegralLower := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite Pointwise
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul] at IntegralLower
  have MeanF : (∫ y, F y ∂μ) = μ.real A := by
    simpa only [F, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := μ) (1 : ℝ) (s := A) (Set.to_countable _).measurableSet)
  rw [MeanF] at IntegralLower
  change ((k : ℝ)-(p : ℝ)*(∑ i : Fin n, Z i))*μ.real A ≤
    ∫ y, A.indicator (fun z => RankPotential Parent-RankPotential z) y ∂μ
  calc
    _ = (k : ℝ)*μ.real A-((p : ℝ)*(∑ i : Fin n, Z i)*μ.real A) := by ring
    _ ≤ (k : ℝ)*μ.real A-(∫ y, A.indicator (AddedRank Parent) y ∂μ) :=
      sub_le_sub_left AddedMean _
    _ ≤ _ := IntegralLower

/-- For rate at most1/n the complete multiple-downward branch is nonnegative.
No event-positive-mass or accepted-bit-independence premise occurs. -/
theorem AcceptedMultipleDownwardContributionNonnegative {n : ℕ} (p : I)
    (RateLengthBound : (p : ℝ)*(n : ℝ) ≤ 1)
    (Weights : Fin n → ℝ) (WeightsNonnegative : ∀ i, 0 ≤ Weights i) (Parent : Bits n) :
    0 ≤ ∫ y, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}.indicator
      (fun z => RankPotential Parent-RankPotential z) y
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  have Lower := AcceptedManyDownwardContributionLowerBound p Weights WeightsNonnegative Parent 2
  have ProductBound := mul_le_mul_of_nonneg_left (ZeroRankWeightSumLeTwoN Parent) p.2.1
  have Coefficient : 0 ≤ 2-(p : ℝ)*(∑ i : Fin n, if Parent i then (0 : ℝ) else RankWeight i) := by
    nlinarith
  exact (mul_nonneg Coefficient ENNReal.toReal_nonneg).trans Lower

/-- The standard1/n mutation and actual weak selection have nonnegative C3
contribution. The event records raw removals before the stated selection. -/
theorem StandardMultipleDownwardContributionNonnegative {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (WeightsNonnegative : ∀ i, 0 ≤ Weights i) (Parent : Bits n) :
    0 ≤ ∫ y, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}.indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  classical
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨div_nonneg (by norm_num) PositiveN.le,
    (div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have RateLengthBound : (p : ℝ)*(n : ℝ) ≤ 1 := by
    change (1/(n : ℝ))*(n : ℝ) ≤ 1
    exact (div_mul_cancel₀ (1 : ℝ) (ne_of_gt PositiveN)).le
  have Bound := AcceptedMultipleDownwardContributionNonnegative p RateLengthBound Weights WeightsNonnegative Parent
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  simp only [Rate] at Bound
  change 0 ≤ ∫ y, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}.indicator
    (fun z => RankPotential Parent-RankPotential z) y ∂(StandardBitMutation PositiveLength Parent).toMeasure at Bound
  let A : Set (Bits n) := {z | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}
  have Equal : (fun y => A.indicator (fun z => RankPotential Parent-
      RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y) =
      fun y => A.indicator (fun z => RankPotential Parent-RankPotential z) y := by
    funext y
    by_cases Member : y ∈ A
    · simp only [Set.indicator_of_mem Member]
      rw [ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent y Member.1]
    · simp only [Set.indicator_of_notMem Member]
  change 0 ≤ ∫ y, A.indicator (fun z => RankPotential Parent-
    RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure
  rw [Equal]
  exact Bound

/-- Even with sorted positive weights, the C3 branch can have a negative
rank decrement at a strictly improving, positive-probability transition.
The nonnegative contribution theorem is an expectation statement. -/
theorem ExistsNegativeStandardMultipleDownwardPoint :
    ∃ (Weights : Fin 6 → ℝ) (Parent Candidate : Bits 6),
      (∀ i, 0 < Weights i) ∧ Monotone Weights ∧
      FlippedOnes Parent Candidate = 2 ∧ Score Weights Candidate < Score Weights Parent ∧
      ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate = Candidate ∧
      (Step (by decide : 0 < 6) Weights Parent Candidate).toReal = (1 : ℝ)/46656 ∧
      0 < Step (by decide : 0 < 6) Weights Parent Candidate ∧
      RankPotential Parent-RankPotential Candidate = -(11 : ℝ)/6 := by
  classical
  let Weights : Fin 6 → ℝ := fun i => if i.val < 4 then 1 else 10
  let Parent : Bits 6 := fun i => decide (4 ≤ i.val)
  let Candidate : Bits 6 := fun i => decide (i.val < 4)
  have Positive : ∀ i, 0 < Weights i := by
    intro i
    dsimp only [Weights]
    split_ifs <;> norm_num
  have Sorted : Monotone Weights := by
    intro i j Ordered
    have Values : i.val ≤ j.val := Ordered
    dsimp only [Weights]
    split_ifs <;> norm_num
    omega
  have Removed : FlippedOnes Parent Candidate = 2 := by
    norm_num [FlippedOnes, Parent, Candidate, Fin.sum_univ_succ]
  have Better : Score Weights Candidate < Score Weights Parent := by
    norm_num [Score, Weights, Parent, Candidate, Fin.sum_univ_succ]
  have Different : Candidate ≠ Parent := by
    intro Equal
    exact (ne_of_lt Better) (congrArg (Score Weights) Equal)
  have Changes : BitDifferenceCount Parent Candidate = 6 := by decide
  have Probability : (Step (by decide : 0 < 6) Weights Parent Candidate).toReal = (1 : ℝ)/46656 := by
    rw [StepAcceptedProbability (by decide : 0 < 6) Weights Parent Candidate Different Better.le,
      StandardBitMutationPatternReal, Changes]
    norm_num
  have Negative : RankPotential Parent-RankPotential Candidate = -(11 : ℝ)/6 := by
    norm_num [RankPotential, Score, RankWeight, Parent, Candidate, Fin.sum_univ_succ]
  refine ⟨Weights, Parent, Candidate, Positive, Sorted, Removed, Better, ?_, Probability, ?_, Negative⟩
  · exact ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent Candidate Better.le
  · exact StepAcceptedProbabilityPositive (by decide : 0 < 6) (by decide) Weights Parent Candidate Different Better.le

/-- Exactly the marked parent-one is removed; parent-zero changes are free. -/
def SingleDownwardAt {n : ℕ} (Parent : Bits n) (i : Fin n) (Candidate : Bits n) : Prop :=
  Parent i = true ∧ Candidate i = false ∧
    ∀ j, j ≠ i → Parent j = true → Candidate j = true

def LowerSingleDownwardEvent {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n)
    (i : Fin n) : Set (Bits n) :=
  {y | Score Weights y ≤ Score Weights Parent ∧ SingleDownwardAt Parent i y ∧
    ∀ j, i < j → Parent j = false → y j = false}

def HigherSingleDownwardEvent {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n)
    (i : Fin n) : Set (Bits n) :=
  {y | Score Weights y ≤ Score Weights Parent ∧ SingleDownwardAt Parent i y ∧
    ∃ j, i < j ∧ Parent j = false ∧ y j = true}

theorem SingleDownwardAtIff {n : ℕ} (Parent Candidate : Bits n) (i : Fin n) :
    SingleDownwardAt Parent i Candidate ↔
      Parent i = true ∧ Candidate i = false ∧ FlippedOnes Parent Candidate = 1 := by
  constructor
  · intro Member
    exact ⟨Member.1, Member.2.1, (FlippedOnesOneIff Parent Candidate).mpr ⟨i, Member⟩⟩
  · rintro ⟨ParentOne, CandidateZero, Count⟩
    rcases (FlippedOnesOneIff Parent Candidate).mp Count with ⟨j, _, _, Others⟩
    have Same : i = j := by
      by_contra Different
      have Kept := Others i Different ParentOne
      rw [CandidateZero] at Kept
      cases Kept
    subst j
    exact ⟨ParentOne, CandidateZero, Others⟩

theorem SingleDownwardAtUnique {n : ℕ} (Parent Candidate : Bits n) (i j : Fin n)
    (First : SingleDownwardAt Parent i Candidate) (Second : SingleDownwardAt Parent j Candidate) :
    i = j := by
  by_contra Different
  have Kept := First.2.2 j (Ne.symm Different) Second.1
  rw [Second.2.1] at Kept
  cases Kept

theorem SingleDownwardAtFlipZero {n : ℕ} (Parent Candidate : Bits n) (i j : Fin n)
    (Different : i ≠ j) (ParentZero : Parent j = false) :
    SingleDownwardAt Parent i (OnebitMutation Candidate j) ↔ SingleDownwardAt Parent i Candidate := by
  rw [SingleDownwardAtIff, SingleDownwardAtIff,
    OnebitMutationAway Candidate j i Different,
    FlippedOnesUnchangedAtParentZero Parent Candidate j ParentZero]

theorem LowerSingleDownwardKeepsHigher {n : ℕ} (Weights : Fin n → ℝ) (Parent Candidate : Bits n)
    (i : Fin n) (Member : Candidate ∈ LowerSingleDownwardEvent Weights Parent i)
    (j : Fin n) (Above : i < j) : Candidate j = Parent j := by
  cases ParentBit : Parent j with
  | false => exact Member.2.2 j Above ParentBit
  | true => exact Member.2.1.2.2 j (ne_of_gt Above) ParentBit

/-- Only allowed lower zero coordinates enter the Ai loss estimate;
the full acceptance and branch-closure conditions are actually discharged. -/
theorem LowerSingleDownwardCoordinateProbability {n : ℕ} (p : I) (Weights : Fin n → ℝ)
    (Parent : Bits n) (i j : Fin n) (Below : j < i) (ParentZero : Parent j = false)
    (WeightNonnegative : 0 ≤ Weights j) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
      {y | y j = true ∧ y ∈ LowerSingleDownwardEvent Weights Parent i} ≤
      (p : ℝ)*(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
        (LowerSingleDownwardEvent Weights Parent i) := by
  apply ZeroCoordinateEventProbability p Parent j ParentZero (LowerSingleDownwardEvent Weights Parent i)
  intro Candidate Zero Member
  refine ⟨AcceptanceDownwardAtZero Weights Parent Candidate j WeightNonnegative Zero Member.1, ?_, ?_⟩
  · exact (SingleDownwardAtFlipZero Parent Candidate i j (ne_of_gt Below) ParentZero).mp Member.2.1
  · intro a Above ParentA
    have Unchanged := Member.2.2 a Above ParentA
    rwa [OnebitMutationAway Candidate j a (ne_of_gt (Below.trans Above))] at Unchanged

theorem SingleDownwardEventsPartition {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n) (i : Fin n) :
    LowerSingleDownwardEvent Weights Parent i ∪ HigherSingleDownwardEvent Weights Parent i =
      {y | Score Weights y ≤ Score Weights Parent ∧ SingleDownwardAt Parent i y} := by
  classical
  ext Candidate
  constructor
  · intro Member
    rcases Member with Lower | Higher
    · exact ⟨Lower.1, Lower.2.1⟩
    · exact ⟨Higher.1, Higher.2.1⟩
  · intro Member
    by_cases NoHigher : ∀ j, i < j → Parent j = false → Candidate j = false
    · exact Or.inl ⟨Member.1, Member.2, NoHigher⟩
    · apply Or.inr
      refine ⟨Member.1, Member.2, ?_⟩
      push Not at NoHigher
      rcases NoHigher with ⟨j, Above, ParentZero, NotFalse⟩
      refine ⟨j, Above, ParentZero, ?_⟩
      cases CandidateBit : Candidate j with
      | true => rfl
      | false => exact False.elim (NotFalse CandidateBit)

theorem SingleDownwardEventsDisjoint {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n) (i : Fin n) :
    Disjoint (LowerSingleDownwardEvent Weights Parent i) (HigherSingleDownwardEvent Weights Parent i) := by
  refine Set.disjoint_left.mpr ?_
  intro Candidate Lower Higher
  rcases Higher.2.2 with ⟨j, Above, ParentZero, CandidateOne⟩
  have CandidateZero := Lower.2.2 j Above ParentZero
  rw [CandidateOne] at CandidateZero
  cases CandidateZero

/-- Strict positivity in the zero-removal selector theorem is essential.
With zero objective weights, the actual one-bit standard EA accepts a tie
and moves with probability one without removing any parent-one bit. -/
theorem ExistsZeroWeightSelectedChangeWithoutRemoval :
    ∃ Parent Candidate : Bits 1,
      Candidate ≠ Parent ∧ FlippedOnes Parent Candidate = 0 ∧
      Score (fun _ => (0 : ℝ)) Candidate = Score (fun _ => (0 : ℝ)) Parent ∧
      ElitistSelect (Problems.MinNotWorse (Score (fun _ => (0 : ℝ)))) Parent Candidate = Candidate ∧
      (Step (by decide : 0 < 1) (fun _ => (0 : ℝ)) Parent Candidate).toReal = 1 := by
  let Parent : Bits 1 := fun _ => false
  let Candidate : Bits 1 := fun _ => true
  have Different : Candidate ≠ Parent := by
    intro Equal
    have Bit := congrFun Equal (0 : Fin 1)
    change true = false at Bit
    cases Bit
  have Accepted : Score (fun _ => (0 : ℝ)) Candidate ≤ Score (fun _ => (0 : ℝ)) Parent := by
    simp only [ScoreZeroWeights, le_refl]
  have Changes : BitDifferenceCount Parent Candidate = 1 := by decide
  refine ⟨Parent, Candidate, Different, ?_, ?_, ?_, ?_⟩
  · simp [FlippedOnes, Parent]
  · simp only [ScoreZeroWeights]
  · exact ElitistSelectAccept (Problems.MinNotWorse (Score (fun _ => (0 : ℝ)))) Parent Candidate Accepted
  · rw [StepAcceptedProbability (by decide : 0 < 1) (fun _ => (0 : ℝ)) Parent Candidate Different Accepted,
      StandardBitMutationPatternReal, Changes]
    norm_num

theorem RemovedRankOfSingleDownward {n : ℕ} (Parent Candidate : Bits n) (i : Fin n)
    (Member : SingleDownwardAt Parent i Candidate) : RemovedRank Parent Candidate = RankWeight i := by
  unfold RemovedRank
  rw [Finset.sum_eq_single i]
  · simp [Member.1, Member.2.1]
  · intro j _ Different
    cases ParentBit : Parent j with
    | false => simp
    | true => simp [Member.2.2 j Different ParentBit]
  · intro Absent
    exact False.elim (Absent (Finset.mem_univ i))

theorem AddedRankOfLowerSingleDownward {n : ℕ} (Weights : Fin n → ℝ) (Parent Candidate : Bits n)
    (i : Fin n) (Member : Candidate ∈ LowerSingleDownwardEvent Weights Parent i) :
    AddedRank Parent Candidate = ∑ j : Fin n,
      (if j < i then (if Parent j then (0 : ℝ) else RankWeight j) else 0)*(if Candidate j then 1 else 0) := by
  unfold AddedRank
  apply Finset.sum_congr rfl
  intro j _
  by_cases Below : j < i
  · simp only [Below, if_true]
  · simp only [Below, if_false, zero_mul]
    cases ParentBit : Parent j with
    | true => simp
    | false =>
      have CandidateZero : Candidate j = false := by
        by_cases Same : j = i
        · subst j
          exact Member.2.1.2.1
        · have Above : i < j := by omega
          rw [LowerSingleDownwardKeepsHigher Weights Parent Candidate i Member j Above]
          exact ParentBit
      simp [CandidateZero]

theorem LowerSingleDownwardContainsOneBit {n : ℕ} (Weights : Fin n → ℝ) (Parent : Bits n)
    (i : Fin n) (ParentOne : Parent i = true) (WeightNonnegative : 0 ≤ Weights i) :
    OnebitMutation Parent i ∈ LowerSingleDownwardEvent Weights Parent i := by
  have Difference : Score Weights Parent-Score Weights (OnebitMutation Parent i) = Weights i := by
    simpa [ParentOne] using (RLSLinear.MutationScoreDifference Weights Parent i)
  refine ⟨by linarith, ⟨ParentOne, ?_, ?_⟩, ?_⟩
  · rw [OnebitMutationAt, ParentOne]
    rfl
  · intro j Different ParentJ
    rw [OnebitMutationAway Parent i j Different]
    exact ParentJ
  · intro j Above ParentJ
    rw [OnebitMutationAway Parent i j (ne_of_gt Above)]
    exact ParentJ

theorem StandardLowerSingleDownwardProbabilityLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Parent : Bits n) (i : Fin n)
    (ParentOne : Parent i = true) (WeightNonnegative : 0 ≤ Weights i) :
    StandardOneBitProbability n ≤
      (StandardBitMutation PositiveLength Parent).toMeasure.real (LowerSingleDownwardEvent Weights Parent i) := by
  have PointMass : (StandardBitMutation PositiveLength Parent).toMeasure.real {OnebitMutation Parent i} =
      StandardOneBitProbability n := by
    change ((StandardBitMutation PositiveLength Parent).toMeasure {OnebitMutation Parent i}).toReal = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact StandardBitMutationOneBitReal PositiveLength Parent i
  rw [← PointMass]
  exact measureReal_mono (Set.singleton_subset_iff.mpr
    (LowerSingleDownwardContainsOneBit Weights Parent i ParentOne WeightNonnegative)) (measure_ne_top _ _)

/-- Actual selected Ai contribution, before specializing the mutation rate.
The removed rank is exact and only lower parent-zero coordinates can add rank. -/
theorem LowerSingleDownwardRankMeanLowerBound {n : ℕ} (p : I) (Weights : Fin n → ℝ)
    (WeightsNonnegative : ∀ j, 0 ≤ Weights j) (Parent : Bits n) (i : Fin n) :
    (RankWeight i-(p : ℝ)*(∑ j : Fin n, if j < i then RankWeight j else 0))*
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure.real
        (LowerSingleDownwardEvent Weights Parent i) ≤
    ∫ y, (LowerSingleDownwardEvent Weights Parent i).indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure := by
  classical
  let μ := (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) Parent).toMeasure
  let A := LowerSingleDownwardEvent Weights Parent i
  let F := A.indicator (fun _ => (1 : ℝ))
  let Z := fun j : Fin n => if j < i then (if Parent j then (0 : ℝ) else RankWeight j) else 0
  have MeanCoordinate (j : Fin n) :
      (∫ y, (if y j then (1 : ℝ) else 0)*F y ∂μ) = μ.real {y | y j = true ∧ y ∈ A} := by
    have Product : (fun y => (if y j then (1 : ℝ) else 0)*F y) =
        {y : Bits n | y j = true ∧ y ∈ A}.indicator (fun _ => (1 : ℝ)) := by
      funext y
      cases Bit : y j <;> simp [F, Set.indicator, Bit]
    rw [Product]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := μ) (1 : ℝ)
        (s := {y : Bits n | y j = true ∧ y ∈ A}) (Set.to_countable _).measurableSet)
  have CoordinateBound (j : Fin n) :
      Z j*(∫ y, (if y j then (1 : ℝ) else 0)*F y ∂μ) ≤ (p : ℝ)*Z j*μ.real A := by
    rw [MeanCoordinate]
    by_cases Below : j < i
    · cases ParentBit : Parent j with
      | false =>
        have ProbabilityBound : μ.real {y | y j = true ∧ y ∈ A} ≤ (p : ℝ)*μ.real A :=
          LowerSingleDownwardCoordinateProbability p Weights Parent i j Below ParentBit (WeightsNonnegative j)
        simp only [Z, Below, if_true, ParentBit, Bool.false_eq_true, if_false]
        calc
          _ ≤ RankWeight j*((p : ℝ)*μ.real A) :=
            mul_le_mul_of_nonneg_left ProbabilityBound (RankWeightPositive j).le
          _ = _ := by ring
      | true => simp [Z, Below, ParentBit]
    · simp [Z, Below]
  have AddedMean : (∫ y, A.indicator (AddedRank Parent) y ∂μ) ≤
      (p : ℝ)*(∑ j : Fin n, Z j)*μ.real A := by
    have Functions : (fun y => A.indicator (AddedRank Parent) y) =
        fun y => ∑ j : Fin n, Z j*((if y j then (1 : ℝ) else 0)*F y) := by
      funext y
      by_cases Member : y ∈ A
      · simp only [F, Set.indicator_of_mem Member, mul_one]
        exact AddedRankOfLowerSingleDownward Weights Parent y i Member
      · simp only [F, Set.indicator_of_notMem Member, mul_zero, Finset.sum_const_zero]
    calc
      _ = ∑ j : Fin n, Z j*(∫ y, (if y j then (1 : ℝ) else 0)*F y ∂μ) := by
        rw [Functions, integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
        simp_rw [integral_const_mul]
      _ ≤ ∑ j : Fin n, (p : ℝ)*Z j*μ.real A :=
        Finset.sum_le_sum (fun j _ => CoordinateBound j)
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  have ZBound : (∑ j : Fin n, Z j) ≤ ∑ j : Fin n, if j < i then RankWeight j else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases Below : j < i
    · cases ParentBit : Parent j <;> simp [Z, Below, ParentBit, (RankWeightPositive j).le]
    · simp [Z, Below]
  have AddedPrefixMean : (∫ y, A.indicator (AddedRank Parent) y ∂μ) ≤
      (p : ℝ)*(∑ j : Fin n, if j < i then RankWeight j else 0)*μ.real A :=
    AddedMean.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ZBound p.2.1) ENNReal.toReal_nonneg)
  have MeanF : (∫ y, F y ∂μ) = μ.real A := by
    simpa only [F, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := μ) (1 : ℝ) (s := A) (Set.to_countable _).measurableSet)
  have MainMean : (∫ y, A.indicator (fun z => RankPotential Parent-
      RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y ∂μ) =
      RankWeight i*μ.real A-(∫ y, A.indicator (AddedRank Parent) y ∂μ) := by
    have Functions : (fun y => A.indicator (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y) =
        fun y => RankWeight i*F y-A.indicator (AddedRank Parent) y := by
      funext y
      by_cases Member : y ∈ A
      · simp only [F, Set.indicator_of_mem Member, mul_one]
        rw [ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent y Member.1,
          RankDifferenceByRemovedAdded, RemovedRankOfSingleDownward Parent y i Member.2.1]
      · simp [F, Set.indicator, Member]
    rw [Functions, integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul, MeanF]
  change (RankWeight i-(p : ℝ)*(∑ j : Fin n, if j < i then RankWeight j else 0))*μ.real A ≤
    ∫ y, A.indicator (fun z => RankPotential Parent-
      RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y ∂μ
  rw [MainMean]
  calc
    _ = RankWeight i*μ.real A-((p : ℝ)*(∑ j : Fin n, if j < i then RankWeight j else 0)*μ.real A) := by ring
    _ ≤ _ := sub_le_sub_left AddedPrefixMean _

/-- Source Ai bound on the actual standard-rate selected decrement.
The coefficient is positive even at the first indices and at n=1. -/
theorem StandardLowerSingleDownwardContributionLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (WeightsNonnegative : ∀ j, 0 ≤ Weights j)
    (Parent : Bits n) (i : Fin n) (ParentOne : Parent i = true) :
    StandardOneBitProbability n*(1-((i.val : ℝ)-2)/(2*(n : ℝ))) ≤
    ∫ y, (LowerSingleDownwardEvent Weights Parent i).indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1/(n : ℝ), ⟨div_nonneg (by norm_num) PositiveN.le,
    (div_le_one PositiveN).mpr (Nat.one_le_cast.mpr PositiveLength)⟩⟩
  have Bound := LowerSingleDownwardRankMeanLowerBound p Weights WeightsNonnegative Parent i
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
  simp only [Rate] at Bound
  change (RankWeight i-(1/(n : ℝ))*(∑ j : Fin n, if j < i then RankWeight j else 0))*
      (StandardBitMutation PositiveLength Parent).toMeasure.real (LowerSingleDownwardEvent Weights Parent i) ≤
    ∫ y, (LowerSingleDownwardEvent Weights Parent i).indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure at Bound
  have Probability := StandardLowerSingleDownwardProbabilityLowerBound PositiveLength
    Weights Parent i ParentOne (WeightsNonnegative i)
  calc
    _ = (1-((i.val : ℝ)-2)/(2*(n : ℝ)))*StandardOneBitProbability n := mul_comm _ _
    _ ≤ (1-((i.val : ℝ)-2)/(2*(n : ℝ)))*
        (StandardBitMutation PositiveLength Parent).toMeasure.real (LowerSingleDownwardEvent Weights Parent i) :=
      mul_le_mul_of_nonneg_left Probability (RankPrefixDriftCoefficientPositive i).le
    _ ≤ (RankWeight i-(1/(n : ℝ))*(∑ j : Fin n, if j < i then RankWeight j else 0))*
        (StandardBitMutation PositiveLength Parent).toMeasure.real (LowerSingleDownwardEvent Weights Parent i) :=
      mul_le_mul_of_nonneg_right (RankPrefixDriftCoefficientLower i) ENNReal.toReal_nonneg
    _ ≤ _ := Bound

/-- Exact objective accounting for the real single-removal event.
No sign or ordering condition on objective weights is needed for this identity. -/
theorem ScoreDifferenceOfSingleDownward {n : ℕ} (Weights : Fin n → ℝ)
    (Parent Candidate : Bits n) (i : Fin n) (Single : SingleDownwardAt Parent i Candidate) :
    Score Weights Parent-Score Weights Candidate = Weights i-
      (∑ j : Fin n, (if Parent j then (0 : ℝ) else Weights j)*(if Candidate j then 1 else 0)) := by
  have Identity : (∑ j : Fin n,
      (Weights j*(if Parent j then (1 : ℝ) else 0)-Weights j*(if Candidate j then (1 : ℝ) else 0)+
        (if Parent j then (0 : ℝ) else Weights j)*(if Candidate j then 1 else 0))) = Weights i := by
    rw [Finset.sum_eq_single i]
    · simp [Single.1, Single.2.1]
    · intro j _ Different
      cases ParentBit : Parent j with
      | false => cases Candidate j <;> simp
      | true => simp [Single.2.2 j Different ParentBit]
    · intro Absent
      exact False.elim (Absent (Finset.mem_univ i))
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at Identity
  change Score Weights Parent-Score Weights Candidate+
    (∑ j : Fin n, (if Parent j then (0 : ℝ) else Weights j)*(if Candidate j then 1 else 0)) = Weights i at Identity
  linarith

/-- A genuine Bi proposal is forced to be exactly one equal-weight swap.
The strict positivity condition excludes extra zero-weight additions. -/
theorem HigherSingleDownwardIsEqualWeightSwap {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights) (Parent Candidate : Bits n)
    (i : Fin n) (Member : Candidate ∈ HigherSingleDownwardEvent Weights Parent i) :
    ∃ j, i < j ∧ Parent j = false ∧ Candidate j = true ∧ Weights j = Weights i ∧
      Candidate = OnebitMutation (OnebitMutation Parent i) j := by
  classical
  rcases Member.2.2 with ⟨j, Above, ParentZero, CandidateOne⟩
  let Z := fun k : Fin n => (if Parent k then (0 : ℝ) else Weights k)*(if Candidate k then 1 else 0)
  have ZNonnegative (k : Fin n) : 0 ≤ Z k := by
    cases ParentBit : Parent k <;> cases CandidateBit : Candidate k <;>
      simp [Z, ParentBit, CandidateBit, (Positive k).le]
  have AddedUpper : (∑ k : Fin n, Z k) ≤ Weights i := by
    have Difference := ScoreDifferenceOfSingleDownward Weights Parent Candidate i Member.2.1
    change Score Weights Parent-Score Weights Candidate = Weights i-(∑ k : Fin n, Z k) at Difference
    linarith [Member.1]
  have TermJ : Z j = Weights j := by simp [Z, ParentZero, CandidateOne]
  have AddedLower : Weights j ≤ ∑ k : Fin n, Z k := by
    rw [← TermJ]
    exact Finset.single_le_sum (fun k _ => ZNonnegative k) (Finset.mem_univ j)
  have WeightOrder : Weights i ≤ Weights j := Sorted Above.le
  have EqualWeight : Weights j = Weights i := le_antisymm (AddedLower.trans AddedUpper) WeightOrder
  have SumEq : (∑ k : Fin n, Z k) = Z j := by
    rw [TermJ, EqualWeight]
    exact le_antisymm AddedUpper (WeightOrder.trans AddedLower)
  have RestZero : (∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, Z k) = 0 := by
    have Split := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) Z (Finset.mem_univ j)
    rw [SumEq] at Split
    linarith
  have OtherTermZero (k : Fin n) (Different : k ≠ j) : Z k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => ZNonnegative a)).mp RestZero k
      (Finset.mem_erase.mpr ⟨Different, Finset.mem_univ k⟩)
  have OtherZeroKept (k : Fin n) (Different : k ≠ j) (ParentK : Parent k = false) : Candidate k = false := by
    have Term := OtherTermZero k Different
    cases CandidateBit : Candidate k with
    | false => rfl
    | true =>
      have Impossible : Weights k = 0 := by simpa [Z, ParentK, CandidateBit] using Term
      exact False.elim ((ne_of_gt (Positive k)) Impossible)
  have Swap : Candidate = OnebitMutation (OnebitMutation Parent i) j := by
    funext k
    by_cases AtI : k = i
    · subst k
      simp [OnebitMutation, ne_of_lt Above, Member.2.1.1, Member.2.1.2.1]
    · by_cases AtJ : k = j
      · subst k
        simp [OnebitMutation, ne_of_gt Above, ParentZero, CandidateOne]
      · rw [OnebitMutationAway (OnebitMutation Parent i) j k AtJ, OnebitMutationAway Parent i k AtI]
        cases ParentBit : Parent k with
        | true => exact Member.2.1.2.2 k AtI ParentBit
        | false => exact OtherZeroKept k AtJ ParentBit
  exact ⟨j, Above, ParentZero, CandidateOne, EqualWeight, Swap⟩

/-- Rank loss of the actual two-coordinate swap; no objective weight hypothesis. -/
theorem RankDifferenceOfSwap {n : ℕ} (Parent : Bits n) (i j : Fin n)
    (Different : i ≠ j) (ParentOne : Parent i = true) (ParentZero : Parent j = false) :
    RankPotential Parent-RankPotential (OnebitMutation (OnebitMutation Parent i) j) =
      RankWeight i-RankWeight j := by
  have First := RLSLinear.MutationScoreDifference RankWeight Parent i
  have Second := RLSLinear.MutationScoreDifference RankWeight (OnebitMutation Parent i) j
  simp only [ParentOne, if_true] at First
  simp only [OnebitMutationAway Parent i j Different.symm, ParentZero,
    Bool.false_eq_true, if_false] at Second
  change RankPotential Parent-RankPotential (OnebitMutation Parent i) = RankWeight i at First
  change RankPotential (OnebitMutation Parent i)-
    RankPotential (OnebitMutation (OnebitMutation Parent i) j) = -RankWeight j at Second
  linarith

/-- Two distinct specified flips change exactly two coordinates, for every parent. -/
theorem SwapBitDifferenceCount {n : ℕ} (Parent : Bits n) (i j : Fin n) (Different : i ≠ j) :
    BitDifferenceCount Parent (OnebitMutation (OnebitMutation Parent i) j) = 2 := by
  classical
  have Changed (k : Fin n) :
      OnebitMutation (OnebitMutation Parent i) j k ≠ Parent k ↔ k = i ∨ k = j := by
    by_cases AtI : k = i
    · subst k
      cases Bit : Parent i <;> simp [OnebitMutation, Different, Bit]
    · by_cases AtJ : k = j
      · subst k
        cases Bit : Parent j <;> simp [OnebitMutation, AtI, Bit]
      · simp [OnebitMutation, AtI, AtJ]
  have Filter : (Finset.univ.filter (fun k : Fin n =>
      OnebitMutation (OnebitMutation Parent i) j k ≠ Parent k)) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    exact Changed k
  unfold BitDifferenceCount
  rw [Filter]
  simp [Different]

/-- Exact probability of a specified two-flip swap relative to the one-flip mass.
The distinct-coordinate premise implies n>=2 before the exponent/division step. -/
theorem StandardSwapProbability {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n)
    (i j : Fin n) (Different : i ≠ j) :
    (StandardBitMutation PositiveLength Parent (OnebitMutation (OnebitMutation Parent i) j)).toReal =
      StandardOneBitProbability n/((n : ℝ)-1) := by
  have AtLeastTwo : 2 ≤ n := by
    have Unequal : i.val ≠ j.val := fun Equal => Different (Fin.ext Equal)
    have ILt := i.isLt
    have JLt := j.isLt
    omega
  have NPositive : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have NMinusPositive : (0 : ℝ) < (n : ℝ)-1 := by
    have RealAtLeastTwo : (2 : ℝ) ≤ n := Nat.cast_le.mpr AtLeastTwo
    linarith
  have Exponent : n-1 = (n-2)+1 := by omega
  rw [StandardBitMutationPatternReal, SwapBitDifferenceCount Parent i j Different]
  unfold StandardOneBitProbability
  rw [Exponent, pow_succ (1-1/(n : ℝ)) (n-2)]
  have NNonzero := ne_of_gt NPositive
  have NMinusNonzero := ne_of_gt NMinusPositive
  have Scalar : (1/(n : ℝ))^2 = (1/(n : ℝ))*(1-1/(n : ℝ))/((n : ℝ)-1) := by
    field_simp
  rw [Scalar]
  ring

/-- A pointwise pessimistic cost covering every true Bi proposal.
Additional higher-coordinate swaps are included only with nonnegative costs. -/
theorem HigherSingleDownwardRankCostLowerBound {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights)
    (Parent Candidate : Bits n) (i : Fin n) :
    -(∑ j : Fin n, if i < j then
      ({OnebitMutation (OnebitMutation Parent i) j} : Set (Bits n)).indicator
        (fun _ => ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ)) Candidate else 0) ≤
    (HigherSingleDownwardEvent Weights Parent i).indicator
      (fun y => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent y)) Candidate := by
  classical
  let C := fun j : Fin n => if i < j then
    ({OnebitMutation (OnebitMutation Parent i) j} : Set (Bits n)).indicator
      (fun _ => ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ)) Candidate else 0
  have Nonnegative (j : Fin n) : 0 ≤ C j := by
    by_cases Above : i < j
    · dsimp only [C]
      rw [if_pos Above]
      exact Set.indicator_nonneg (fun _ _ => div_nonneg
        (sub_nonneg.mpr (Nat.cast_le.mpr (show i.val ≤ j.val from Above.le)))
        (Nat.cast_nonneg n)) Candidate
    · simp [C, Above]
  change -(∑ j : Fin n, C j) ≤ _
  by_cases Member : Candidate ∈ HigherSingleDownwardEvent Weights Parent i
  · rcases HigherSingleDownwardIsEqualWeightSwap Weights Positive Sorted Parent Candidate i Member with
      ⟨j, Above, ParentZero, _, _, Swap⟩
    have TermJ : C j = ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ) := by simp [C, Above, Swap]
    calc
      _ ≤ -C j := neg_le_neg (Finset.single_le_sum (fun k _ => Nonnegative k) (Finset.mem_univ j))
      _ = RankPotential Parent-RankPotential Candidate := by
        rw [TermJ, Swap, RankDifferenceOfSwap Parent i j (ne_of_lt Above) Member.2.1.1 ParentZero,
          RankWeightDifference]
        ring
      _ = _ := by
        rw [Set.indicator_of_mem Member,
          ElitistSelectAccept (Problems.MinNotWorse (Score Weights)) Parent Candidate Member.1]
  · rw [Set.indicator_of_notMem Member]
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun j _ => Nonnegative j))

/-- Source Bi lower bound for the actual selected standard-rate decrement.
For n=1 the Bi event is empty; no n-1 division is used in that branch. -/
theorem StandardHigherSingleDownwardContributionLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights)
    (Parent : Bits n) (i : Fin n) :
    -StandardOneBitProbability n*(((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ))) ≤
    ∫ y, (HigherSingleDownwardEvent Weights Parent i).indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  classical
  let μ := (StandardBitMutation PositiveLength Parent).toMeasure
  let C := fun (j : Fin n) (y : Bits n) => if i < j then
    ({OnebitMutation (OnebitMutation Parent i) j} : Set (Bits n)).indicator
      (fun _ => ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ)) y else 0
  by_cases AtLeastTwo : 2 ≤ n
  · have Each (j : Fin n) : (∫ y, C j y ∂μ) =
        (StandardOneBitProbability n/((n : ℝ)-1))*
          (if i < j then ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ) else 0) := by
      by_cases Above : i < j
      · simp only [C, if_pos Above]
        rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
        have Mass : μ.real {OnebitMutation (OnebitMutation Parent i) j} =
            StandardOneBitProbability n/((n : ℝ)-1) := by
          change ((StandardBitMutation PositiveLength Parent).toMeasure
            {OnebitMutation (OnebitMutation Parent i) j}).toReal = _
          rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
          exact StandardSwapProbability PositiveLength Parent i j (ne_of_lt Above)
        rw [Mass]
      · simp [C, Above]
    have Mean : (∫ y, ∑ j : Fin n, C j y ∂μ) =
        StandardOneBitProbability n*
          ((∑ j : Fin n, if i < j then ((j.val : ℝ)-(i.val : ℝ))/(n : ℝ) else 0)/((n : ℝ)-1)) := by
      rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
      simp_rw [Each]
      rw [← Finset.mul_sum]
      ring
    have MeanUpper : (∫ y, ∑ j : Fin n, C j y ∂μ) ≤
        StandardOneBitProbability n*(((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ))) := by
      rw [Mean]
      exact mul_le_mul_of_nonneg_left (RankSuffixSwapCostBound AtLeastTwo i)
        (StandardOneBitProbabilityPositive PositiveLength).le
    have Bound := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite
      (fun y => HigherSingleDownwardRankCostLowerBound Weights Positive Sorted Parent y i)
    change (∫ y, -(∑ j : Fin n, C j y) ∂μ) ≤ _ at Bound
    rw [integral_neg] at Bound
    calc
      _ = -(StandardOneBitProbability n*(((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)))) := by ring
      _ ≤ -(∫ y, ∑ j : Fin n, C j y ∂μ) := neg_le_neg MeanUpper
      _ ≤ _ := Bound
  · have Empty : HigherSingleDownwardEvent Weights Parent i = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y Member
      rcases Member.2.2 with ⟨j, Above, _, _⟩
      have IBound := i.isLt
      have JBound := j.isLt
      have IndexOrder : i.val < j.val := Above
      omega
    rw [Empty]
    simp only [Set.indicator_empty, integral_zero]
    have IndexBound : (i.val : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.le_of_lt i.isLt)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (StandardOneBitProbabilityPositive PositiveLength).le)
      (div_nonneg (sub_nonneg.mpr IndexBound) (by positivity))

/-- The complete accepted single-removal contribution for a marked parent-one.
Both Ai and Bi are integrated under the original standard mutation law. -/
theorem StandardSingleDownwardContributionLowerBound {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights)
    (Parent : Bits n) (i : Fin n) (ParentOne : Parent i = true) :
    StandardOneBitProbability n/2 ≤
    ∫ y, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ SingleDownwardAt Parent i z}.indicator
      (fun z => RankPotential Parent-
        RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) y
      ∂(StandardBitMutation PositiveLength Parent).toMeasure := by
  have Lower := StandardLowerSingleDownwardContributionLowerBound PositiveLength
    Weights (fun k => (Positive k).le) Parent i ParentOne
  have Higher := StandardHigherSingleDownwardContributionLowerBound PositiveLength Weights Positive Sorted Parent i
  have NNonzero : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr PositiveLength)
  have Coefficient : StandardOneBitProbability n/2 ≤
      StandardOneBitProbability n*(1-((i.val : ℝ)-2)/(2*(n : ℝ)))+
        (-StandardOneBitProbability n*(((n : ℝ)-(i.val : ℝ))/(2*(n : ℝ)))) := by
    calc
      _ ≤ StandardOneBitProbability n/2+StandardOneBitProbability n/(n : ℝ) :=
        le_add_of_nonneg_right (div_nonneg (StandardOneBitProbabilityPositive PositiveLength).le (Nat.cast_nonneg n))
      _ = _ := by field_simp; ring
  rw [← SingleDownwardEventsPartition, Set.indicator_union_of_disjoint (SingleDownwardEventsDisjoint Weights Parent i)]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  exact Coefficient.trans (add_le_add Lower Higher)

/-- A real weak-selection Bi event with negative contribution: 10 -> 01 at n=2.
Its exact integral -1/8 attains the pessimistic Bi bound for the first index. -/
theorem ExistsTightNegativeHigherSingleDownwardContribution :
    ∃ Parent Candidate : Bits 2,
      Candidate ∈ HigherSingleDownwardEvent (fun _ => (1 : ℝ)) Parent (0 : Fin 2) ∧
      Score (fun _ => (1 : ℝ)) Candidate = Score (fun _ => (1 : ℝ)) Parent ∧
      (Step (by decide : 0 < 2) (fun _ => (1 : ℝ)) Parent Candidate).toReal = (1 : ℝ)/4 ∧
      RankPotential Parent-RankPotential Candidate = -(1 : ℝ)/2 ∧
      (∫ y, (HigherSingleDownwardEvent (fun _ => (1 : ℝ)) Parent (0 : Fin 2)).indicator
        (fun z => RankPotential Parent-
          RankPotential (ElitistSelect (Problems.MinNotWorse (Score (fun _ => (1 : ℝ)))) Parent z)) y
        ∂(StandardBitMutation (by decide : 0 < 2) Parent).toMeasure) = -(1 : ℝ)/8 := by
  classical
  let Parent : Bits 2 := fun i => decide (i.val = 0)
  let Candidate := OnebitMutation (OnebitMutation Parent (0 : Fin 2)) (1 : Fin 2)
  have Positive : ∀ k : Fin 2, 0 < (fun _ : Fin 2 => (1 : ℝ)) k := by intro k; norm_num
  have Sorted : Monotone (fun _ : Fin 2 => (1 : ℝ)) := by intro i j _; rfl
  have ScoreEqual : Score (fun _ => (1 : ℝ)) Candidate = Score (fun _ => (1 : ℝ)) Parent := by
    norm_num [Score, Parent, Candidate, OnebitMutation, Fin.sum_univ_succ]
  have Single : SingleDownwardAt Parent (0 : Fin 2) Candidate := by
    refine ⟨by decide, by decide, ?_⟩
    intro j Different ParentOne
    fin_cases j
    · exact False.elim (Different rfl)
    · rfl
  have Member : Candidate ∈ HigherSingleDownwardEvent (fun _ => (1 : ℝ)) Parent (0 : Fin 2) :=
    ⟨ScoreEqual.le, Single, ⟨1, by decide, by decide, by decide⟩⟩
  have Different : Candidate ≠ Parent := by
    intro Equal
    have Bit := congrFun Equal (0 : Fin 2)
    norm_num [Candidate, Parent, OnebitMutation] at Bit
  have MutationMass : (StandardBitMutation (by decide : 0 < 2) Parent Candidate).toReal = (1 : ℝ)/4 := by
    have Mass := StandardSwapProbability (by decide : 0 < 2) Parent (0 : Fin 2) (1 : Fin 2) (by decide)
    norm_num [StandardOneBitProbability] at Mass
    exact Mass
  have StepMass : (Step (by decide : 0 < 2) (fun _ => (1 : ℝ)) Parent Candidate).toReal = (1 : ℝ)/4 := by
    rw [StepAcceptedProbability (by decide : 0 < 2) (fun _ => (1 : ℝ)) Parent Candidate Different ScoreEqual.le]
    exact MutationMass
  have RankDifference : RankPotential Parent-RankPotential Candidate = -(1 : ℝ)/2 := by
    change RankPotential Parent-RankPotential (OnebitMutation (OnebitMutation Parent (0 : Fin 2)) (1 : Fin 2)) = _
    rw [RankDifferenceOfSwap Parent 0 1 (by decide) (by decide) (by decide), RankWeightDifference]
    norm_num
  have Event : HigherSingleDownwardEvent (fun _ => (1 : ℝ)) Parent (0 : Fin 2) = {Candidate} := by
    ext y
    constructor
    · intro InEvent
      rcases HigherSingleDownwardIsEqualWeightSwap (fun _ => (1 : ℝ)) Positive Sorted Parent y 0 InEvent with
        ⟨j, Above, _, _, _, Swap⟩
      have JOne : j = (1 : Fin 2) := by
        apply Fin.ext
        have JBound := j.isLt
        have Lower : 0 < j.val := Above
        omega
      rw [JOne] at Swap
      exact Set.mem_singleton_iff.mpr Swap
    · intro InSingleton
      rw [Set.mem_singleton_iff.mp InSingleton]
      exact Member
  have Functions : (fun y => (HigherSingleDownwardEvent (fun _ => (1 : ℝ)) Parent (0 : Fin 2)).indicator
        (fun z => RankPotential Parent-
          RankPotential (ElitistSelect (Problems.MinNotWorse (Score (fun _ => (1 : ℝ)))) Parent z)) y) =
      ({Candidate} : Set (Bits 2)).indicator (fun _ => -(1 : ℝ)/2) := by
    funext y
    rw [Event]
    by_cases InSingleton : y ∈ ({Candidate} : Set (Bits 2))
    · rw [Set.indicator_of_mem InSingleton, Set.indicator_of_mem InSingleton,
        Set.mem_singleton_iff.mp InSingleton,
        ElitistSelectAccept (Problems.MinNotWorse (Score (fun _ => (1 : ℝ)))) Parent Candidate ScoreEqual.le]
      exact RankDifference
    · rw [Set.indicator_of_notMem InSingleton, Set.indicator_of_notMem InSingleton]
  refine ⟨Parent, Candidate, Member, ScoreEqual, StepMass, RankDifference, ?_⟩
  rw [Functions, integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
  have RealMass : (StandardBitMutation (by decide : 0 < 2) Parent).toMeasure.real {Candidate} = (1 : ℝ)/4 := by
    change ((StandardBitMutation (by decide : 0 < 2) Parent).toMeasure {Candidate}).toReal = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact MutationMass
  rw [RealMass]
  norm_num

/-- Exact zero/unique/multiple-removal accounting for any selected observable.
Strictly positive objective weights make the zero-removal selector the parent.
No sorting, mutation law or monotonicity of the observable is assumed. -/
theorem SelectedDifferencePartition {n : ℕ} (Weights : Fin n → ℝ)
    (Positive : ∀ k, 0 < Weights k) (V : Bits n → ℝ) (Parent Candidate : Bits n) :
    V Parent-V (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent Candidate) =
      {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}.indicator
        (fun z => V Parent-V (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) Candidate+
      ∑ i : Fin n, {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ SingleDownwardAt Parent i z}.indicator
        (fun z => V Parent-V (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)) Candidate := by
  classical
  let F := fun z : Bits n => V Parent-V (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)
  let M : Set (Bits n) := {z | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}
  let A := fun i : Fin n => {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ SingleDownwardAt Parent i z}
  have SingleSumZero (NotOne : FlippedOnes Parent Candidate ≠ 1) :
      (∑ i : Fin n, (A i).indicator F Candidate) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have Outside : Candidate ∉ A i := by
      intro Member
      exact NotOne ((SingleDownwardAtIff Parent Candidate i).mp Member.2).2.2
    rw [Set.indicator_of_notMem Outside]
  change F Candidate = M.indicator F Candidate+∑ i : Fin n, (A i).indicator F Candidate
  by_cases Accepted : Score Weights Candidate ≤ Score Weights Parent
  · by_cases Zero : FlippedOnes Parent Candidate = 0
    · have FZero : F Candidate = 0 := by
        dsimp only [F]
        rw [SelectWithoutRemovalEqParent Weights Positive Parent Candidate Zero, sub_self]
      have Outside : Candidate ∉ M := by
        intro Member
        have Count := Member.2
        omega
      rw [FZero, Set.indicator_of_notMem Outside, SingleSumZero (by omega), add_zero]
    · by_cases One : FlippedOnes Parent Candidate = 1
      · rcases (FlippedOnesOneIff Parent Candidate).mp One with ⟨i, Single⟩
        have SingleAt : SingleDownwardAt Parent i Candidate := Single
        have Outside : Candidate ∉ M := by
          intro Member
          have Count := Member.2
          omega
        have Sum : (∑ j : Fin n, (A j).indicator F Candidate) = F Candidate := by
          rw [Finset.sum_eq_single i]
          · rw [Set.indicator_of_mem (show Candidate ∈ A i from ⟨Accepted, SingleAt⟩)]
          · intro j _ Different
            have OutsideJ : Candidate ∉ A j := by
              intro Member
              exact Different (SingleDownwardAtUnique Parent Candidate j i Member.2 SingleAt)
            rw [Set.indicator_of_notMem OutsideJ]
          · intro Absent
            exact False.elim (Absent (Finset.mem_univ i))
        rw [Set.indicator_of_notMem Outside, Sum, zero_add]
      · have Member : Candidate ∈ M := ⟨Accepted, by omega⟩
        rw [Set.indicator_of_mem Member, SingleSumZero One, add_zero]
  · have FZero : F Candidate = 0 := by
      dsimp only [F]
      rw [ElitistSelectReject (Problems.MinNotWorse (Score Weights)) Parent Candidate Accepted, sub_self]
    have Outside : Candidate ∉ M := fun Member => Accepted Member.1
    have Sum : (∑ i : Fin n, (A i).indicator F Candidate) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [Set.indicator_of_notMem (show Candidate ∉ A i from fun Member => Accepted Member.1)]
    rw [FZero, Set.indicator_of_notMem Outside, Sum, add_zero]

/-- Complete selected rank drift for sorted positive linear objectives, in one-count units. -/
theorem StandardSortedRankDriftCountLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights)
    (Parent : Bits n) :
    StandardOneBitProbability n*(OneMax Parent : ℝ)/2 ≤
      ∫ Next, RankPotential Parent-RankPotential Next ∂(Step PositiveLength Weights Parent).toMeasure := by
  classical
  let μ := (StandardBitMutation PositiveLength Parent).toMeasure
  let F := fun z : Bits n => RankPotential Parent-
    RankPotential (ElitistSelect (Problems.MinNotWorse (Score Weights)) Parent z)
  let A := fun i : Fin n => {z : Bits n | Score Weights z ≤ Score Weights Parent ∧ SingleDownwardAt Parent i z}
  let M : Set (Bits n) := {z | Score Weights z ≤ Score Weights Parent ∧ 2 ≤ FlippedOnes Parent z}
  have Each (i : Fin n) : (if Parent i then StandardOneBitProbability n/2 else 0) ≤
      ∫ y, (A i).indicator F y ∂μ := by
    cases ParentBit : Parent i with
    | true =>
      simp only [if_true]
      exact StandardSingleDownwardContributionLowerBound PositiveLength Weights Positive Sorted Parent i ParentBit
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have Empty : A i = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y Member
        have ParentOne := Member.2.1
        rw [ParentBit] at ParentOne
        cases ParentOne
      rw [Empty]
      simp
  have SumLower : StandardOneBitProbability n*(OneMax Parent : ℝ)/2 ≤
      ∑ i : Fin n, ∫ y, (A i).indicator F y ∂μ := by
    calc
      _ = ∑ i : Fin n, if Parent i then StandardOneBitProbability n/2 else 0 := by
        rw [← ScoreUnitWeights Parent]
        simp only [Score, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        cases Parent i <;> simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Each i)
  have Many : 0 ≤ ∫ y, M.indicator F y ∂μ :=
    StandardMultipleDownwardContributionNonnegative PositiveLength Weights (fun k => (Positive k).le) Parent
  have Functions : (fun y => F y) = fun y => M.indicator F y+∑ i : Fin n, (A i).indicator F y := by
    funext y
    exact SelectedDifferencePartition Weights Positive RankPotential Parent y
  unfold Step OnePlusOneEAStep
  rw [PMFIntegralMap]
  change _ ≤ ∫ y, F y ∂μ
  rw [Functions, integral_add Integrable.of_finite Integrable.of_finite,
    integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  exact SumLower.trans (le_add_of_nonneg_left Many)

/-- Weight-independent G/(4en) drift of the original standard weak-minimizing EA.
This is the entire selected kernel, not a conditional or single-bit surrogate. -/
theorem StandardSortedRankDriftLower {n : ℕ} (PositiveLength : 0 < n)
    (Weights : Fin n → ℝ) (Positive : ∀ k, 0 < Weights k) (Sorted : Monotone Weights)
    (Parent : Bits n) :
    RankPotential Parent/(4*Real.exp 1*(n : ℝ)) ≤
      ∫ Next, RankPotential Parent-RankPotential Next ∂(Step PositiveLength Weights Parent).toMeasure := by
  have QPositive := StandardOneBitProbabilityPositive PositiveLength
  have QLower : 1/(Real.exp 1*(n : ℝ)) ≤ StandardOneBitProbability n := by
    have Bound := one_div_le_one_div_of_le (one_div_pos.mpr QPositive)
      (StandardOneBitProbabilityInverseBound PositiveLength)
    simpa using Bound
  calc
    _ ≤ (2*(OneMax Parent : ℝ))/(4*Real.exp 1*(n : ℝ)) :=
      div_le_div_of_nonneg_right (RankPotentialLeTwoCount Parent) (by positivity)
    _ = (1/(Real.exp 1*(n : ℝ)))*(OneMax Parent : ℝ)/2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ StandardOneBitProbability n*(OneMax Parent : ℝ)/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right QLower (Nat.cast_nonneg _)) (by norm_num)
    _ ≤ _ := StandardSortedRankDriftCountLower PositiveLength Weights Positive Sorted Parent

end
end ECTheoryLib.Analysis.EALinearMinimization

