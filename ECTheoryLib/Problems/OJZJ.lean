import ECTheoryLib.Problems.Jump
import ECTheoryLib.Problems.OneMinMax

/-!
# OneJumpZeroJump (OJZJ)

The two shifted Jump objectives count ones and zeroes, respectively. The formal
Pareto characterization assumes `1 ≤ k` and `2*k ≤ n`, which includes the
degenerate boundary `2*k=n`. It is the conventional bi-objective benchmark,
not the stepping-stone or many-objective variants.
Source: Doerr and Zheng, AAAI 2021, Definition 4 and Theorem 5,
https://cdn.aaai.org/ojs/17459/17459-13-20953-1-2-20210518.pdf
-/

namespace ECTheoryLib

/-- OneJumpZeroJump: maximize JumpValue on the one count and on the zero count. The gap parameter is shared by both objectives. -/
def OJZJ {n : Nat} (k : Nat) (x : Bits n) : Fin 2 → Nat :=
  Problems.BiObjective (JumpValue n k (OneMax x)) (JumpValue n k (OneMin x))

namespace Problems.OJZJ

/-- Candidate front-weight condition: either endpoint or the middle interval from k to n-k. Its equivalence to Pareto optimality requires the parameter hypotheses of the subsequent theorems. -/
def IsFrontWeight (n k Weight : Nat) : Prop :=
  Weight = 0 ∨ Weight = n ∨ (k ≤ Weight ∧ Weight ≤ n - k)

instance (n k Weight : Nat) : Decidable (IsFrontWeight n k Weight) :=
  inferInstanceAs (Decidable (Weight = 0 ∨ Weight = n ∨ (k ≤ Weight ∧ Weight ≤ n - k)))

private theorem JumpValueLeLinear (n k Weight : Nat) : JumpValue n k Weight ≤ k + Weight := by
  unfold JumpValue
  split_ifs with OutsideValley
  · exact Nat.le_refl _
  · have TooManyOnes : n - k < Weight := by
      have NotSmallWeight : ¬ Weight ≤ n - k := by
        intro SmallWeight
        exact OutsideValley (Or.inl SmallWeight)
      omega
    omega

theorem ObjectiveSumLeNAddTwoK {n k : Nat} (x : Bits n) :
    ECTheoryLib.OJZJ k x 0 + ECTheoryLib.OJZJ k x 1 ≤ n + 2 * k := by
  have OnesBound := JumpValueLeLinear n k (OneMax x)
  have ZeroesBound := JumpValueLeLinear n k (OneMin x)
  have CountSum := OneMinMax.OneMaxAddOneMin x
  change JumpValue n k (OneMax x) + JumpValue n k (OneMin x) ≤ n + 2 * k
  omega

theorem FrontWeightFitness {n k : Nat} (x : Bits n)
    (FrontWeight : IsFrontWeight n k (OneMax x)) :
    ECTheoryLib.OJZJ k x = BiObjective (k + OneMax x) (k + OneMin x) := by
  have OnesBound := OneMax.OneMaxLeN x
  have OnesOutsideValley : OneMax x ≤ n - k ∨ OneMax x = n := by
    rcases FrontWeight with ZeroWeight | FullWeight | InteriorWeight
    · left
      omega
    · exact Or.inr FullWeight
    · exact Or.inl InteriorWeight.2
  have ZeroesOutsideValley : OneMin x ≤ n - k ∨ OneMin x = n := by
    unfold OneMin
    rcases FrontWeight with ZeroWeight | FullWeight | InteriorWeight
    · right
      omega
    · left
      omega
    · left
      omega
  unfold ECTheoryLib.OJZJ JumpValue
  rw [if_pos OnesOutsideValley, if_pos ZeroesOutsideValley]

theorem FrontWeightIsParetoMaximal {n k : Nat} (x : Bits n)
    (FrontWeight : IsFrontWeight n k (OneMax x)) :
    IsParetoMaximal (ECTheoryLib.OJZJ k) x := by
  have Fitness := FrontWeightFitness x FrontWeight
  have CountSum := OneMinMax.OneMaxAddOneMin x
  intro y Dominance
  have CoordinateBounds :
      k + OneMax x ≤ JumpValue n k (OneMax y) ∧
        k + OneMin x ≤ JumpValue n k (OneMin y) := by
    unfold ParetoMaxNotWorse at Dominance
    rw [Fitness] at Dominance
    exact (BiObjectiveLeIff _ _ _ _).mp Dominance
  have CandidateSumBound := ObjectiveSumLeNAddTwoK y (k := k)
  change JumpValue n k (OneMax y) + JumpValue n k (OneMin y) ≤ n + 2 * k at CandidateSumBound
  unfold ParetoMaxNotWorse
  rw [Fitness]
  apply (BiObjectiveLeIff _ _ _ _).mpr
  constructor
  · omega
  · omega

theorem IsParetoMaximalIffFrontWeight {n k : Nat}
    (PositiveK : 1 ≤ k) (ValleysDisjoint : 2 * k ≤ n) (x : Bits n) :
    IsParetoMaximal (ECTheoryLib.OJZJ k) x ↔ IsFrontWeight n k (OneMax x) := by
  constructor
  · intro Maximal
    by_contra OffFront
    have WeightBound := OneMax.OneMaxLeN x
    have CountSum := OneMinMax.OneMaxAddOneMin x
    have NonzeroWeight : OneMax x ≠ 0 := by
      intro ZeroWeight
      exact OffFront (Or.inl ZeroWeight)
    have NotFullWeight : OneMax x ≠ n := by
      intro FullWeight
      exact OffFront (Or.inr (Or.inl FullWeight))
    by_cases BelowK : OneMax x < k
    · let Candidate := PrefixOnes n k
      have KBound : k ≤ n := by omega
      have CandidateWeight : OneMax Candidate = k := LeadingOnes.OneMaxPrefixOnes KBound
      have CandidateFront : IsFrontWeight n k (OneMax Candidate) := by
        right
        right
        rw [CandidateWeight]
        constructor
        · exact Nat.le_refl k
        · omega
      have CandidateFitness := FrontWeightFitness Candidate CandidateFront
      rw [CandidateWeight] at CandidateFitness
      have CandidateZeroes : OneMin Candidate = n - k := by
        unfold OneMin
        rw [CandidateWeight]
      rw [CandidateZeroes] at CandidateFitness
      have OnesOutsideValley : OneMax x ≤ n - k ∨ OneMax x = n := by
        left
        omega
      have ZeroesInValley : ¬ (OneMin x ≤ n - k ∨ OneMin x = n) := by
        omega
      have XFitness : ECTheoryLib.OJZJ k x =
          BiObjective (k + OneMax x) (n - OneMin x) := by
        unfold ECTheoryLib.OJZJ JumpValue
        rw [if_pos OnesOutsideValley, if_neg ZeroesInValley]
      have Dominance : ParetoMaxNotWorse (ECTheoryLib.OJZJ k) Candidate x := by
        unfold ParetoMaxNotWorse
        rw [XFitness, CandidateFitness]
        apply (BiObjectiveLeIff _ _ _ _).mpr
        constructor
        · omega
        · omega
      have Reverse := Maximal Candidate Dominance
      have FirstCoordinate := Reverse 0
      rw [XFitness, CandidateFitness] at FirstCoordinate
      change k + k ≤ k + OneMax x at FirstCoordinate
      omega
    · have AboveInterior : n - k < OneMax x := by
        by_contra NotAbove
        apply OffFront
        right
        right
        omega
      let Candidate := PrefixOnes n (n - k)
      have CandidateWeight : OneMax Candidate = n - k :=
        LeadingOnes.OneMaxPrefixOnes (Nat.sub_le n k)
      have CandidateFront : IsFrontWeight n k (OneMax Candidate) := by
        right
        right
        rw [CandidateWeight]
        constructor
        · omega
        · exact Nat.le_refl _
      have CandidateFitness := FrontWeightFitness Candidate CandidateFront
      rw [CandidateWeight] at CandidateFitness
      have CandidateZeroes : OneMin Candidate = k := by
        unfold OneMin
        rw [CandidateWeight]
        omega
      rw [CandidateZeroes] at CandidateFitness
      have OnesInValley : ¬ (OneMax x ≤ n - k ∨ OneMax x = n) := by omega
      have ZeroesOutsideValley : OneMin x ≤ n - k ∨ OneMin x = n := by
        left
        omega
      have XFitness : ECTheoryLib.OJZJ k x =
          BiObjective (n - OneMax x) (k + OneMin x) := by
        unfold ECTheoryLib.OJZJ JumpValue
        rw [if_neg OnesInValley, if_pos ZeroesOutsideValley]
      have Dominance : ParetoMaxNotWorse (ECTheoryLib.OJZJ k) Candidate x := by
        unfold ParetoMaxNotWorse
        rw [XFitness, CandidateFitness]
        apply (BiObjectiveLeIff _ _ _ _).mpr
        constructor
        · omega
        · omega
      have Reverse := Maximal Candidate Dominance
      have SecondCoordinate := Reverse 1
      rw [XFitness, CandidateFitness] at SecondCoordinate
      change k + k ≤ k + OneMin x at SecondCoordinate
      omega
  · intro FrontWeight
    exact FrontWeightIsParetoMaximal x FrontWeight

theorem EveryFrontValueRealized {n k Weight : Nat} (WeightBound : Weight ≤ n)
    (FrontWeight : IsFrontWeight n k Weight) :
    ∃ x : Bits n, IsParetoMaximal (ECTheoryLib.OJZJ k) x ∧
      ECTheoryLib.OJZJ k x = BiObjective (k + Weight) (k + (n - Weight)) := by
  let x := PrefixOnes n Weight
  have WeightValue : OneMax x = Weight := LeadingOnes.OneMaxPrefixOnes WeightBound
  have XFront : IsFrontWeight n k (OneMax x) := by
    rw [WeightValue]
    exact FrontWeight
  refine ⟨x, FrontWeightIsParetoMaximal x XFront, ?_⟩
  rw [FrontWeightFitness x XFront]
  unfold OneMin
  rw [WeightValue]

end Problems.OJZJ
end ECTheoryLib
