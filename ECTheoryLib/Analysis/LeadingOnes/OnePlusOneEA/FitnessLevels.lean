import ECTheoryLib.Algorithms.OnePlusOneEA
import ECTheoryLib.Operators.Mutation.IndependentBitCoupling
import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Problems.LOTZGeometry
import ECTheoryLib.Tools.Runtime.FitnessLevelsFromHistory
import Mathlib.Order.Interval.Finset.Fin

/-!
# Standard (1+1) EA on LeadingOnes: fitness-level runtime distribution

The original independent-bit mutation and weak elitist selection cross level i
with exact probability (1/n)(1-1/n)^i. Only the initial i+1 coordinates are
constrained; the suffix remains unrestricted, including neutral multibit moves.
The original first hitting time, from arbitrary initialization, is dominated
by a sum of independent geometric waits counting trials from one. Actual
level durations may vanish and need not be independent. Time counts mutation
rounds after initialization. This bound does not claim an exact runtime law.
-/

namespace ECTheoryLib.Analysis.OnePlusOneEAOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
open scoped unitInterval
noncomputable section

/-- The existing standard EA kernel with weak maximization of LeadingOnes. -/
def Step {n : ℕ} (PositiveLength : 0 < n) (Parent : Bits n) : PMF (Bits n) :=
  OnePlusOneEAStep PositiveLength
    (fun Candidate Parent => LeadingOnes Parent ≤ LeadingOnes Candidate) Parent

/-- Exact success parameter of nonterminal prefix level i. -/
def FitnessLevelProbability {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) : I :=
  ⟨(1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) ^ i.val, by
    have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
    have RateNonnegative : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have RateUpper : 1 / (n : ℝ) ≤ 1 :=
      (div_le_one PositiveN).mpr (by exact_mod_cast PositiveLength)
    have ComplementNonnegative : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := sub_nonneg.mpr RateUpper
    constructor
    · exact mul_nonneg RateNonnegative (pow_nonneg ComplementNonnegative _)
    · calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul RateUpper
          (pow_le_one₀ ComplementNonnegative (by linarith))
          (pow_nonneg ComplementNonnegative _) zero_le_one
        _ = 1 := mul_one 1⟩

/-- Success is positive for every nonterminal level, including n=1. -/
theorem FitnessLevelProbabilityPositive {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) :
    0 < (FitnessLevelProbability PositiveLength i : ℝ) := by
  by_cases One : n = 1
  · subst n
    have IndexZero : i.val = 0 := by omega
    norm_num [FitnessLevelProbability, IndexZero]
  · have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
    have RateStrict : 1 / (n : ℝ) < 1 :=
      (div_lt_one PositiveN).mpr (by exact_mod_cast (show 1 < n by omega))
    exact mul_pos (div_pos zero_lt_one PositiveN) (pow_pos (sub_pos.mpr RateStrict) _)

private theorem PrefixThresholdEvent {n : ℕ} (i : Fin n) :
    {y : Bits n | i.val + 1 ≤ LeadingOnes y} =
      (↑(Finset.Iic i) : Set (Fin n)).pi (fun _ => ({true} : Set Bool)) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_Iic,
    Set.mem_singleton_iff]
  constructor
  · intro Length j Before
    apply Problems.LeadingOnes.HasLeadingOnesPrefix y j
    have Bound : j.val ≤ i.val := Before
    omega
  · intro Prefix
    apply Problems.LeadingOnes.PrefixLeLeadingOnes y (Nat.succ_le_of_lt i.isLt)
    intro j Before
    apply Prefix j
    change j.val ≤ i.val
    omega

private theorem MutationFitnessLevelSuccess {n : ℕ} (p : I) (i : Fin n) (x : Bits n)
    (AtLevel : LeadingOnes x = i) :
    (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).toMeasure.real
      {y | i.val + 1 ≤ LeadingOnes y} = (p : ℝ) * (1 - (p : ℝ)) ^ i.val := by
  have Outside : LeadingOnes x < n := by rw [AtLevel]; exact i.isLt
  have Zero := Problems.LOTZ.FirstZeroBit x Outside
  have Same : (⟨LeadingOnes x, Outside⟩ : Fin n) = i := Fin.ext AtLevel
  rw [Same] at Zero
  have PrefixMass :
      (∏ j ∈ Finset.Iio i, BitMutationProbability (ENNReal.ofReal (p : ℝ)) (x j) true) =
        (1 - ENNReal.ofReal (p : ℝ)) ^ i.val := by
    calc
      _ = ∏ _j ∈ Finset.Iio i, (1 - ENNReal.ofReal (p : ℝ)) := by
        apply Finset.prod_congr rfl
        intro j Before
        have One : x j = true := Problems.LeadingOnes.HasLeadingOnesPrefix x j (by
          rw [AtLevel]
          exact (Finset.mem_Iio.mp Before : j < i))
        simp only [One, BitMutationProbability, if_true]
      _ = _ := by rw [Finset.prod_const, Fin.card_Iio]
  have Mass :
      (IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x).toMeasure
        {y | i.val + 1 ≤ LeadingOnes y} =
          ENNReal.ofReal (p : ℝ) * (1 - ENNReal.ofReal (p : ℝ)) ^ i.val := by
    rw [← IndependentBitMutationProductLaw, PrefixThresholdEvent, Measure.pi_pi_finset]
    simp_rw [BernoulliMutationMass]
    rw [← Finset.Iio_insert i, Finset.prod_insert Finset.notMem_Iio_self, PrefixMass]
    simp only [Zero, BitMutationProbability, Bool.true_eq_false, if_false]
  have Complement : ENNReal.ofReal (1 - (p : ℝ)) = 1 - ENNReal.ofReal (p : ℝ) := by
    rw [ENNReal.ofReal_sub 1 p.2.1, ENNReal.ofReal_one]
  rw [measureReal_def, Mass, ← Complement, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal p.2.1, ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]

/-- At level i, selection crosses that level exactly when the proposed child does. -/
theorem SelectedCrossesFitnessLevelIff {n : ℕ} (i : Fin n) (x y : Bits n)
    (AtLevel : LeadingOnes x = i) :
    i.val + 1 ≤ LeadingOnes
      (ElitistSelect (fun Candidate Parent => LeadingOnes Parent ≤ LeadingOnes Candidate) x y) ↔
      i.val + 1 ≤ LeadingOnes y := by
  unfold ElitistSelect
  split_ifs with Accepted
  · rfl
  · change ¬LeadingOnes x ≤ LeadingOnes y at Accepted
    rw [AtLevel] at Accepted ⊢
    omega

/-- Weak selection preserves every prefix threshold under the original EA kernel. -/
theorem StepFitnessLevelAbsorption {n : ℕ} (PositiveLength : 0 < n) (i : ℕ) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, i ≤ LeadingOnes x → i ≤ LeadingOnes y := by
  apply PMFAEOfSupport
  intro y Supported Lower
  exact Lower.trans (OnePlusOneEAStepNotWorse PositiveLength
    (fun Candidate Parent => LeadingOnes Parent ≤ LeadingOnes Candidate)
    (fun _ => le_rfl) x y Supported)

/-- The exact probability of crossing level i under standard bit mutation and selection. -/
theorem StepFitnessLevelSuccess {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) (x : Bits n)
    (AtLevel : LeadingOnes x = i) :
    (Step PositiveLength x).toMeasure.real {y | i.val + 1 ≤ LeadingOnes y} =
      (FitnessLevelProbability PositiveLength i : ℝ) := by
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  let p : I := ⟨1 / (n : ℝ), by
    constructor
    · positivity
    · exact (div_le_one PositiveN).mpr (by exact_mod_cast PositiveLength)⟩
  have Rate : ENNReal.ofReal (p : ℝ) = (n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos PositiveN, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  have StandardLaw : StandardBitMutation PositiveLength x =
      IndependentBitMutation (ENNReal.ofReal (p : ℝ)) (MutationProbabilityBound p) x := by
    unfold StandardBitMutation
    simp only [Rate]
  have Event :
      (fun y => ElitistSelect
        (fun Candidate Parent => LeadingOnes Parent ≤ LeadingOnes Candidate) x y) ⁻¹'
          {y | i.val + 1 ≤ LeadingOnes y} = {y | i.val + 1 ≤ LeadingOnes y} := by
    ext y
    exact SelectedCrossesFitnessLevelIff i x y AtLevel
  rw [Step, OnePlusOneEAStep, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    measureReal_def, Measure.map_apply (measurable_of_finite _) (Set.to_countable _).measurableSet,
    Event, StandardLaw]
  exact MutationFitnessLevelSuccess p i x AtLevel

/-- The actual runtime is dominated by independent geometric waits with level-dependent rates. -/
theorem RuntimeFitnessLevelGeometricBound {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) Initial).map (FirstHittingTime (fun x => x = AllOnes n)))
      ((Measure.pi (fun i : Fin n => geometricMeasure (FitnessLevelProbability PositiveLength i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i + 1 : ℕ) : WithTop ℕ))) := by
  let Goals := fun i (x : Bits n) => i ≤ LeadingOnes x
  have FinalGoal : Goals n = (fun x => x = AllOnes n) := by
    funext x
    apply propext
    change n ≤ LeadingOnes x ↔ x = AllOnes n
    rw [← Problems.LeadingOnes.LeadingOnesEqNIffEqAllOnes]
    exact ⟨fun Lower => Nat.le_antisymm (Problems.LeadingOnes.LeadingOnesLeN x) Lower,
      fun Equal => Equal.ge⟩
  have Bound := PathFitnessLevelsGeometricBound (Step PositiveLength) Initial Goals
    (fun i x Later => Nat.le_trans (Nat.le_succ i) Later) (fun _ => Nat.zero_le _) n
    (FitnessLevelProbability PositiveLength) (FitnessLevelProbabilityPositive PositiveLength)
    (StepFitnessLevelAbsorption PositiveLength) (by
      intro i x Lower NotNext
      have AtLevel : LeadingOnes x = i := by
        change i.val ≤ LeadingOnes x at Lower
        change ¬i.val + 1 ≤ LeadingOnes x at NotNext
        omega
      exact (StepFitnessLevelSuccess PositiveLength i x AtLevel).ge)
  rw [FinalGoal] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.OnePlusOneEAOnLeadingOnes
