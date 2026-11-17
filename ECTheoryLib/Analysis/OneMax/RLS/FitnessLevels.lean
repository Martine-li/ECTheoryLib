import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Probability.PMF.FinitePMF
import ECTheoryLib.Tools.Runtime.FitnessLevelsFromHistory

/-!
# RLS on OneMax: fitness-level runtime distribution

The actual uniform-bit-flip and elitist-selection kernel preserves fitness
thresholds. Its probability of leaving level i is exactly (n-i)/n, obtained
from the existing one-step drift identity because each accepted mutation
improves the score by exactly one. The history theorem gives the distribution
bound for any initial PMF, including initially optimal strings.

The product geometric reference is independent; no independence assumption is
placed on actual stage durations. Positive length is needed by RLS itself.
Runtime counts mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
open scoped unitInterval
noncomputable section

/-- The exact RLS probability of leaving OneMax level i: (n-i)/n. -/
def FitnessLevelProbability {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) : I :=
  ⟨((n : ℝ)-(i : ℝ))/(n : ℝ), by
    have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
    have BelowN : (i : ℝ) < n := Nat.cast_lt.mpr i.isLt
    constructor
    · exact div_nonneg (sub_nonneg.mpr BelowN.le) PositiveN.le
    · apply (div_le_one PositiveN).mpr
      exact sub_le_self _ (Nat.cast_nonneg i)⟩

/-- Every nonterminal level has positive progress probability. -/
theorem FitnessLevelProbabilityPositive {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) :
    0 < (FitnessLevelProbability PositiveLength i : ℝ) := by
  exact div_pos (sub_pos.mpr (Nat.cast_lt.mpr i.isLt)) (Nat.cast_pos.mpr PositiveLength)

/-- Elitist RLS preserves every lower fitness threshold almost surely. -/
theorem StepFitnessLevelAbsorption {n : ℕ} (PositiveLength : 0 < n) (i : ℕ) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, i ≤ OneMax x → i ≤ OneMax y := by
  filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Decrease
  have PotentialValue (z : Bits n) : Potential z = (n : ℝ)-(OneMax z : ℝ) :=
    Problems.OneMax.ZeroCountAsRealDifference z
  rw [PotentialValue x, PotentialValue y] at Decrease
  have FitnessIncreases : OneMax x ≤ OneMax y := by
    apply Nat.cast_le.mp (show (OneMax x : ℝ) ≤ (OneMax y : ℝ) by linarith)
  exact fun AtLevel => AtLevel.trans FitnessIncreases

/-- The genuine transition kernel has the exact level-success probability. -/
theorem StepFitnessLevelSuccess {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) (x : Bits n)
    (AtLevel : OneMax x = i) :
    (Step PositiveLength x).toMeasure.real {y | i.val+1 ≤ OneMax y} =
      (FitnessLevelProbability PositiveLength i : ℝ) := by
  classical
  let Goal : Set (Bits n) := {y | i.val+1 ≤ OneMax y}
  have UpdateIndicator (j : Fin n) :
      Goal.indicator (1 : Bits n → ℝ) (Update x j) = Potential x-Potential (Update x j) := by
    rw [PotentialDecrease]
    cases Bit : x j with
    | false =>
      have AtNext : Update x j ∈ Goal := by
        change i.val+1 ≤ OneMax (Update x j)
        rw [RLSAcceptsZeroFlip x j Bit, OneMax.OneMaxMutationAtZero x j Bit, AtLevel]
      rw [Set.indicator_of_mem AtNext]
      rfl
    | true =>
      have NotNext : Update x j ∉ Goal := by
        change ¬i.val+1 ≤ OneMax (Update x j)
        rw [RLSRejectsOneFlip x j Bit, AtLevel]
        omega
      rw [Set.indicator_of_notMem NotNext]
      rfl
  have ProbabilityAsDrift : (Step PositiveLength x).toMeasure.real Goal =
      ∫ y, Potential x-Potential y ∂(Step PositiveLength x).toMeasure := by
    rw [← integral_indicator_one (μ := (Step PositiveLength x).toMeasure)
      ((Set.to_countable Goal).measurableSet)]
    rw [Step, RLSStepEqUniformUpdate]
    rw [PMFIntegralMap, PMFIntegralMap]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall UpdateIndicator
  change (Step PositiveLength x).toMeasure.real Goal = _
  rw [ProbabilityAsDrift, OneStepDrift]
  change (Problems.OneMax.ZeroCount x : ℝ)/(n : ℝ) = _
  rw [Problems.OneMax.ZeroCountAsRealDifference, AtLevel]
  rfl

/-- For any initialization, actual RLS runtime is dominated by the independent geometric level sum. -/
theorem RuntimeFitnessLevelGeometricBound {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    StochasticDominated ((PathMeasure (Step PositiveLength) Initial).map (FirstHittingTime IsTarget))
      ((Measure.pi (fun i : Fin n => geometricMeasure (FitnessLevelProbability PositiveLength i))).map
        (fun z : Fin n → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  let Goals := fun i (x : Bits n) => i ≤ OneMax x
  have FinalGoal : Goals n = IsTarget := by
    funext x
    apply propext
    change n ≤ OneMax x ↔ IsTarget x
    rw [IsTargetIffEqAllOnes, ← Problems.OneMax.OneMaxEqNIffEqAllOnes]
    exact ⟨fun Lower => Nat.le_antisymm (Problems.OneMax.OneMaxLeN x) Lower,
      fun Equal => Equal.ge⟩
  have Bound := PathFitnessLevelsGeometricBound (Step PositiveLength) Initial Goals
    (fun i x Later => Nat.le_trans (Nat.le_succ i) Later) (fun _ => Nat.zero_le _) n
    (FitnessLevelProbability PositiveLength) (FitnessLevelProbabilityPositive PositiveLength)
    (StepFitnessLevelAbsorption PositiveLength) (by
      intro i x Lower NotNext
      have AtLevel : OneMax x = i := by
        change i.val ≤ OneMax x at Lower
        change ¬i.val+1 ≤ OneMax x at NotNext
        omega
      exact (StepFitnessLevelSuccess PositiveLength i x AtLevel).ge)
  rw [FinalGoal] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
