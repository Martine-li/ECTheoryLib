import ECTheoryLib.Analysis.LeadingOnes.RLS.SuffixSymmetry
import ECTheoryLib.Tools.Runtime.FitnessLevelsFromHistory

/-!
# RLS on LeadingOnes: fitness-level runtime distribution

At every nonterminal prefix length, the actual uniform-bit RLS update improves
exactly when it flips the first zero. The probability is 1/n even when that flip
skips several fitness levels. Weak selection also accepts neutral suffix moves.

For arbitrary initialization, the original path-law first hitting time is
dominated by a sum of n independent geometric waiting times. The reference
counts trials from one; actual level durations can be zero and need not be
independent. This bound does not claim a sharp uniform-start distribution or
improve the existing exact mean n^2/2. Time counts mutations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
open scoped unitInterval
noncomputable section

/-- The common success probability of every nonterminal LeadingOnes level. -/
def FitnessLevelProbability {n : ℕ} (PositiveLength : 0 < n) : I :=
  ⟨1 / (n : ℝ), by
    have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
    constructor
    · positivity
    · exact (div_le_one PositiveN).mpr (by exact_mod_cast PositiveLength)⟩

/-- Every nonterminal level has positive success probability, including n=1. -/
theorem FitnessLevelProbabilityPositive {n : ℕ} (PositiveLength : 0 < n) :
    0 < (FitnessLevelProbability PositiveLength : ℝ) := by
  exact div_pos zero_lt_one (Nat.cast_pos.mpr PositiveLength)

/-- A selected update crosses its current level exactly at the first zero. -/
theorem UpdateCrossesFitnessLevelIff {n : ℕ} (x : Bits n) (j : Fin n)
    (Outside : LeadingOnes x < n) :
    LeadingOnes x + 1 ≤ LeadingOnes (Update x j) ↔ j.val = LeadingOnes x := by
  by_cases Before : j.val < LeadingOnes x
  · rw [UpdateByPosition, if_pos Before]
    omega
  · rw [UpdateByPosition, if_neg Before]
    by_cases Equal : j.val = LeadingOnes x
    · have Same : j = ⟨LeadingOnes x, Outside⟩ := Fin.ext Equal
      rw [Same]
      exact ⟨fun _ => rfl, fun _ => FirstZeroFlipProgress x Outside⟩
    · rw [SuffixFlipValue x j (by omega)]
      omega

/-- Weak elitism preserves each prefix threshold under the actual kernel. -/
theorem StepFitnessLevelAbsorption {n : ℕ} (PositiveLength : 0 < n) (i : ℕ) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, i ≤ LeadingOnes x → i ≤ LeadingOnes y := by
  rw [Step, RLSStepEqUniformUpdate]
  apply PMFAEOfSupport
  intro y Supported
  obtain ⟨j, _Possible, Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Supported
  rw [← Equal]
  exact fun Lower => Lower.trans (UpdateFitnessNondecreasing x j)

/-- The exact probability of crossing level i under the original RLS kernel. -/
theorem StepFitnessLevelSuccess {n : ℕ} (PositiveLength : 0 < n) (i : Fin n) (x : Bits n)
    (AtLevel : LeadingOnes x = i) :
    (Step PositiveLength x).toMeasure.real {y | i.val + 1 ≤ LeadingOnes y} =
      (FitnessLevelProbability PositiveLength : ℝ) := by
  have Outside : LeadingOnes x < n := by rw [AtLevel]; exact i.isLt
  have Event : (Update x) ⁻¹' {y | i.val + 1 ≤ LeadingOnes y} = {i} := by
    ext j
    change i.val + 1 ≤ LeadingOnes (Update x j) ↔ j = i
    rw [← AtLevel, UpdateCrossesFitnessLevelIff x j Outside, AtLevel]
    exact Fin.ext_iff.symm
  rw [Step, RLSStepEqUniformUpdate]
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
    Measure.map_apply (measurable_of_finite _) (Set.to_countable _).measurableSet]
  change ((UniformBitIndex n PositiveLength).toMeasure
    ((Update x) ⁻¹' {y | i.val + 1 ≤ LeadingOnes y})).toReal = _
  rw [Event, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change (n : ℝ)⁻¹ = 1 / (n : ℝ)
  rw [one_div]

/-- The actual first hitting time is dominated by n independent Geom(1/n) waits. -/
theorem RuntimeFitnessLevelGeometricBound {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) Initial).map (FirstHittingTime (fun x => x = AllOnes n)))
      ((Measure.pi (fun _ : Fin n => geometricMeasure (FitnessLevelProbability PositiveLength))).map
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
    (fun _ => FitnessLevelProbability PositiveLength)
    (fun _ => FitnessLevelProbabilityPositive PositiveLength)
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
end ECTheoryLib.Analysis.RLSOnLeadingOnes
