import ECTheoryLib.Analysis.OneMax.RLSWithShortcuts.RuntimeBounds
import ECTheoryLib.Analysis.Linear.UniformInitialization
import ECTheoryLib.Tools.Drift.Potential.LogarithmicBounds

/-!
Uniform-start precision of the zero-safe drift upper-bound expression in Example2.3.6.
Finite constants and the initial optimum atom are explicit; this is not a runtime lower bound.
-/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped Classical
noncomputable section

def UniformBoundMean (n : ℕ) : ℝ := ∫ x : Bits n, Bound x ∂(RLSInit n).toMeasure

theorem UniformCountMean (n : ℕ) :
    (∫ x : Bits n, (OneMax x : ℝ) ∂(RLSInit n).toMeasure) = (n : ℝ) / 2 := by
  simpa [Problems.Linear.ScoreUnitWeights] using
    LinearInitialization.UniformLinearScoreExpectation (n := n) (fun _ => 1)

theorem UniformSuccessProbability (n : ℕ) :
    (RLSInit n).toMeasure {x : Bits n | (OneMax x : ℝ) = 0} = ((2 : ENNReal)^n)⁻¹ := by
  have GoalSet : {x : Bits n | (OneMax x : ℝ) = 0} = {fun _ => false} := by
    ext x
    exact CountZeroIff x
  rw [GoalSet, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]

theorem UniformSuccessProbabilityReal (n : ℕ) :
    (RLSInit n).toMeasure.real {x : Bits n | (OneMax x : ℝ) = 0} = ((2 : ℝ)^n)⁻¹ := by
  rw [measureReal_def, UniformSuccessProbability, ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

theorem UniformFailureProbabilityReal (n : ℕ) :
    (RLSInit n).toMeasure.real {x : Bits n | (OneMax x : ℝ) ≠ 0} = 1 - ((2 : ℝ)^n)⁻¹ := by
  change (RLSInit n).toMeasure.real {x : Bits n | (OneMax x : ℝ) = 0}ᶜ = _
  rw [probReal_compl_eq_one_sub (Set.to_countable _).measurableSet, UniformSuccessProbabilityReal]

private theorem CountGap {n : ℕ} (x : Bits n) : (OneMax x : ℝ) = 0 ∨ 1 ≤ (OneMax x : ℝ) := by
  by_cases Zero : OneMax x = 0
  · exact Or.inl (by simp [Zero])
  · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)

/-- The lower bound uses the actual uniform mean and a pointwise log comparison. -/
theorem UniformBoundLower {n : ℕ} (PositiveLength : 0 < n) :
    Coefficient n / 2 * (1 + Real.log (n : ℝ)) ≤ UniformBoundMean n := by
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  let f : Bits n → ℝ := fun x => ((OneMax x : ℝ) / (n : ℝ)) *
    ((1 + Real.log (n : ℝ)) / Delta n)
  have Pointwise : ∀ x, f x ≤ Bound x := by
    intro x
    exact MultiplicativePotentialLowerChord (Delta n) (n : ℝ) (OneMax x : ℝ)
      (DeltaPositive PositiveLength) AtLeastOne (CountGap x)
      (by exact_mod_cast Problems.OneMax.OneMaxLeN x)
  have IntegralLower : (∫ x, f x ∂(RLSInit n).toMeasure) ≤ UniformBoundMean n :=
    integral_mono Integrable.of_finite Integrable.of_finite Pointwise
  have IntegralValue : (∫ x, f x ∂(RLSInit n).toMeasure) =
      Coefficient n / 2 * (1 + Real.log (n : ℝ)) := by
    have Functions : f = fun x : Bits n =>
        (((1 + Real.log (n : ℝ)) / Delta n) / (n : ℝ)) * (OneMax x : ℝ) := by
      funext x
      dsimp [f]
      ring
    rw [Functions, integral_const_mul, UniformCountMean, CoefficientEqReciprocal PositiveLength]
    have NonzeroN : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr PositiveLength)
    have NonzeroDelta : Delta n ≠ 0 := ne_of_gt (DeltaPositive PositiveLength)
    field_simp
  rw [← IntegralValue]
  exact IntegralLower

/-- The upper integral keeps the zero branch instead of replacing log0 by a fictitious value. -/
theorem UniformBoundUpper {n : ℕ} (PositiveLength : 0 < n) :
    UniformBoundMean n ≤ Coefficient n * (1 - ((2 : ℝ)^n)⁻¹) * (1 + Real.log (n : ℝ)) := by
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  let K : ℝ := Coefficient n * (1 + Real.log (n : ℝ))
  let f : Bits n → ℝ := fun x => if (OneMax x : ℝ) = 0 then 0 else K
  have Scale : (1 + Real.log (n : ℝ)) / Delta n = K := by
    dsimp [K]
    rw [CoefficientEqReciprocal PositiveLength]
    ring
  have Pointwise : ∀ x, Bound x ≤ f x := by
    intro x
    have Range := MultiplicativePotentialUpperRange (Delta n) (n : ℝ) (OneMax x : ℝ)
      (DeltaPositive PositiveLength) AtLeastOne (CountGap x)
      (by exact_mod_cast Problems.OneMax.OneMaxLeN x)
    simpa only [Bound, Scale] using Range
  have IntegralUpper : UniformBoundMean n ≤ (∫ x, f x ∂(RLSInit n).toMeasure) :=
    integral_mono Integrable.of_finite Integrable.of_finite Pointwise
  have AsIndicator : f = {x : Bits n | (OneMax x : ℝ) ≠ 0}.indicator (fun _ => K) := by
    funext x
    by_cases Zero : (OneMax x : ℝ) = 0 <;> simp [f, Set.indicator_apply]
  have IntegralValue : (∫ x, f x ∂(RLSInit n).toMeasure) =
      Coefficient n * (1 - ((2 : ℝ)^n)⁻¹) * (1 + Real.log (n : ℝ)) := by
    rw [AsIndicator, integral_indicator_const _ (Set.to_countable _).measurableSet,
      smul_eq_mul, UniformFailureProbabilityReal]
    dsimp [K]
    ring
  rw [← IntegralValue]
  exact IntegralUpper

theorem UniformBoundFiniteComparison {n : ℕ} (PositiveLength : 0 < n) :
    (n : ℝ) / 4 * (1 + Real.log (n : ℝ)) ≤ UniformBoundMean n ∧
      UniformBoundMean n ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  have LogTermNonnegative : 0 ≤ 1 + Real.log (n : ℝ) := by
    linarith [Real.log_nonneg AtLeastOne]
  have Bounds := CoefficientBounds PositiveLength
  constructor
  · have Compared := mul_le_mul_of_nonneg_right Bounds.1 LogTermNonnegative
    exact (by nlinarith : (n : ℝ) / 4 * (1 + Real.log (n : ℝ)) ≤
      Coefficient n / 2 * (1 + Real.log (n : ℝ))).trans (UniformBoundLower PositiveLength)
  · have FailureLeOne : 1 - ((2 : ℝ)^n)⁻¹ ≤ 1 := sub_le_self 1 (by positivity)
    have ScaleNonnegative := mul_nonneg (CoefficientPositive PositiveLength).le LogTermNonnegative
    have DropAtom : Coefficient n * (1 - ((2 : ℝ)^n)⁻¹) * (1 + Real.log (n : ℝ)) ≤
        Coefficient n * (1 + Real.log (n : ℝ)) := by
      calc
        _ = (Coefficient n * (1 + Real.log (n : ℝ))) * (1 - ((2 : ℝ)^n)⁻¹) := by ring
        _ ≤ (Coefficient n * (1 + Real.log (n : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left FailureLeOne ScaleNonnegative
        _ = _ := mul_one _
    exact (UniformBoundUpper PositiveLength).trans
      (DropAtom.trans (mul_le_mul_of_nonneg_right Bounds.2 LogTermNonnegative))

/-- Explicit n log n comparison for positive logarithms; a bound-expression theorem only. -/
theorem UniformBoundLogComparison {n : ℕ} (AtLeastTwo : 2 ≤ n) :
    (1 / 4 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ UniformBoundMean n ∧
      UniformBoundMean n ≤ (1 + 1 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ) := by
  have PositiveLength : 0 < n := by omega
  have Bounds := UniformBoundFiniteComparison PositiveLength
  constructor
  · exact (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)] : (1 / 4 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (n : ℝ) / 4 * (1 + Real.log (n : ℝ))).trans Bounds.1
  · have LogTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have LogLower : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast AtLeastTwo)
    have OneLe : 1 ≤ Real.log (n : ℝ) / Real.log 2 :=
      (le_div_iff₀ LogTwoPositive).mpr (by simpa using LogLower)
    have Compared := mul_le_mul_of_nonneg_left
      (add_le_add_right OneLe (Real.log (n : ℝ))) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    apply Bounds.2.trans
    convert Compared using 1 <;> ring

theorem UniformVariableRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤ ENNReal.ofReal (UniformBoundMean n) := by
  have Actual := VariableRuntimeUpper PositiveLength (RLSInit n)
  simpa only [VariablePotentialEqBound PositiveLength, UniformBoundMean] using Actual

theorem UniformMultiplicativeRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤ ENNReal.ofReal (UniformBoundMean n) :=
  MultiplicativeRuntimeUpper PositiveLength (RLSInit n)

theorem UniformGeometricRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤ ENNReal.ofReal
      ((n : ℝ) * (1 - ((2 : ℝ)^n)⁻¹)) := by
  simpa only [UniformFailureProbabilityReal] using InitialFailureRuntimeUpper PositiveLength (RLSInit n)

theorem UniformBoundAtOne : UniformBoundMean 1 = 1 / 2 := by
  have Lower := UniformBoundLower (by decide : 0 < 1)
  have Upper := UniformBoundUpper (by decide : 0 < 1)
  norm_num [Coefficient] at Lower Upper
  exact le_antisymm Upper Lower

end
end ECTheoryLib.Analysis.RLSWithShortcuts

