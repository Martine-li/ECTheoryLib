import ECTheoryLib.Analysis.Linear.UniformInitialization
import ECTheoryLib.Analysis.Linear.RLS.BinVal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity

/-!
Uniform-start precision of the two zero-safe BinVal potentials.
The quadratic comparison is about a bound expression, not a runtime lower bound.
-/
namespace ECTheoryLib.Analysis.RLSBinVal
open MeasureTheory ProbabilityTheory ECTheoryLib.Tools.Drift LinearInitialization
open ECTheoryLib.Problems.Linear.BinVal
open scoped BigOperators
noncomputable section

/-- Guard the logarithm at success rather than treating the source's log 0 as defined. -/
def GuardedLog {n : ℕ} (x : Bits n) : ℝ := if Score x = 0 then 0 else Real.log (Score x)

theorem UniformScoreExpectation (n : ℕ) :
    (∫ x : Bits n, Score x ∂(RLSInit n).toMeasure) = ((2 : ℝ) ^ n - 1) / 2 := by
  change (∫ x : Bits n, Problems.Linear.Score Weights x ∂(RLSInit n).toMeasure) = _
  rw [UniformLinearScoreExpectation, WeightsSum]

theorem UniformSuccessProbability (n : ℕ) :
    (RLSInit n).toMeasure {x : Bits n | Score x = 0} = ((2 : ENNReal) ^ n)⁻¹ := by
  have Event : {x : Bits n | Score x = 0} = {fun _ => false} := by
    ext x
    exact ScoreZeroIff x
  rw [Event, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]

theorem UniformSuccessProbabilityReal (n : ℕ) :
    (RLSInit n).toMeasure.real {x : Bits n | Score x = 0} = ((2 : ℝ) ^ n)⁻¹ := by
  rw [measureReal_def, UniformSuccessProbability, ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

/-- Includes the success atom, even at n=0; no runtime model is invoked here. -/
theorem UniformFitnessBoundIdentity (n : ℕ) :
    (∫ x : Bits n, FitnessBound x ∂(RLSInit n).toMeasure) =
      (n : ℝ) * (1 - ((2 : ℝ) ^ n)⁻¹ +
        ∫ x, GuardedLog x ∂(RLSInit n).toMeasure) := by
  classical
  have Pointwise (x : Bits n) : FitnessBound x =
      (n : ℝ) * ((1 - (if Score x = 0 then 1 else 0)) + GuardedLog x) := by
    by_cases Zero : Score x = 0
    · simp [FitnessBound, MultiplicativeDriftPotential, GuardedLog, Zero]
    · rw [FitnessBoundOfNonzero x Zero]
      simp [GuardedLog, Zero]
  have AtomIntegral : (∫ x : Bits n, (if Score x = 0 then (1 : ℝ) else 0)
      ∂(RLSInit n).toMeasure) = ((2 : ℝ) ^ n)⁻¹ := by
    calc
      _ = ∫ x, ({x : Bits n | Score x = 0} : Set (Bits n)).indicator 1 x
          ∂(RLSInit n).toMeasure := rfl
      _ = _ := (integral_indicator_one (Set.toFinite _).measurableSet).trans
        (UniformSuccessProbabilityReal n)
  simp_rw [Pointwise]
  rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, AtomIntegral]
  simp

theorem FitnessBoundNonnegative {n : ℕ} (x : Bits n) : 0 ≤ FitnessBound x := by
  by_cases Zero : Score x = 0
  · simp [FitnessBound, MultiplicativeDriftPotential, Zero]
  · rw [FitnessBoundOfNonzero x Zero]
    exact mul_nonneg (Nat.cast_nonneg n) (by
      linarith [Real.log_nonneg ((FitnessUnitGap x).resolve_left Zero)])

theorem FitnessBoundUpper {n : ℕ} (x : Bits n) :
    FitnessBound x ≤ (n : ℝ) * (1 + (n : ℝ) * Real.log 2) := by
  by_cases Zero : Score x = 0
  · simpa [FitnessBound, MultiplicativeDriftPotential, Zero] using
      mul_nonneg (Nat.cast_nonneg n) (by positivity : 0 ≤ 1 + (n : ℝ) * Real.log 2)
  · rw [FitnessBoundOfNonzero x Zero]
    have ScorePositive : 0 < Score x := lt_of_lt_of_le (by norm_num)
      ((FitnessUnitGap x).resolve_left Zero)
    have LogBound := Real.log_le_log ScorePositive
      ((ScoreLeMaximum x).trans (sub_le_self _ (by norm_num)))
    rw [Real.log_pow] at LogBound
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)

theorem WeightLeScoreOfOne {n : ℕ} (x : Bits n) (i : Fin n) (One : x i = true) :
    Weights i ≤ Score x := by
  unfold Problems.Linear.BinVal.Score Problems.Linear.Score
  have Term := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => Weights j * (if x j then (1 : ℝ) else 0))
    (fun j _ => by cases x j <;> simp [le_of_lt (WeightPositive j)]) (Finset.mem_univ i)
  simpa only [One, if_true, mul_one] using Term

theorem FirstBitFitnessBoundLower {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (One : x ⟨0, PositiveLength⟩ = true) :
    (n : ℝ) * (1 + ((n : ℝ) - 1) * Real.log 2) ≤ FitnessBound x := by
  have WeightBound := WeightLeScoreOfOne x ⟨0, PositiveLength⟩ One
  have Weight : Weights (⟨0, PositiveLength⟩ : Fin n) = (2 : ℝ) ^ (n - 1) := by simp [Weights]
  rw [Weight] at WeightBound
  have ScorePositive : 0 < Score x := (pow_pos (by norm_num : (0 : ℝ) < 2) _).trans_le WeightBound
  rw [FitnessBoundOfNonzero x ScorePositive.ne']
  have LogBound := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) WeightBound
  rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at LogBound
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)

theorem UniformFitnessBoundLower {n : ℕ} (PositiveLength : 0 < n) :
    (n : ℝ) / 2 * (1 + ((n : ℝ) - 1) * Real.log 2) ≤
      ∫ x : Bits n, FitnessBound x ∂(RLSInit n).toMeasure := by
  let C : ℝ := (n : ℝ) * (1 + ((n : ℝ) - 1) * Real.log 2)
  have Bound (x : Bits n) : (if x ⟨0, PositiveLength⟩ then C else 0) ≤ FitnessBound x := by
    cases Bit : x ⟨0, PositiveLength⟩ with
    | false => simpa only [Bit, Bool.false_eq_true, if_false] using FitnessBoundNonnegative x
    | true => simpa only [Bit, if_true, C] using FirstBitFitnessBoundLower PositiveLength x Bit
  calc
    _ = ∫ x : Bits n, (if x ⟨0, PositiveLength⟩ then C else 0)
        ∂(RLSInit n).toMeasure := by
      rw [UniformCoordinateIntegral ⟨0, PositiveLength⟩ (fun b => if b then C else 0)]
      simp only [Bool.false_eq_true, if_false, if_true, zero_add]
      dsimp [C]
      ring
    _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite Bound

private theorem InitialIntegralLeConstant {n : ℕ} (Initial : PMF (Bits n))
    (f : Bits n → ℝ) (C : ℝ) (Bound : ∀ x, f x ≤ C) :
    (∫ x, f x ∂Initial.toMeasure) ≤ C := by
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono (μ := Initial.toMeasure) Integrable.of_finite (integrable_const C) Bound

theorem InitialFitnessBoundUpper {n : ℕ} (Initial : PMF (Bits n)) :
    (∫ x, FitnessBound x ∂Initial.toMeasure) ≤ (n : ℝ) * (1 + (n : ℝ) * Real.log 2) :=
  InitialIntegralLeConstant Initial FitnessBound _ FitnessBoundUpper

theorem CountBoundUpper {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    CountBound x ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) := by
  have NgeOne : (1 : ℝ) ≤ n := by exact_mod_cast PositiveLength
  by_cases Zero : (OneMax x : ℝ) = 0
  · simpa [CountBound, MultiplicativeDriftPotential, Zero] using
      mul_nonneg (Nat.cast_nonneg n) (by linarith [Real.log_nonneg NgeOne])
  · rw [CountBoundOfNonzero x Zero]
    have CountPositive : 0 < (OneMax x : ℝ) := lt_of_lt_of_le (by norm_num)
      ((CountUnitGap x).resolve_left Zero)
    have CountLe : (OneMax x : ℝ) ≤ n := by exact_mod_cast Problems.OneMax.OneMaxLeN x
    exact mul_le_mul_of_nonneg_left (by linarith [Real.log_le_log CountPositive CountLe])
      (Nat.cast_nonneg n)

theorem InitialCountBoundUpper {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    (∫ x, CountBound x ∂Initial.toMeasure) ≤ (n : ℝ) * (1 + Real.log (n : ℝ)) :=
  InitialIntegralLeConstant Initial CountBound _ (CountBoundUpper PositiveLength)

/-- Explicit finite constants for the fitness-bound expression only. -/
theorem UniformFitnessBoundQuadratic {n : ℕ} (AtLeastTwo : 2 ≤ n) :
    Real.log 2 / 4 * (n : ℝ) ^ 2 ≤
        (∫ x : Bits n, FitnessBound x ∂(RLSInit n).toMeasure) ∧
      (∫ x : Bits n, FitnessBound x ∂(RLSInit n).toMeasure) ≤
        (1 + Real.log 2) * (n : ℝ) ^ 2 := by
  have NgeTwo : (2 : ℝ) ≤ n := by exact_mod_cast AtLeastTwo
  have LogPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · apply le_trans _ (UniformFitnessBoundLower (by omega : 0 < n))
    have Product : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) * Real.log 2 := by positivity
    nlinarith
  · apply (InitialFitnessBoundUpper (RLSInit n)).trans
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- Calls the actual variable-drift result, independently of exact harmonic runtime. -/
theorem UniformCountVariableRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (n : ℝ))) := by
  have Bound := CountVariableUpperBound PositiveLength (RLSInit n)
  simp_rw [VariableCountPotentialEqBound PositiveLength] at Bound
  exact Bound.trans (ENNReal.ofReal_le_ofReal (InitialCountBoundUpper PositiveLength _))

/-- A separate actual multiplicative-drift call with the same uniform initialization. -/
theorem UniformCountMultiplicativeRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤
      ENNReal.ofReal ((n : ℝ) * (1 + Real.log (n : ℝ))) :=
  (CountMultiplicativeUpperBound PositiveLength (RLSInit n)).trans
    (ENNReal.ofReal_le_ofReal (InitialCountBoundUpper PositiveLength _))

end
end ECTheoryLib.Analysis.RLSBinVal

