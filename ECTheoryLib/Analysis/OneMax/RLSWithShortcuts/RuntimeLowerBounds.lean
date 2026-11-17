import ECTheoryLib.Analysis.OneMax.RLSWithShortcuts.UniformInitialization
import ECTheoryLib.Tools.Runtime.Additive.NonabsorbingLower
import Mathlib.Analysis.Asymptotics.Defs

/-! Actual shortcut-RLS runtime lower bounds and precision.
The failure indicator is derived from the same selected kernel;the old
drift-bound expression is not an input runtime lower certificate. -/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift Filter
open scoped Classical
noncomputable section

/-- The complete selected kernel's exact0/1 failure decrease. -/
theorem FailureIndicatorDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, (if OneMax x = 0 then (0 : ℝ) else 1) -
      (if OneMax y = 0 then (0 : ℝ) else 1) ∂(Step PositiveLength x).toMeasure) =
        if OneMax x = 0 then 0 else if OneMax x = 1 then Delta n else 1 / (n : ℝ) := by
  let f : ℕ → ℝ := fun s => if s = 0 then 0 else 1
  have Formula := CountFunctionDrift PositiveLength x f
  by_cases Zero : OneMax x = 0
  · simpa [f,Zero] using Formula
  · by_cases One : OneMax x = 1
    · simp only [One,if_true]
      calc
        _ = 1 / (n : ℝ) + (1 - 1 / (n : ℝ)) * (1 / (n : ℝ)) := by
          simpa [f,One] using Formula
        _ = Delta n := by unfold Delta; ring
    · have Earlier : OneMax x - 1 ≠ 0 := by omega
      simpa [f,Zero,One,Earlier] using Formula

private theorem ReciprocalDimensionLeDelta {n : ℕ} (PositiveLength : 0 < n) :
    1 / (n : ℝ) ≤ Delta n := by
  have Bound := one_div_le_one_div_of_le (CoefficientPositive PositiveLength)
    (CoefficientBounds PositiveLength).2
  simpa only [CoefficientEqReciprocal PositiveLength,one_div_one_div] using Bound

/-- Lower bound for the real shortcut algorithm,retaining initial goal mass. -/
theorem InitialFailureRuntimeLower {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ENNReal.ofReal (Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0} / Delta n) ≤
      ExpectedRuntime PositiveLength Initial := by
  let V : Bits n → ℝ := fun x => if OneMax x = 0 then 0 else 1
  have Mean : (∫ x, V x ∂Initial.toMeasure) =
      Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0} := by
    have Functions : V = {x : Bits n | (OneMax x : ℝ) ≠ 0}.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases Zero : OneMax x = 0 <;> simp [V,Zero]
    rw [Functions,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  have Bound := Tools.Runtime.AdditiveRuntimeLowerBoundOfFiniteRangeNonabsorbing
    (Step PositiveLength) Initial V (fun x => (OneMax x : ℝ) = 0) (fun _ => True) {0,1}
    (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      rcases InS with rfl | rfl <;> norm_num)
    (by intro x; by_cases Zero : OneMax x = 0 <;> simp [V,Zero])
    (by intro x; by_cases Zero : OneMax x = 0 <;> simp [V,Zero])
    (ae_of_all _ (fun _ => trivial)) (fun _ => ae_of_all _ (fun _ _ => trivial))
    (Delta n) (DeltaPositive PositiveLength) (by
      intro x _ Nonzero
      have Away : OneMax x ≠ 0 := by
        intro Zero
        apply Nonzero
        simp [V,Zero]
      change (∫ y, (if OneMax x = 0 then (0 : ℝ) else 1) -
        (if OneMax y = 0 then (0 : ℝ) else 1) ∂(Step PositiveLength x).toMeasure) ≤ Delta n
      rw [FailureIndicatorDrift PositiveLength x,if_neg Away]
      split_ifs
      · exact le_rfl
      · exact ReciprocalDimensionLeDelta PositiveLength)
  rw [Mean] at Bound
  exact Bound

theorem InitialFailureRuntimeCoarseLower {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) :
    ENNReal.ofReal ((n : ℝ) / 2 * Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0}) ≤
      ExpectedRuntime PositiveLength Initial := by
  have Compared := mul_le_mul_of_nonneg_right (CoefficientBounds PositiveLength).1
    (measureReal_nonneg : 0 ≤ Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0})
  have Equal : Coefficient n * Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0} =
      Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0} / Delta n := by
    rw [CoefficientEqReciprocal PositiveLength]
    ring
  rw [Equal] at Compared
  exact (ENNReal.ofReal_le_ofReal Compared).trans (InitialFailureRuntimeLower PositiveLength Initial)

/-- At dimension1 every non-goal initialization needs exactly one update. -/
theorem RuntimeAtOne (Initial : PMF (Bits 1)) :
    ExpectedRuntime (by decide : 0 < 1) Initial =
      ENNReal.ofReal (Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0}) := by
  have Lower := InitialFailureRuntimeLower (by decide : 0 < 1) Initial
  have Upper := InitialFailureRuntimeUpper (by decide : 0 < 1) Initial
  rw [show Delta 1 = 1 by norm_num [Delta],div_one] at Lower
  rw [Nat.cast_one,one_mul] at Upper
  exact le_antisymm Upper Lower

/-- A pure single-one state attains the coefficient lower bound. -/
theorem SingleOneRuntimeExact {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Count : OneMax x = 1) :
    ExpectedRuntime PositiveLength (PMF.pure x) = ENNReal.ofReal (Coefficient n) := by
  have Nonzero : (OneMax x : ℝ) ≠ 0 := by simp [Count]
  have InitialFailure : (PMF.pure x).toMeasure.real {y | (OneMax y : ℝ) ≠ 0} = 1 := by
    simp [Measure.real,PMF.toMeasure_pure,Count]
  have Lower := InitialFailureRuntimeLower PositiveLength (PMF.pure x)
  rw [InitialFailure,← CoefficientEqReciprocal PositiveLength] at Lower
  have BoundValue : Bound x = Coefficient n := by
    simp [BoundOfNonzero PositiveLength x Nonzero,Count]
  have Upper := MultiplicativeRuntimeUpper PositiveLength (PMF.pure x)
  have UpperBound : ExpectedRuntime PositiveLength (PMF.pure x) ≤ ENNReal.ofReal (Coefficient n) := by
    simpa [PMF.toMeasure_pure,BoundValue] using Upper
  exact le_antisymm UpperBound Lower

private theorem UniformFailureAtLeastHalf {n : ℕ} (PositiveLength : 0 < n) :
    (1 / 2 : ℝ) ≤ (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} := by
  rw [UniformFailureProbabilityReal]
  have Power : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.succ_le_of_lt PositiveLength)
  have Inverse : ((2 : ℝ) ^ n)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) Power
  linarith

/-- Explicit actual uniform runtime constants;finiteness is used before toReal. -/
theorem UniformRuntimeFiniteBounds {n : ℕ} (PositiveLength : 0 < n) :
    (n : ℝ) / 4 ≤ (ExpectedRuntime PositiveLength (RLSInit n)).toReal ∧
      (ExpectedRuntime PositiveLength (RLSInit n)).toReal ≤ (n : ℝ) := by
  have Finite := RuntimeFinite PositiveLength (RLSInit n)
  have QNonnegative : 0 ≤ (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} := measureReal_nonneg
  have LowerNonnegative : 0 ≤ (n : ℝ) / 2 *
      (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg n) (by norm_num)) QNonnegative
  have Lower := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top Finite).mpr
    (InitialFailureRuntimeCoarseLower PositiveLength (RLSInit n))
  rw [ENNReal.toReal_ofReal LowerNonnegative] at Lower
  constructor
  · calc
      (n : ℝ) / 4 = (n : ℝ) / 2 * (1 / 2) := by ring
      _ ≤ (n : ℝ) / 2 * (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} :=
        mul_le_mul_of_nonneg_left (UniformFailureAtLeastHalf PositiveLength)
          (div_nonneg (Nat.cast_nonneg n) (by norm_num))
      _ ≤ _ := Lower
  · have Upper := (ENNReal.toReal_le_toReal Finite ENNReal.ofReal_ne_top).mpr
      (GeometricRuntimeUpper PositiveLength (RLSInit n))
    simpa only [ENNReal.toReal_ofReal (Nat.cast_nonneg n)] using Upper

/-- Theta(n) concerns the actual uniform-initial family at dimension k+1. -/
theorem UniformRuntimeFamilyIsTheta :
    (fun k => (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal) =Θ[atTop]
      (fun k => ((k + 1 : ℕ) : ℝ)) := by
  have Upper : (fun k => (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal) =O[atTop]
      (fun k => ((k + 1 : ℕ) : ℝ)) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall ?_⟩
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (k + 1)),one_mul]
    exact (UniformRuntimeFiniteBounds (Nat.succ_pos k)).2
  refine Upper.antisymm ?_
  refine Asymptotics.isBigO_iff.mpr ⟨4,Filter.Eventually.of_forall ?_⟩
  intro k
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (k + 1)),
    Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  have Lower := (UniformRuntimeFiniteBounds (Nat.succ_pos k)).1
  linarith

/-- Quantify the loss of the old drift upper-bound expression against real runtime. -/
theorem UniformBoundRuntimeRatioBounds {n : ℕ} (PositiveLength : 0 < n) :
    (1 + Real.log (n : ℝ)) / 4 ≤
        UniformBoundMean n / (ExpectedRuntime PositiveLength (RLSInit n)).toReal ∧
      UniformBoundMean n / (ExpectedRuntime PositiveLength (RLSInit n)).toReal ≤
        1 + Real.log (n : ℝ) := by
  have Finite := RuntimeFinite PositiveLength (RLSInit n)
  have Actual := UniformRuntimeFiniteBounds PositiveLength
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have PositiveRuntime : 0 < (ExpectedRuntime PositiveLength (RLSInit n)).toReal :=
    lt_of_lt_of_le (div_pos PositiveN (by norm_num)) Actual.1
  have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt PositiveLength
  have LogNonnegative : 0 ≤ 1 + Real.log (n : ℝ) := by
    linarith [Real.log_nonneg AtLeastOne]
  have QNonnegative : 0 ≤ (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} := measureReal_nonneg
  have Sharp := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top Finite).mpr
    (InitialFailureRuntimeLower PositiveLength (RLSInit n))
  rw [ENNReal.toReal_ofReal (div_nonneg QNonnegative (DeltaPositive PositiveLength).le)] at Sharp
  have CoefficientLower : Coefficient n * (1 - ((2 : ℝ) ^ n)⁻¹) ≤
      (ExpectedRuntime PositiveLength (RLSInit n)).toReal := by
    calc
      _ = (RLSInit n).toMeasure.real {x | (OneMax x : ℝ) ≠ 0} / Delta n := by
        rw [UniformFailureProbabilityReal,CoefficientEqReciprocal PositiveLength]
        ring
      _ ≤ _ := Sharp
  constructor
  · apply (le_div_iff₀ PositiveRuntime).mpr
    calc
      _ ≤ ((1 + Real.log (n : ℝ)) / 4) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left Actual.2 (div_nonneg LogNonnegative (by norm_num))
      _ = (n : ℝ) / 4 * (1 + Real.log (n : ℝ)) := by ring
      _ ≤ _ := (UniformBoundFiniteComparison PositiveLength).1
  · apply (div_le_iff₀ PositiveRuntime).mpr
    calc
      _ ≤ Coefficient n * (1 - ((2 : ℝ) ^ n)⁻¹) * (1 + Real.log (n : ℝ)) :=
        UniformBoundUpper PositiveLength
      _ ≤ (ExpectedRuntime PositiveLength (RLSInit n)).toReal * (1 + Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right CoefficientLower LogNonnegative
      _ = _ := mul_comm _ _

/-- The proved expression-to-runtime ratio has logarithmic order. -/
theorem UniformBoundRuntimeRatioFamilyIsTheta :
    (fun k => UniformBoundMean (k + 1) /
      (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal) =Θ[atTop]
        (fun k => Real.log ((k + 1 : ℕ) : ℝ)) := by
  have LogTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have Upper : (fun k => UniformBoundMean (k + 1) /
      (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal) =O[atTop]
        (fun k => Real.log ((k + 1 : ℕ) : ℝ)) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1 + 1 / Real.log 2,?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k AtLeastOne
    have Two : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
    have LogLower : Real.log 2 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) Two
    have LogNonnegative : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      le_trans (le_of_lt LogTwoPositive) LogLower
    have Bounds := UniformBoundRuntimeRatioBounds (Nat.succ_pos k)
    have RatioNonnegative : 0 ≤ UniformBoundMean (k + 1) /
        (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal := by
      linarith [Bounds.1]
    rw [Real.norm_eq_abs,abs_of_nonneg RatioNonnegative,Real.norm_eq_abs,abs_of_nonneg LogNonnegative]
    apply Bounds.2.trans
    have OneLe : 1 ≤ Real.log ((k + 1 : ℕ) : ℝ) / Real.log 2 :=
      (le_div_iff₀ LogTwoPositive).mpr (by simpa only [one_mul] using LogLower)
    calc
      _ ≤ Real.log ((k + 1 : ℕ) : ℝ) / Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ) := by linarith
      _ = _ := by ring
  refine Upper.antisymm ?_
  refine Asymptotics.isBigO_iff.mpr ⟨4,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k AtLeastOne
  have Two : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
  have LogNonnegative : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg (by linarith)
  have Bounds := UniformBoundRuntimeRatioBounds (Nat.succ_pos k)
  have RatioNonnegative : 0 ≤ UniformBoundMean (k + 1) /
      (ExpectedRuntime (Nat.succ_pos k) (RLSInit (k + 1))).toReal := by linarith [Bounds.1]
  rw [Real.norm_eq_abs,abs_of_nonneg LogNonnegative,Real.norm_eq_abs,abs_of_nonneg RatioNonnegative]
  linarith [Bounds.1]

end
end ECTheoryLib.Analysis.RLSWithShortcuts

