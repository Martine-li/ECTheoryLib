import ECTheoryLib.Analysis.BitMutationLowerTail
import ECTheoryLib.Probability.Distributions.GeometricWaiting
import ECTheoryLib.Tools.Runtime.Cost
import ECTheoryLib.Problems.Comparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Universal lower tails for the actual standard (1+1) EA

Source: Doerr Theorem 1.9.4, printed pages 37-38. Keep the initialization
factor one half: the logarithmic bound has exponent (n/2)^epsilon.
The printed n^epsilon is refuted in Tests/UniversalEALowerTailSourceAudit.
Iteration time and evaluation cost 1+T are explicit; no finite-time
replacement of an infinite hitting time is used. Any linearly ordered
objective with a specified unique global maximum is supported.
-/

namespace ECTheoryLib.Analysis.UniversalEA
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Problems.TargetOneMax
open scoped unitInterval
noncomputable section

theorem UniqueMaximumSelectionPreservesTarget {Value : Type*} [LinearOrder Value] {n : ℕ} (Fitness : Bits n → Value) (Target : Bits n)
    (Unique : ∀ x, x≠Target → Fitness x<Fitness Target) (y : Bits n) :
    ElitistSelect (Problems.MaxNotWorse Fitness) Target y=Target := by
  by_cases Equal : y=Target
  · subst y
    simp [ElitistSelect]
  · exact ElitistSelectReject _ _ _ (not_le_of_gt (Unique y Equal))

/-- A universal finite-time lower tail on the actual standard EA kernel.
The only objective hypothesis is the specified unique global maximum. -/
theorem UniformRuntimePowerLowerTail {Value : Type*} [LinearOrder Value] {n : ℕ} (Positive : 0<n)
    (Fitness : Bits n → Value) (Target : Bits n)
    (Unique : ∀ x, x≠Target → Fitness x<Fitness Target) (t : ℕ) :
    (PathMeasure (OnePlusOneEAStep Positive (Problems.MaxNotWorse Fitness)) (OnePlusOneEAInit n)).real
      {Path | FirstHittingTime (fun x => x=Target) Path≤(t : WithTop ℕ)}≤
        (1-(1-1/(n : ℝ))^t/2)^n := by
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  let p : I := ⟨1/(n : ℝ),⟨by positivity,(div_le_one NPositive).mpr (Nat.one_le_cast.mpr Positive)⟩⟩
  have Rate : ENNReal.ofReal (p : ℝ)=(n : ENNReal)⁻¹ := by
    change ENNReal.ofReal (1/(n : ℝ))=(n : ENNReal)⁻¹
    rw [ENNReal.ofReal_div_of_pos NPositive,ENNReal.ofReal_one,ENNReal.ofReal_natCast,one_div]
  have Selection (x y : Bits n) : ElitistSelect (Problems.MaxNotWorse Fitness) x y=x ∨
      ElitistSelect (Problems.MaxNotWorse Fitness) x y=y := by
    unfold ElitistSelect
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have Bound := BitMutation.UniformSelectedMutationRuntimeLowerTail p Target
    (ElitistSelect (Problems.MaxNotWorse Fitness)) Selection
    (UniqueMaximumSelectionPreservesTarget Fitness Target Unique) t
  change _≤(1-(1-1/(n : ℝ))^t/2)^n at Bound
  have Kernel : (fun x : Bits n => (IndependentBitMutation (ENNReal.ofReal (p : ℝ))
        (MutationProbabilityBound p) x).map (ElitistSelect (Problems.MaxNotWorse Fitness) x))=
      OnePlusOneEAStep Positive (Problems.MaxNotWorse Fitness) := by
    funext x
    unfold OnePlusOneEAStep StandardBitMutation
    simp only [Rate]
  rwa [Kernel] at Bound

/-- The initialization factor one half remains in the exponential bound. -/
theorem UniformRuntimeExponentialLowerTail {Value : Type*} [LinearOrder Value] {n : ℕ} (Positive : 0<n)
    (Fitness : Bits n → Value) (Target : Bits n)
    (Unique : ∀ x, x≠Target → Fitness x<Fitness Target) (t : ℕ) :
    (PathMeasure (OnePlusOneEAStep Positive (Problems.MaxNotWorse Fitness)) (OnePlusOneEAInit n))
      {Path | FirstHittingTime (fun x => x=Target) Path≤(t : WithTop ℕ)}≤
        ENNReal.ofReal (Real.exp (-((n : ℝ)/2)*(1-1/(n : ℝ))^t)) := by
  have Bound := UniformRuntimePowerLowerTail Positive Fitness Target Unique t
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr Positive
  have FactorNonnegative : 0≤1-1/(n : ℝ) := by
    have Small : 1/(n : ℝ)≤1 := (div_le_one NPositive).mpr (Nat.one_le_cast.mpr Positive)
    linarith
  have FactorAtMostOne : 1-1/(n : ℝ)≤1 := by
    have := (one_div_pos.mpr NPositive).le
    linarith
  have PowerSmall := pow_le_one₀ FactorNonnegative FactorAtMostOne (n := t)
  have BaseNonnegative : 0≤1-(1-1/(n : ℝ))^t/2 := by linarith
  have Elementary : 1-(1-1/(n : ℝ))^t/2≤Real.exp (-((1-1/(n : ℝ))^t/2)) := by
    have Linear := Real.add_one_le_exp (-((1-1/(n : ℝ))^t/2))
    linarith
  have PowerBound : (1-(1-1/(n : ℝ))^t/2)^n≤Real.exp (-((n : ℝ)/2)*(1-1/(n : ℝ))^t) := by
    calc
      _≤(Real.exp (-((1-1/(n : ℝ))^t/2)))^n := pow_le_pow_left₀ BaseNonnegative Elementary n
      _=Real.exp (-((n : ℝ)/2)*(1-1/(n : ℝ))^t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact Bound.trans PowerBound

end
end ECTheoryLib.Analysis.UniversalEA


namespace ECTheoryLib.Analysis.UniversalEA
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Runtime
noncomputable section

/-- The logarithmic lower tail retains the initialization factor 1/2.
An arbitrary real epsilon is allowed provided the integer horizon is below
the stated real threshold. -/
theorem CorrectedLowerTailAtTime {Value : Type*} [LinearOrder Value] {n : ℕ} (AtLeastTwo : 2≤n)
    (Fitness : Bits n → Value) (Target : Bits n)
    (Unique : ∀ x, x≠Target → Fitness x<Fitness Target) (ε : ℝ) (t : ℕ)
    (Before : (t : ℝ)≤(1-ε)*((n : ℝ)-1)*Real.log ((n : ℝ)/2)) :
    (PathMeasure (OnePlusOneEAStep (by omega : 0<n) (Problems.MaxNotWorse Fitness))
      (OnePlusOneEAInit n))
      {Path | FirstHittingTime (fun x => x=Target) Path≤(t : WithTop ℕ)}≤
        ENNReal.ofReal (Real.exp (-((n : ℝ)/2)^ε)) := by
  have Positive : 0<n := by omega
  apply (UniformRuntimeExponentialLowerTail Positive Fitness Target Unique t).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have NAboveOne : (1 : ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have NPositive : (0 : ℝ)<n := by linarith
  have DenPositive : (0 : ℝ)<(n : ℝ)-1 := by linarith
  have HalfPositive : (0 : ℝ)<(n : ℝ)/2 := by positivity
  have Survival := BernoulliFailurePowerExponentialLower (1/(n : ℝ))
    ((div_lt_one NPositive).mpr NAboveOne) t
  have Rational : -(t : ℝ)*(1/(n : ℝ))/(1-1/(n : ℝ))= -(t : ℝ)/((n : ℝ)-1) := by
    field_simp
  rw [Rational] at Survival
  have Exponent : (ε-1)*Real.log ((n : ℝ)/2)≤ -(t : ℝ)/((n : ℝ)-1) := by
    apply (le_div_iff₀ DenPositive).mpr
    nlinarith
  have Missing := (Real.exp_le_exp.mpr Exponent).trans Survival
  have Scaled := mul_le_mul_of_nonneg_left Missing HalfPositive.le
  have Identity : ((n : ℝ)/2)*Real.exp ((ε-1)*Real.log ((n : ℝ)/2))=((n : ℝ)/2)^ε := by
    rw [Real.rpow_def_of_pos HalfPositive]
    calc
      _=Real.exp (Real.log ((n : ℝ)/2))*Real.exp ((ε-1)*Real.log ((n : ℝ)/2)) := by
        rw [Real.exp_log HalfPositive]
      _=Real.exp (Real.log ((n : ℝ)/2)*ε) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Identity] at Scaled
  linarith

/-- Source-style evaluation counts charge initialization. The formula is
valid for every real epsilon, with no truncation of a negative threshold to
time zero. Its exponent is (n/2)^epsilon, correcting the printed n^epsilon. -/
theorem CorrectedEvaluationLowerTail {Value : Type*} [LinearOrder Value] {n : ℕ} (AtLeastTwo : 2≤n)
    (Fitness : Bits n → Value) (Target : Bits n)
    (Unique : ∀ x, x≠Target → Fitness x<Fitness Target) (ε : ℝ) :
    (PathMeasure (OnePlusOneEAStep (by omega : 0<n) (Problems.MaxNotWorse Fitness))
      (OnePlusOneEAInit n))
      {Path | EvaluationCost (fun x => x=Target) 1 1 Path≤
        ENNReal.ofReal ((1-ε)*((n : ℝ)-1)*Real.log ((n : ℝ)/2))}≤
          ENNReal.ofReal (Real.exp (-((n : ℝ)/2)^ε)) := by
  let a : ℝ := (1-ε)*((n : ℝ)-1)*Real.log ((n : ℝ)/2)
  by_cases Nonnegative : 0≤a
  · have Included : {Path : ℕ → Bits n | EvaluationCost (fun x => x=Target) 1 1 Path≤ENNReal.ofReal a}⊆
        {Path | FirstHittingTime (fun x => x=Target) Path≤(⌊a⌋₊ : WithTop ℕ)} := by
      intro Path Before
      obtain ⟨k,Time,Cost⟩ := (UnitEvaluationCostLeOfRealIff (fun x => x=Target) Path a).mp Before
      change FirstHittingTime (fun x => x=Target) Path≤(⌊a⌋₊ : WithTop ℕ)
      rw [Time]
      have NaturalBefore : k≤⌊a⌋₊ := (Nat.le_floor_iff Nonnegative).mpr (by linarith)
      exact_mod_cast NaturalBefore
    exact (measure_mono Included).trans
      (CorrectedLowerTailAtTime AtLeastTwo Fitness Target Unique ε ⌊a⌋₊ (Nat.floor_le Nonnegative))
  · have Empty : {Path : ℕ → Bits n | EvaluationCost (fun x => x=Target) 1 1 Path≤ENNReal.ofReal a}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro Path Before
      obtain ⟨k,_,Cost⟩ := (UnitEvaluationCostLeOfRealIff (fun x => x=Target) Path a).mp Before
      have := (Nat.cast_nonneg k : (0 : ℝ)≤k)
      linarith
    change (PathMeasure _ _) {Path | EvaluationCost (fun x => x=Target) 1 1 Path≤ENNReal.ofReal a}≤_
    rw [Empty,measure_empty]
    exact zero_le

end
end ECTheoryLib.Analysis.UniversalEA

