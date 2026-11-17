import ECTheoryLib.Problems.LeadingOnesCounting
import ECTheoryLib.Analysis.LeadingOnes.RLS.RuntimeBounds

/-!
# Uniform initialization for actual RLS on LeadingOnes

The actual RLSInit law gives Pr[LeadingOnes >= k] = 2^(-k) for 0 <= k <= n,
and zero beyond n. Its mean prefix length is 1-2^(-n), including n=0.
Consequently the coarse runtime bound becomes n*(n-1+2^(-n)).

The translated zero-safe potential in Example 2.3.2 has initial mean exactly n.
This alone does not prove runtime n^2/2: its later conditional drift requires
a separately verified unseen-suffix distribution invariant. See pp. 98-99,
equations (2.15)-(2.18), and the explicit scope in the E06m report.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes
noncomputable section

/-- Closed prefix tails of the actual uniform initial law, including k=0 and k=n. -/
theorem UniformPrefixProbability (n k : ℕ) (Within : k ≤ n) :
    (RLSInit n).toMeasure {x | k ≤ LeadingOnes x} = ((2 : ENNReal)^k)⁻¹ := by
  classical
  have Card : Fintype.card {x : Bits n | k ≤ LeadingOnes x} = 2^(n-k) := by
    rw [Fintype.card_subtype]
    have Count := PrefixCount n k Within
    simp only [Finset.sum_boole] at Count
    exact Count
  have TotalCard : Fintype.card (Bits n) = 2^n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [RLSInit, PMF.toMeasure_uniformOfFintype_apply _ (Set.to_countable _).measurableSet,
    Card, TotalCard, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat]
  have Powers : (2 : ENNReal)^n = (2 : ENNReal)^(n-k) * (2 : ENNReal)^k := by
    rw [← pow_add, Nat.sub_add_cancel Within]
  rw [Powers]
  calc
    _ = ((2 : ENNReal)^(n-k) * 1) / ((2 : ENNReal)^(n-k) * (2 : ENNReal)^k) := by rw [mul_one]
    _ = 1 / (2 : ENNReal)^k := ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)
    _ = _ := one_div _

/-- A requested prefix longer than the string has probability zero. -/
theorem UniformPrefixProbabilityOfTooLong (n k : ℕ) (Beyond : n < k) :
    (RLSInit n).toMeasure {x | k ≤ LeadingOnes x} = 0 := by
  have Empty : {x : Bits n | k ≤ LeadingOnes x} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x InEvent
    have Upper := LeadingOnesLeN x
    change k ≤ LeadingOnes x at InEvent
    omega
  rw [Empty, measure_empty]

/-- The actual uniform initialization has mean prefix length 1-2^(-n), also at n=0. -/
theorem UniformLeadingOnesExpectation (n : ℕ) :
    (∫ x, (LeadingOnes x : ℝ) ∂(RLSInit n).toMeasure) = 1 - (2 : ℝ)⁻¹^n := by
  rw [PMF.integral_eq_sum]
  simp only [RLSInitProbability, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← Finset.mul_sum, LeadingOnesTotal]
  rw [inv_pow]
  have Nonzero : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes
noncomputable section

/-- Exact mean deficit under uniform initialization, retaining optimal initial mass. -/
theorem UniformInitialPotentialExpectation (n : ℕ) :
    (∫ x, Potential x ∂(RLSInit n).toMeasure) = (n : ℝ) - 1 + (2 : ℝ)⁻¹^n := by
  have Difference (x : Bits n) : Potential x = (n : ℝ) - LeadingOnes x := by
    exact Nat.cast_sub (LeadingOnesLeN x)
  simp_rw [Difference]
  rw [integral_sub (integrable_const _) (Integrable.of_finite), integral_const,
    probReal_univ, one_smul, UniformLeadingOnesExpectation]
  ring

/-- The translated zero-safe potential from Example 2.3.2. -/
def TranslatedPotential {n : ℕ} (x : Bits n) : ℝ :=
  if x = AllOnes n then 0 else Potential x + 1

/-- Translating the deficit exactly cancels the finite-size initialization correction. -/
theorem UniformTranslatedPotentialExpectation (n : ℕ) :
    (∫ x, TranslatedPotential x ∂(RLSInit n).toMeasure) = (n : ℝ) := by
  classical
  let I : Bits n → ℝ := ({AllOnes n} : Set (Bits n)).indicator (fun _ => 1)
  have IndicatorMean : (∫ x, I x ∂(RLSInit n).toMeasure) = (2 : ℝ)⁻¹^n := by
    change (∫ x, ({AllOnes n} : Set (Bits n)).indicator (fun _ => (1 : ℝ)) x ∂(RLSInit n).toMeasure) = _
    rw [integral_indicator_const _ (measurableSet_singleton _), measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      smul_eq_mul, mul_one, inv_pow]
  have Difference (x : Bits n) : TranslatedPotential x = Potential x + 1 - I x := by
    by_cases Target : x = AllOnes n
    · have Zero := (PotentialZeroIffTarget x).mpr Target
      simp only [TranslatedPotential, I, Set.indicator_apply, Set.mem_singleton_iff, if_pos Target,
        Zero, zero_add, sub_self]
    · simp only [TranslatedPotential, I, Set.indicator_apply, Set.mem_singleton_iff,
        if_neg Target, sub_zero]
  simp_rw [Difference]
  have SumIntegrable : Integrable (fun x : Bits n => Potential x + 1) (RLSInit n).toMeasure :=
    (Integrable.of_finite (f := Potential)).add (integrable_const 1)
  rw [integral_sub SumIntegrable
      (Integrable.of_finite (f := I)),
    integral_add (Integrable.of_finite (f := Potential)) (integrable_const 1),
    UniformInitialPotentialExpectation, IndicatorMean, integral_const, probReal_univ, one_smul]
  ring

/-- The coarse drift bound with the exact uniform initial mean, sharper than n^2. -/
theorem UniformRuntimeUpperBound {n : ℕ} (PositiveLength : 0 < n) :
    ExpectedRuntime PositiveLength (RLSInit n) ≤
      ENNReal.ofReal ((n : ℝ) * ((n : ℝ) - 1 + (2 : ℝ)⁻¹^n)) := by
  have Bound := RuntimeUpperBound PositiveLength (RLSInit n)
  rw [UniformInitialPotentialExpectation] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
