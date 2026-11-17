import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous exponential tails and signed expectations

Corollary 1.6.2(c), Benjamin Doerr, in Theory of Evolutionary Computation
(Doerr and Neumann, eds., 2020), pp. 16-17. The continuous additive premise
uses every positive real offset, unlike the integer-offset premise in (a).
Signed integrable real variables and the full nonnegative center are retained.
Mathlib supplies the layer-cake formula and exponential integral.
The real-valued theorem includes the source signed-integer scope.
-/

namespace ECTheoryLib.Probability

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Continuous positive-offset exponential tails control the expected positive
deviation. No finite expectation or probability-measure premise is needed. -/
theorem PositiveDeviationLIntegralLeOfContinuousExponentialTail
    (μ : Measure Ω) (X : Ω → ℝ) (T α β : ℝ)
    (XMeasurable : AEMeasurable X μ)
    (NonnegativeAlpha : 0 ≤ α) (PositiveBeta : 0 < β)
    (Tail : ∀ u : ℝ, 0 < u → μ {ω | T + u ≤ X ω} ≤
      ENNReal.ofReal (α * Real.exp (-u / β))) :
    (∫⁻ ω, ENNReal.ofReal (max (X ω - T) 0) ∂μ) ≤ ENNReal.ofReal (α * β) := by
  let q : ℝ := -(1 / β)
  have NegativeQ : q < 0 := neg_neg_of_pos (one_div_pos.mpr PositiveBeta)
  have KernelIntegrable : IntegrableOn (fun u : ℝ => α * Real.exp (q * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi NegativeQ 0).const_mul α
  have KernelIntegral : (∫ u : ℝ in Ioi 0, α * Real.exp (q * u)) = α * β := by
    rw [integral_const_mul, integral_exp_mul_Ioi NegativeQ]
    simp [q, one_div]
  have KernelLIntegral :
      (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (α * Real.exp (q * u))) =
        ENNReal.ofReal (α * β) := by
    rw [← ofReal_integral_eq_lintegral_ofReal KernelIntegrable
      (ae_of_all _ (fun u => mul_nonneg NonnegativeAlpha (Real.exp_nonneg _))),
      KernelIntegral]
  calc
    _ = ∫⁻ u : ℝ in Ioi 0, μ {ω | u ≤ max (X ω - T) 0} :=
      lintegral_eq_lintegral_meas_le μ (ae_of_all _ (fun ω => le_max_right _ _))
        ((XMeasurable.sub aemeasurable_const).max aemeasurable_const)
    _ ≤ ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (α * Real.exp (q * u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u PositiveU
      have Event : {ω | u ≤ max (X ω - T) 0} = {ω | T + u ≤ X ω} := by
        ext ω
        change u ≤ max (X ω - T) 0 ↔ T + u ≤ X ω
        rw [le_max_iff]
        constructor
        · intro Bound
          rcases Bound with Left | Right
          · linarith
          · exact False.elim ((not_le.mpr PositiveU) Right)
        · intro Bound
          left
          linarith
      rw [Event]
      have Exponent : q * u = -u / β := by dsimp [q]; ring
      rw [Exponent]
      exact Tail u PositiveU
    _ = _ := KernelLIntegral

/-- An arbitrary real center is valid when the upper-tail premise covers every
positive real offset. Negative values of the integrable variable are allowed. -/
theorem ExpectedRealLeOfContinuousExponentialTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (T α β : ℝ)
    (XIntegrable : Integrable X μ)
    (NonnegativeAlpha : 0 ≤ α) (PositiveBeta : 0 < β)
    (Tail : ∀ u : ℝ, 0 < u → μ {ω | T + u ≤ X ω} ≤
      ENNReal.ofReal (α * Real.exp (-u / β))) :
    (∫ ω, X ω ∂μ) ≤ T + α * β := by
  let Z := fun ω => max (X ω - T) 0
  have ZIntegrable : Integrable Z μ := (XIntegrable.sub (integrable_const T)).pos_part
  have ZNonnegative : 0 ≤ᵐ[μ] Z := ae_of_all _ (fun ω => le_max_right _ _)
  have Bound := PositiveDeviationLIntegralLeOfContinuousExponentialTail μ X T α β
    XIntegrable.aemeasurable NonnegativeAlpha PositiveBeta Tail
  change (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) ≤ _ at Bound
  rw [← ofReal_integral_eq_lintegral_ofReal ZIntegrable ZNonnegative] at Bound
  have ZBound : (∫ ω, Z ω ∂μ) ≤ α * β :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg NonnegativeAlpha PositiveBeta.le)).mp Bound
  calc
    (∫ ω, X ω ∂μ) ≤ ∫ ω, T + Z ω ∂μ := by
      apply integral_mono XIntegrable ((integrable_const T).add ZIntegrable)
      intro ω
      have := le_max_left (X ω - T) 0
      dsimp [Z]
      linarith
    _ = T + ∫ ω, Z ω ∂μ := by rw [integral_add (integrable_const T) ZIntegrable]; simp
    _ ≤ T + α * β := add_le_add le_rfl ZBound

/-- Book Corollary 1.6.2(c), generalized from integer to integrable real X.
The center T may be zero; the full quantifier over positive real epsilon is
essential there as well as for the continuous-integral argument. -/
theorem ExpectedRealLeOfMultiplicativeExponentialTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (T α β : ℝ)
    (XIntegrable : Integrable X μ) (NonnegativeT : 0 ≤ T)
    (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ ε : ℝ, 0 < ε → μ {ω | (1 + ε) * T ≤ X ω} ≤
      ENNReal.ofReal (α * Real.exp (-ε / β))) :
    (∫ ω, X ω ∂μ) ≤ (1 + α * β) * T := by
  rcases NonnegativeT.eq_or_lt with Zero | PositiveT
  · subst T
    have ConstantTail (r : ℝ) (PositiveR : 0 < r) :
        μ.real {ω | 0 ≤ X ω} ≤ α * Real.exp (-r) := by
      have Bound := Tail (β * r) (mul_pos PositiveBeta PositiveR)
      have Exponent : -(β * r) / β = -r := by field_simp
      simp only [mul_zero, Exponent] at Bound
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top Bound).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg PositiveAlpha.le (Real.exp_nonneg _)))
    have Decay : Tendsto (fun r : ℝ => α * Real.exp (-r)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := α)).mul Real.tendsto_exp_neg_atTop_nhds_zero
    have TailNonpositive : μ.real {ω | 0 ≤ X ω} ≤ 0 :=
      ge_of_tendsto Decay (eventually_atTop.mpr ⟨1, fun r Bound => ConstantTail r (by linarith)⟩)
    have NullTail : μ {ω | 0 ≤ X ω} = 0 := by
      apply le_antisymm _ bot_le
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mp
      exact TailNonpositive
    have NonpositiveX : X ≤ᵐ[μ] 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp NullTail] with ω Negative
      exact (lt_of_not_ge Negative).le
    simpa using integral_nonpos_of_ae NonpositiveX
  · have AdditiveTail : ∀ u : ℝ, 0 < u → μ {ω | T + u ≤ X ω} ≤
        ENNReal.ofReal (α * Real.exp (-u / (β * T))) := by
      intro u PositiveU
      have Bound := Tail (u / T) (div_pos PositiveU PositiveT)
      have Center : (1 + u / T) * T = T + u := by field_simp
      have Exponent : -(u / T) / β = -u / (β * T) := by ring
      rwa [Center, Exponent] at Bound
    have Bound := ExpectedRealLeOfContinuousExponentialTail μ X T α (β * T)
      XIntegrable PositiveAlpha.le (mul_pos PositiveBeta PositiveT) AdditiveTail
    convert Bound using 1
    ring

end
end ECTheoryLib.Probability


namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section

/-- A nonnegative-variable repair of book Corollary 1.6.2(d), generalized from
integer to integrable real X. The source's signed-X statement is false; almost
everywhere nonnegativity is an additional substantive assumption. The premise
uses every real epsilon in (0, 1] and the closed lower-tail event. -/
theorem ExpectedRealGeOfMultiplicativeExponentialLowerTail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (T α β : ℝ)
    (XIntegrable : Integrable X μ) (NonnegativeX : 0 ≤ᵐ[μ] X)
    (NonnegativeT : 0 ≤ T) (PositiveAlpha : 0 < α) (PositiveBeta : 0 < β)
    (Tail : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → μ {ω | X ω ≤ (1 - ε) * T} ≤
      ENNReal.ofReal (α * Real.exp (-ε / β))) :
    (1 - α * β) * T ≤ ∫ ω, X ω ∂μ := by
  rcases NonnegativeT.eq_or_lt with Zero | PositiveT
  · subst T
    simpa only [mul_zero] using integral_nonneg_of_ae NonnegativeX
  · have DeficitTail : ∀ u : ℝ, 0 < u → μ {ω | 0 + u ≤ T - X ω} ≤
        ENNReal.ofReal (α * Real.exp (-u / (β * T))) := by
      intro u PositiveU
      by_cases Within : u ≤ T
      · have Bound := Tail (u / T) (div_pos PositiveU PositiveT)
          ((div_le_one PositiveT).mpr Within)
        have Center : (1 - u / T) * T = T - u := by field_simp
        have Event : {ω | 0 + u ≤ T - X ω} = {ω | X ω ≤ (1 - u / T) * T} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Center]
          constructor <;> intro Bound <;> linarith
        have Exponent : -(u / T) / β = -u / (β * T) := by ring
        rw [Event]
        simpa only [Exponent] using Bound
      · have Null : μ {ω | 0 + u ≤ T - X ω} = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [NonnegativeX] with ω Nonnegative
          change 0 ≤ X ω at Nonnegative
          linarith
        rw [Null]
        exact zero_le
    have Bound := ExpectedRealLeOfContinuousExponentialTail μ (fun ω => T - X ω)
      0 α (β * T) ((integrable_const T).sub XIntegrable) PositiveAlpha.le
      (mul_pos PositiveBeta PositiveT) DeficitTail
    have MeanDeficit : (∫ ω, T - X ω ∂μ) = T - ∫ ω, X ω ∂μ := by
      rw [integral_sub (integrable_const T) XIntegrable]
      simp
    rw [MeanDeficit] at Bound
    nlinarith [Bound]

end
end ECTheoryLib.Probability

