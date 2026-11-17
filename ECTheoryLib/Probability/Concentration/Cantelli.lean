import Mathlib.Probability.Moments.Variance

/-!
# Cantelli one-sided variance bounds

Book Lemma 1.6.10 follows from Mathlib Markov applied to a shifted centered
square. Raw offsets may have zero variance; standardized offsets require
positive variance. Every bound explicitly requires a finite second moment.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

private theorem CenteredShiftSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (b : ℝ) :
    (∫ ω, (X ω - (∫ z, X z ∂P) + b) ^ 2 ∂P) = variance X P + b ^ 2 := by
  have IntegrableX : Integrable X P := SquareIntegrable.integrable (by norm_num)
  have ShiftMem : MemLp (fun ω => X ω - (∫ z, X z ∂P) + b) 2 P :=
    (SquareIntegrable.sub (memLp_const _)).add (memLp_const _)
  have CenterIntegrable : Integrable (fun ω => X ω - (∫ z, X z ∂P)) P :=
    IntegrableX.sub (integrable_const _)
  have CenterMeasurable : AEStronglyMeasurable (fun ω => X ω - (∫ z, X z ∂P)) P :=
    SquareIntegrable.aestronglyMeasurable.sub aestronglyMeasurable_const
  have Mean : (∫ ω, X ω - (∫ z, X z ∂P) + b ∂P) = b := by
    rw [integral_add CenterIntegrable (integrable_const _),
      integral_sub IntegrableX (integrable_const _), integral_const, integral_const,
      probReal_univ, one_smul, one_smul]
    ring
  have VarianceEq := variance_eq_sub ShiftMem
  rw [variance_add_const CenterMeasurable,
    variance_sub_const SquareIntegrable.aestronglyMeasurable, Mean] at VarianceEq
  change variance X P = (∫ ω, (X ω - (∫ z, X z ∂P) + b) ^ 2 ∂P) - b ^ 2 at VarianceEq
  linarith

private theorem ShiftedSquareUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (c b : ℝ) (Positive : 0 < c) (NonnegativeB : 0 ≤ b) :
    P.real {ω | (∫ z, X z ∂P) + c ≤ X ω} ≤
      (variance X P + b ^ 2) / (c + b) ^ 2 := by
  have ShiftMem : MemLp (fun ω => X ω - (∫ z, X z ∂P) + b) 2 P :=
    (SquareIntegrable.sub (memLp_const _)).add (memLp_const _)
  have Nonnegative : 0 ≤ᵐ[P] (fun ω => (X ω - (∫ z, X z ∂P) + b) ^ 2) :=
    ae_of_all _ (fun ω => sq_nonneg _)
  have Markov := mul_meas_ge_le_integral_of_nonneg Nonnegative ShiftMem.integrable_sq ((c + b) ^ 2)
  rw [CenteredShiftSecondMoment P X SquareIntegrable b] at Markov
  have Subset : {ω | (∫ z, X z ∂P) + c ≤ X ω} ⊆
      {ω | (c + b) ^ 2 ≤ (X ω - (∫ z, X z ∂P) + b) ^ 2} := by
    intro ω Above
    change (∫ z, X z ∂P) + c ≤ X ω at Above
    have PositiveSum : 0 ≤ c + b := by linarith
    have Larger : c + b ≤ X ω - (∫ z, X z ∂P) + b := by linarith
    exact pow_le_pow_left₀ PositiveSum Larger 2
  calc
    P.real {ω | (∫ z, X z ∂P) + c ≤ X ω} ≤
        P.real {ω | (c + b) ^ 2 ≤ (X ω - (∫ z, X z ∂P) + b) ^ 2} :=
      measureReal_mono Subset
    _ ≤ (variance X P + b ^ 2) / (c + b) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < c + b))).mpr
      rw [mul_comm]
      exact Markov

/-- Upper-tail bound at a positive raw offset, including zero variance. -/
theorem CantelliUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (c : ℝ) (Positive : 0 < c) :
    P.real {ω | (∫ z, X z ∂P) + c ≤ X ω} ≤ variance X P / (variance X P + c ^ 2) := by
  have NonnegativeV := variance_nonneg X P
  -- The shift variance/c minimizes the shifted-square estimate.
  have Bound := ShiftedSquareUpperTail P X SquareIntegrable c (variance X P / c) Positive
    (div_nonneg NonnegativeV Positive.le)
  have PositiveDenominator : 0 < variance X P + c ^ 2 :=
    add_pos_of_nonneg_of_pos NonnegativeV (sq_pos_of_pos Positive)
  have PositiveShift : 0 < c + variance X P / c :=
    add_pos_of_pos_of_nonneg Positive (div_nonneg NonnegativeV Positive.le)
  have Ratio : (variance X P + (variance X P / c) ^ 2) / (c + variance X P / c) ^ 2 =
      variance X P / (variance X P + c ^ 2) := by
    field_simp
    ring
  rw [Ratio] at Bound
  exact Bound

/-- Lower-tail bound at a positive raw offset, obtained by negating the variable. -/
theorem CantelliLowerTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (c : ℝ) (Positive : 0 < c) :
    P.real {ω | X ω ≤ (∫ z, X z ∂P) - c} ≤ variance X P / (variance X P + c ^ 2) := by
  have Bound := CantelliUpperTail P (fun ω => -X ω) SquareIntegrable.neg c Positive
  rw [integral_neg, variance_fun_neg] at Bound
  have EventEq : {ω | -(∫ z, X z ∂P) + c ≤ -X ω} =
      {ω | X ω ≤ (∫ z, X z ∂P) - c} := by
    ext ω
    change -(∫ z, X z ∂P) + c ≤ -X ω ↔ X ω ≤ (∫ z, X z ∂P) - c
    constructor
    · intro Above
      linarith
    · intro Below
      linarith
  rw [EventEq] at Bound
  exact Bound

/-- Book 1.6.10 upper tail at Scale standard deviations. -/
theorem CantelliUpperTailStandardized {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (Scale : ℝ) (PositiveScale : 0 < Scale)
    (PositiveVariance : 0 < variance X P) :
    P.real {ω | (∫ z, X z ∂P) + Scale * Real.sqrt (variance X P) ≤ X ω} ≤
      1 / (Scale ^ 2 + 1) := by
  have PositiveThreshold : 0 < Scale * Real.sqrt (variance X P) :=
    mul_pos PositiveScale (Real.sqrt_pos.mpr PositiveVariance)
  have Bound := CantelliUpperTail P X SquareIntegrable _ PositiveThreshold
  rw [mul_pow, Real.sq_sqrt PositiveVariance.le] at Bound
  have Ratio : variance X P / (variance X P + Scale ^ 2 * variance X P) =
      1 / (Scale ^ 2 + 1) := by
    field_simp
    ring
  rw [Ratio] at Bound
  exact Bound

/-- Book 1.6.10 lower tail at Scale standard deviations. -/
theorem CantelliLowerTailStandardized {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (Scale : ℝ) (PositiveScale : 0 < Scale)
    (PositiveVariance : 0 < variance X P) :
    P.real {ω | X ω ≤ (∫ z, X z ∂P) - Scale * Real.sqrt (variance X P)} ≤
      1 / (Scale ^ 2 + 1) := by
  have PositiveThreshold : 0 < Scale * Real.sqrt (variance X P) :=
    mul_pos PositiveScale (Real.sqrt_pos.mpr PositiveVariance)
  have Bound := CantelliLowerTail P X SquareIntegrable _ PositiveThreshold
  rw [mul_pow, Real.sq_sqrt PositiveVariance.le] at Bound
  have Ratio : variance X P / (variance X P + Scale ^ 2 * variance X P) =
      1 / (Scale ^ 2 + 1) := by
    field_simp
    ring
  rw [Ratio] at Bound
  exact Bound

end
end ECTheoryLib.Probability

