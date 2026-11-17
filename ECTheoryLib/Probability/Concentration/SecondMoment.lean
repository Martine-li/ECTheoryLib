import ECTheoryLib.Probability.Concentration.Cantelli

/-!
# Second-moment bounds and the sign of the mean

Book Lemma 1.6.11 has a missing positive-mean condition for its nonpositive-event
claim. Zero-event bounds require only nonzero mean. All finite-moment obligations
are explicit, and positivity of the second moment is derived before division.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Nonzero mean and a finite second moment force the second moment to be positive. -/
theorem SecondMomentPositiveOfMeanNeZero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (MeanNeZero : (∫ ω, X ω ∂P) ≠ 0) :
    0 < ∫ ω, X ω ^ 2 ∂P := by
  have Identity := variance_eq_sub SquareIntegrable
  change variance X P = (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 at Identity
  have Nonnegative := variance_nonneg X P
  have Positive := sq_pos_of_ne_zero MeanNeZero
  linarith

/-- The tighter zero-event bound, valid for either sign of a nonzero mean. -/
theorem ZeroProbabilitySecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (MeanNeZero : (∫ ω, X ω ∂P) ≠ 0) :
    P.real {ω | X ω = 0} ≤ variance X P / (∫ ω, X ω ^ 2 ∂P) := by
  have Identity : variance X P + (∫ ω, X ω ∂P) ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
    have VarianceEq := variance_eq_sub SquareIntegrable
    change variance X P = (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 at VarianceEq
    linarith
  by_cases PositiveMean : 0 < ∫ ω, X ω ∂P
  · have Bound := CantelliLowerTail P X SquareIntegrable _ PositiveMean
    simp only [sub_self] at Bound
    rw [Identity] at Bound
    calc
      P.real {ω | X ω = 0} ≤ P.real {ω | X ω ≤ 0} := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω Zero
        change X ω = 0 at Zero
        change X ω ≤ 0
        exact Zero.le
      _ ≤ _ := Bound
  · have NegativeMean : (∫ ω, X ω ∂P) < 0 :=
      lt_of_le_of_ne (le_of_not_gt PositiveMean) MeanNeZero
    have Bound := CantelliUpperTail P X SquareIntegrable _ (neg_pos.mpr NegativeMean)
    simp only [add_neg_cancel, neg_sq] at Bound
    rw [Identity] at Bound
    calc
      P.real {ω | X ω = 0} ≤ P.real {ω | 0 ≤ X ω} := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω Zero
        change X ω = 0 at Zero
        change 0 ≤ X ω
        exact Zero.ge
      _ ≤ _ := Bound

/-- Corrected book 1.6.11 first bound: positive, not merely nonzero, mean is essential. -/
theorem NonpositiveProbabilityOfPositiveMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (PositiveMean : 0 < ∫ ω, X ω ∂P) :
    P.real {ω | X ω ≤ 0} ≤ variance X P / (∫ ω, X ω ∂P) ^ 2 := by
  have Bound := CantelliLowerTail P X SquareIntegrable _ PositiveMean
  simp only [sub_self] at Bound
  calc
    P.real {ω | X ω ≤ 0} ≤ variance X P / (variance X P + (∫ ω, X ω ∂P) ^ 2) := Bound
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (variance_nonneg X P) (sq_pos_of_pos PositiveMean)
      exact le_add_of_nonneg_left (variance_nonneg X P)

/-- The weaker zero-event bound also allows negative nonzero mean. -/
theorem ZeroProbabilityVarianceMeanSquare {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (MeanNeZero : (∫ ω, X ω ∂P) ≠ 0) :
    P.real {ω | X ω = 0} ≤ variance X P / (∫ ω, X ω ∂P) ^ 2 := by
  have Identity := variance_eq_sub SquareIntegrable
  change variance X P = (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 at Identity
  have Nonnegative := variance_nonneg X P
  have MeanSquareBelow : (∫ ω, X ω ∂P) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂P := by linarith
  exact (ZeroProbabilitySecondMoment P X SquareIntegrable MeanNeZero).trans
    (div_le_div_of_nonneg_left Nonnegative (sq_pos_of_ne_zero MeanNeZero) MeanSquareBelow)

/-- Equivalent lower bound on a nonzero outcome; signed variables are allowed. -/
theorem NonzeroProbabilitySecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (MeanNeZero : (∫ ω, X ω ∂P) ≠ 0) :
    (∫ ω, X ω ∂P) ^ 2 / (∫ ω, X ω ^ 2 ∂P) ≤ P.real {ω | X ω ≠ 0} := by
  have ZeroNull : NullMeasurableSet {ω | X ω = 0} P :=
    SquareIntegrable.aemeasurable.nullMeasurable (measurableSet_singleton 0)
  have Complement : {ω | X ω ≠ 0} = {ω | X ω = 0}ᶜ := rfl
  rw [Complement, measureReal_compl₀ ZeroNull, probReal_univ]
  have PositiveSecond := SecondMomentPositiveOfMeanNeZero P X SquareIntegrable MeanNeZero
  have Bound := ZeroProbabilitySecondMoment P X SquareIntegrable MeanNeZero
  have Product := (le_div_iff₀ PositiveSecond).mp Bound
  have Identity := variance_eq_sub SquareIntegrable
  change variance X P = (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 at Identity
  apply (div_le_iff₀ PositiveSecond).mpr
  nlinarith

/-- For an almost-surely nonnegative variable, nonzero means strictly positive. -/
theorem PositiveProbabilitySecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (SquareIntegrable : MemLp X 2 P) (MeanNeZero : (∫ ω, X ω ∂P) ≠ 0)
    (Nonnegative : 0 ≤ᵐ[P] X) :
    (∫ ω, X ω ∂P) ^ 2 / (∫ ω, X ω ^ 2 ∂P) ≤ P.real {ω | 0 < X ω} := by
  have EventEq : {ω | X ω ≠ 0} =ᵐ[P] {ω | 0 < X ω} := by
    filter_upwards [Nonnegative] with ω NonnegativeX
    apply propext
    exact ne_iff_lt_or_gt.trans (or_iff_right (not_lt.mpr NonnegativeX))
  rw [← measureReal_congr EventEq]
  exact NonzeroProbabilitySecondMoment P X SquareIntegrable MeanNeZero

end
end ECTheoryLib.Probability


