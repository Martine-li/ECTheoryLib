import ECTheoryLib.Probability.Concentration.LogarithmicThreshold

/-!
# Failure-probability thresholds for power-tail bounds

The substitution t = exp(log(1/q)/alpha) connects the scalar threshold to the
bound (e*alpha/k)^k <= q. The full source range
0 < q <= exp(-alpha*exp(1/e)) is retained for alpha > 0.
At q = exp(-alpha*e), the explicitly repaired threshold is alpha*e^2.
These are scalar facts; actual random laws enter only in application modules.
-/

namespace ECTheoryLib.Probability.PowerTailThreshold
noncomputable section

/-- Scaled, explicitly corrected threshold for a target failure probability. It agrees with the source formula off its singular input and equals alpha times e squared at q = exp(-alpha*e). -/
def failureThreshold (α q : ℝ) : ℝ :=
  α * repairedThreshold (Real.exp (Real.log (1 / q) / α))

/-- The full original failure-probability range maps into the scalar source domain. -/
theorem failureThreshold_originalRange (α q : ℝ) (PositiveAlpha : 0 < α)
    (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1))) :
    Real.exp (Real.exp (1 / Real.exp 1)) ≤ Real.exp (Real.log (1 / q) / α) := by
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ PositiveAlpha).mpr
  have LogBound := Real.log_le_log PositiveQ SourceRange
  rw [Real.log_exp] at LogBound
  simp only [one_div, Real.log_inv] at LogBound ⊢
  nlinarith

/-- For positive alpha away from the singular input, retain the displayed nested-log formula. -/
theorem failureThreshold_agrees (α q : ℝ) (PositiveAlpha : 0 < α)
    (Nonsingular : Real.exp (Real.log (1 / q) / α) ≠ Real.exp (Real.exp 1)) :
    failureThreshold α q = Real.log (1 / q) /
      Real.log ((Real.log (1 / q) / α) /
        (Real.exp 1 * Real.log (Real.log (1 / q) / α))) := by
  rw [failureThreshold, repairedThreshold_agrees _ Nonsingular]
  simp only [displayedThreshold, logDenominator, Real.log_exp]
  rw [← mul_div_assoc, mul_comm α (Real.log (1 / q) / α),
    div_mul_cancel₀ _ PositiveAlpha.ne']

/-- Every threshold above the corrected value gives the requested power-tail bound. -/
theorem failureThreshold_powerBound (α q k : ℝ) (PositiveAlpha : 0 < α)
    (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)))
    (LargeThreshold : failureThreshold α q ≤ k) :
    (Real.exp 1 * α / k) ^ k ≤ q := by
  let L : ℝ := Real.log (1 / q) / α
  have Range := failureThreshold_originalRange α q PositiveAlpha PositiveQ SourceRange
  have DeltaPositive := repairedThreshold_positive (Real.exp L) Range
  have PositiveK : 0 < k := (mul_pos PositiveAlpha DeltaPositive).trans_le LargeThreshold
  have LargeRatio : repairedThreshold (Real.exp L) ≤ k / α := by
    apply (le_div_iff₀ PositiveAlpha).mpr
    simpa only [failureThreshold, mul_comm] using LargeThreshold
  have Scalar := repairedThreshold_larger_bound (Real.exp L) (k / α) Range LargeRatio
  have PositiveBase : 0 < Real.exp 1 / (k / α) :=
    div_pos (Real.exp_pos 1) (div_pos PositiveK PositiveAlpha)
  have Scaled := Real.rpow_le_rpow (Real.rpow_nonneg PositiveBase.le _) Scalar PositiveAlpha.le
  rw [← Real.rpow_mul PositiveBase.le, div_mul_cancel₀ _ PositiveAlpha.ne',
    div_div_eq_mul_div] at Scaled
  have RightSide : (1 / Real.exp L) ^ α = q := by
    rw [Real.rpow_def_of_pos (div_pos zero_lt_one (Real.exp_pos L)),
      one_div, Real.log_inv, Real.log_exp, neg_mul]
    have Cancel : L * α = Real.log (1 / q) := div_mul_cancel₀ _ PositiveAlpha.ne'
    rw [Cancel, one_div, Real.log_inv, neg_neg]
    exact Real.exp_log PositiveQ
  exact Scaled.trans_eq RightSide

/-- The singular probability exp(-alpha*e) belongs to the original range for every positive alpha. -/
theorem failureThreshold_singularQ_originalRange (α : ℝ) (PositiveAlpha : 0 < α) :
    0 < Real.exp (-α * Real.exp 1) ∧
      Real.exp (-α * Real.exp 1) ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) := by
  constructor
  · exact Real.exp_pos _
  · have ReciprocalAtMostOne : 1 / Real.exp 1 ≤ 1 :=
      (div_le_one (Real.exp_pos 1)).mpr (Real.one_le_exp zero_le_one)
    have ExpReciprocalAtMostE : Real.exp (1 / Real.exp 1) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr ReciprocalAtMostOne
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ExpReciprocalAtMostE (neg_nonpos.mpr PositiveAlpha.le)

/-- The singular probability maps exactly to the scalar singular input. -/
theorem failureThreshold_singularInput (α : ℝ) (PositiveAlpha : 0 < α) :
    Real.exp (Real.log (1 / Real.exp (-α * Real.exp 1)) / α) =
      Real.exp (Real.exp 1) := by
  have LogReciprocal : Real.log (1 / Real.exp (-α * Real.exp 1)) = α * Real.exp 1 := by
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  have ScaledLog : Real.log (1 / Real.exp (-α * Real.exp 1)) / α = Real.exp 1 := by
    rw [LogReciprocal]
    apply (div_eq_iff PositiveAlpha.ne').mpr
    ring
  exact congrArg Real.exp ScaledLog

/-- The explicit correction at the singular probability is alpha times e squared. -/
theorem failureThreshold_at_singularQ (α : ℝ) (PositiveAlpha : 0 < α) :
    failureThreshold α (Real.exp (-α * Real.exp 1)) =
      α * (Real.exp 1) ^ (2 : ℕ) := by
  rw [failureThreshold, failureThreshold_singularInput α PositiveAlpha]
  simp [repairedThreshold]

/-- For positive alpha and q, the scalar singular input corresponds exactly to q = exp(-alpha*e). -/
theorem failureThreshold_singularInput_iff (α q : ℝ)
    (PositiveAlpha : 0 < α) (PositiveQ : 0 < q) :
    Real.exp (Real.log (1 / q) / α) = Real.exp (Real.exp 1) ↔
      q = Real.exp (-α * Real.exp 1) := by
  constructor
  · intro Singular
    have ScaledLog : Real.log (1 / q) / α = Real.exp 1 := by
      simpa only [Real.log_exp] using congrArg Real.log Singular
    have LogReciprocal : Real.log (1 / q) = Real.exp 1 * α :=
      (div_eq_iff PositiveAlpha.ne').mp ScaledLog
    simp only [one_div, Real.log_inv] at LogReciprocal
    have LogQ : Real.log q = -α * Real.exp 1 := by
      nlinarith [LogReciprocal]
    calc
      q = Real.exp (Real.log q) := (Real.exp_log PositiveQ).symm
      _ = Real.exp (-α * Real.exp 1) := congrArg Real.exp LogQ
  · intro SingularQ
    rw [SingularQ]
    exact failureThreshold_singularInput α PositiveAlpha

end
end ECTheoryLib.Probability.PowerTailThreshold
