import ECTheoryLib.Probability.Concentration.FailureThreshold

/-!
# Scalar thresholds for finitely many mutation calls

The original stronger failure range supplies a per-call budget q/T.
These theorems reuse failureThreshold without introducing another definition,
preserve positive natural horizons including T=1, and separate the singular
probability from its membership in the source domain. At the singular input
the explicit repaired threshold is alpha*e^2; away from it the displayed
log(T/q) formula is recovered.
-/

namespace ECTheoryLib.Probability.PowerTailThreshold

noncomputable section

/-- The source's stronger q range supplies the existing single-call range at q/T.
This ordered-field bridge itself does not require alpha to be positive. -/
theorem perCallBudget_originalRange (α q : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ)) :
    0 < q / (T : ℝ) ∧
      q / (T : ℝ) ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) := by
  have PositiveRealT : 0 < (T : ℝ) := Nat.cast_pos.mpr PositiveT
  have OneLeRealT : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr PositiveT
  refine ⟨div_pos PositiveQ PositiveRealT, ?_⟩
  calc
    q / (T : ℝ) ≤ q := div_le_self PositiveQ.le OneLeRealT
    _ ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ) := SourceRange
    _ ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) :=
      div_le_self (Real.exp_pos _).le OneLeRealT

/-- The corrected multi-call threshold is positive; consequently every larger k
is positive without adding a new positivity premise to the book's statement. -/
theorem failureThreshold_multiround_positive (α q : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveAlpha : 0 < α) (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ)) :
    0 < failureThreshold α (q / (T : ℝ)) := by
  have Budget := perCallBudget_originalRange α q T PositiveT PositiveQ SourceRange
  have Range := failureThreshold_originalRange α (q / (T : ℝ))
    PositiveAlpha Budget.1 Budget.2
  exact mul_pos PositiveAlpha (repairedThreshold_positive _ Range)

/-- The original multi-call q range and the inherited threshold give the required
per-call power bound. The real-power proof is reused, not repeated. -/
theorem failureThreshold_multiround_powerBound (α q k : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveAlpha : 0 < α) (PositiveQ : 0 < q)
    (SourceRange : q ≤ Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ))
    (LargeThreshold : failureThreshold α (q / (T : ℝ)) ≤ k) :
    (Real.exp 1 * α / k) ^ k ≤ q / (T : ℝ) := by
  have Budget := perCallBudget_originalRange α q T PositiveT PositiveQ SourceRange
  exact failureThreshold_powerBound α (q / (T : ℝ)) k PositiveAlpha
    Budget.1 Budget.2 LargeThreshold

/-- For positive alpha, q and T, the substituted scalar input is singular exactly
at q = T*exp(-alpha*e). This is not an unconditional assertion of source-domain
membership, nor a characterization of every total-log denominator zero. -/
theorem failureThreshold_multiround_singularInput_iff (α q : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveAlpha : 0 < α) (PositiveQ : 0 < q) :
    Real.exp (Real.log ((T : ℝ) / q) / α) = Real.exp (Real.exp 1) ↔
      q = (T : ℝ) * Real.exp (-α * Real.exp 1) := by
  have PositiveRealT : 0 < (T : ℝ) := Nat.cast_pos.mpr PositiveT
  calc
    Real.exp (Real.log ((T : ℝ) / q) / α) = Real.exp (Real.exp 1) ↔
        q / (T : ℝ) = Real.exp (-α * Real.exp 1) := by
      simpa only [one_div_div] using
        failureThreshold_singularInput_iff α (q / (T : ℝ)) PositiveAlpha
          (div_pos PositiveQ PositiveRealT)
    _ ↔ q = (T : ℝ) * Real.exp (-α * Real.exp 1) := by
      rw [div_eq_iff PositiveRealT.ne', mul_comm (Real.exp (-α * Real.exp 1))]

/-- Away from that singular probability, the corrected threshold equals the
book's exact nested-log expression with log(T/q). The identity does not itself
need the source upper bound on q; the power-bound theorem retains that bound. -/
theorem failureThreshold_multiround_agrees (α q : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveAlpha : 0 < α) (PositiveQ : 0 < q)
    (Nonsingular : q ≠ (T : ℝ) * Real.exp (-α * Real.exp 1)) :
    failureThreshold α (q / (T : ℝ)) = Real.log ((T : ℝ) / q) /
      Real.log ((Real.log ((T : ℝ) / q) / α) /
        (Real.exp 1 * Real.log (Real.log ((T : ℝ) / q) / α))) := by
  have InputNonsingular :
      Real.exp (Real.log ((T : ℝ) / q) / α) ≠ Real.exp (Real.exp 1) := by
    intro Singular
    exact Nonsingular ((failureThreshold_multiround_singularInput_iff α q T
      PositiveT PositiveAlpha PositiveQ).mp Singular)
  have OriginalInputNonsingular :
      Real.exp (Real.log (1 / (q / (T : ℝ))) / α) ≠ Real.exp (Real.exp 1) := by
    simpa only [one_div_div] using InputNonsingular
  simpa only [one_div_div] using
    failureThreshold_agrees α (q / (T : ℝ)) PositiveAlpha OriginalInputNonsingular

/-- The inherited correction at the multi-call singular q is alpha*e^2. -/
theorem failureThreshold_multiround_at_singularQ (α : ℝ) (T : ℕ)
    (PositiveT : 0 < T) (PositiveAlpha : 0 < α) :
    failureThreshold α (((T : ℝ) * Real.exp (-α * Real.exp 1)) / (T : ℝ)) =
      α * (Real.exp 1) ^ (2 : ℕ) := by
  have PositiveRealT : 0 < (T : ℝ) := Nat.cast_pos.mpr PositiveT
  rw [mul_div_cancel_left₀ _ PositiveRealT.ne']
  exact failureThreshold_at_singularQ α PositiveAlpha

/-- Exact extra condition for the singular q to lie in the original source
range. It must not be silently assumed for every positive T and alpha. -/
theorem failureThreshold_multiround_singularQ_originalRange_iff (α : ℝ) (T : ℕ)
    (PositiveT : 0 < T) :
    (T : ℝ) * Real.exp (-α * Real.exp 1) ≤
        Real.exp (-α * Real.exp (1 / Real.exp 1)) / (T : ℝ) ↔
      (T : ℝ) ^ (2 : ℕ) * Real.exp (-α * Real.exp 1) ≤
        Real.exp (-α * Real.exp (1 / Real.exp 1)) := by
  have PositiveRealT : 0 < (T : ℝ) := Nat.cast_pos.mpr PositiveT
  rw [le_div_iff₀ PositiveRealT]
  have Rearrange : ((T : ℝ) * Real.exp (-α * Real.exp 1)) * (T : ℝ) =
      (T : ℝ) ^ (2 : ℕ) * Real.exp (-α * Real.exp 1) := by ring
  rw [Rearrange]

end
end ECTheoryLib.Probability.PowerTailThreshold
