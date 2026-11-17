import ECTheoryLib.Tools.Drift.GeneralExponentialLowerTail

/-!
# General-target exponential upper tails

Full-history moments and the original first hitting time are retained without
original absorption. The strict fixed-start bound requires strict potential
comparison and positive parameters, as in Lehre-Witt Theorem 2(iii). The book's
weak-comparison strict formula has the preserved flat-potential counterexample.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Full-history weak upper tail for any initial law and a possibly nonabsorbing
process. The factor is the killed exponential expectation at initialization. -/
theorem GeneralExponentialDriftUpperTailOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ j, 0 ≤ beta j)
    (PotentialAbove : ∀ s ∈ S, a < s → g a ≤ g s)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X (j + 1) u) - g (X j u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, beta j) *
        (∫ ω, KilledExponentialPotential a Lambda g (X 0 ω) ∂μ)) := by
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let K := KilledExponentialPotential a Lambda g
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Sign (v w : ℝ) : (-Lambda) * (v - w) = Lambda * (w - v) := by ring
  have Decay := KilledExponentialLowerExpectationBoundOfCondExp μ X F AdaptedX S a (-Lambda) g beta
    Values NonnegativeBeta (by intro j; simpa only [Sign] using Moment j) t
  simp only [neg_neg] at Decay
  have IntegrableK : Integrable (fun ω => K (Y t ω)) μ :=
    FiniteStateCompositionIntegrable μ (Y t) S K AdaptedY.measurable (YValues t)
  have Markov := IntegrableK.measure_le_integral
    (ae_of_all μ (fun ω => KilledExponentialNonnegative a Lambda g (Y t ω)))
    (s := {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)}) (by
      intro ω Survives
      have Above : a < Y t ω := by
        apply lt_of_not_ge
        intro Hit
        exact (not_le_of_gt Survives) ((StopAtFirstHitGoalIff _ X t ω).mp Hit)
      change 1 ≤ KilledExponentialPotential a Lambda g (Y t ω)
      rw [KilledExponentialPotential, if_neg (not_le_of_gt Above)]
      exact Real.one_le_exp_iff.mpr
        (mul_nonneg NonnegativeLambda (sub_nonneg.mpr (PotentialAbove _ (YValues t ω) Above))))
  exact Markov.trans (ENNReal.ofReal_le_ofReal Decay)

/-- The corrected strict fixed-start upper bound, including time zero and
infinite first hitting times. No comparison below the target is required. -/
theorem StrictGeneralExponentialDriftUpperTailOfFixedInitial
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (a s₀ Lambda : ℝ) (g : ℝ → ℝ)
    (beta : ℕ → ℝ) (Values : ∀ j ω, X j ω ∈ S)
    (PositiveLambda : 0 < Lambda) (PositiveBeta : ∀ j, 0 < beta j)
    (PotentialAbove : ∀ s ∈ S, a < s → g a < g s)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (Moment : ∀ j, ∀ᵐ ω ∂μ, a < X j ω →
      (μ[fun u => Real.exp (Lambda * (g (X (j + 1) u) - g (X j u))) | F j]) ω ≤ beta j)
    (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} <
      ENNReal.ofReal ((∏ j ∈ Finset.range t, beta j) * Real.exp (Lambda * (g s₀ - g a))) := by
  classical
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  let A := {ω | a < Y t ω}
  let K := fun ω => KilledExponentialPotential a Lambda g (Y t ω)
  let I := A.indicator (fun _ : Ω => (1 : ℝ))
  let B := (∏ j ∈ Finset.range t, beta j) * Real.exp (Lambda * (g s₀ - g a))
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω ∈ S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Event : MeasurableSet A := measurableSet_lt measurable_const AdaptedY.measurable
  have EventEqual : {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} = A := by
    ext ω
    change (t : WithTop ℕ) < FirstHittingTime _ _ ↔ a < Y t ω
    rw [← not_le, ← StopAtFirstHitGoalIff, not_le]
  rw [EventEqual]
  have PositiveB : 0 < B := mul_pos (Finset.prod_pos (fun j _ => PositiveBeta j)) (Real.exp_pos _)
  by_cases Null : μ A = 0
  · rw [Null]
    exact ENNReal.ofReal_pos.mpr PositiveB
  have IntegrableI : Integrable I μ := (integrable_const (1 : ℝ)).indicator Event
  have IntegrableK : Integrable K μ := FiniteStateCompositionIntegrable μ (Y t) S
    (KilledExponentialPotential a Lambda g) AdaptedY.measurable (YValues t)
  have AboveOne (ω : Ω) (Above : ω ∈ A) : 1 < K ω := by
    change a < Y t ω at Above
    change 1 < KilledExponentialPotential a Lambda g (Y t ω)
    rw [KilledExponentialPotential, if_neg (not_le_of_gt Above)]
    exact Real.one_lt_exp_iff.mpr (mul_pos PositiveLambda (sub_pos.mpr (PotentialAbove _ (YValues t ω) Above)))
  have Comparison : I ≤ᵐ[μ] K := ae_of_all μ (by
    intro ω
    by_cases Above : ω ∈ A
    · exact (show I ω = 1 from Set.indicator_of_mem Above _).le.trans (AboveOne ω Above).le
    · rw [show I ω = 0 from Set.indicator_of_notMem Above _]
      exact KilledExponentialNonnegative a Lambda g (Y t ω))
  have StrictIntegral : (∫ ω, I ω ∂μ) < ∫ ω, K ω ∂μ := by
    apply lt_of_le_of_ne (integral_mono_ae IntegrableI IntegrableK Comparison)
    intro Equal
    have Same := (integral_eq_iff_of_ae_le IntegrableI IntegrableK Comparison).mp Equal
    have Outside : ∀ᵐ ω ∂μ, ω ∉ A := by
      filter_upwards [Same] with ω Same
      intro Above
      have One : I ω = 1 := Set.indicator_of_mem Above _
      have Strict := AboveOne ω Above
      linarith
    exact Null (by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using Outside)
  have Sign (v w : ℝ) : (-Lambda) * (v - w) = Lambda * (w - v) := by ring
  have Decay := KilledExponentialLowerExpectationBoundOfCondExp μ X F AdaptedX S a (-Lambda) g beta
    Values (fun j => (PositiveBeta j).le) (by intro j; simpa only [Sign] using Moment j) t
  simp only [neg_neg] at Decay
  have InitialIntegral : (∫ ω, KilledExponentialPotential a Lambda g (X 0 ω) ∂μ) =
      Real.exp (Lambda * (g s₀ - g a)) := by
    calc
      _ = ∫ _ω : Ω, Real.exp (Lambda * (g s₀ - g a)) ∂μ := integral_congr_ae (by
        filter_upwards [FixedInitial] with ω Equal
        rw [Equal, KilledExponentialPotential, if_neg (not_le_of_gt InitialAbove)])
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  rw [InitialIntegral] at Decay
  have ProbabilityIntegral : (∫ ω, I ω ∂μ) = (μ A).toReal := by
    rw [integral_indicator_const 1 Event, smul_eq_mul, mul_one, measureReal_def]
  apply (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ A)).mpr
  rw [← ProbabilityIntegral]
  exact StrictIntegral.trans_le Decay

end
end ECTheoryLib.Tools.Drift
