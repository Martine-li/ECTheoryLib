import ECTheoryLib.Probability.Moments.GeometricTailMoment
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditional geometric jump tails and integrable moments

Reuse regular conditional laws to lift the scalar geometric-tail estimate.
Localization to a past event ignores uncontrolled inactive increments.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- A complete-history geometric absolute tail gives genuine absolute
exponential integrability and its conditional bound, with no finite range.
Mathlib's regular conditional law carries the already proved scalar result. -/
theorem ConditionalAbsoluteExponentialMomentOfJumpTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (Below : m ≤ m0) (Z : Ω → ℝ) (eta r : ℝ)
    (PositiveEta : 0<eta) (NonnegativeR : 0≤r) (Observable : Measurable[m0] Z)
    (Tail : ∀ j : ℕ, (μ[({ω | (j : ℝ)≤|Z ω|}).indicator (fun _ => (1 : ℝ)) | m]) ≤ᵐ[μ]
      (fun _ => r/(1+eta)^j)) :
    Integrable (fun ω => Real.exp (GeometricJumpMomentRadius eta*|Z ω|)) μ ∧
      (μ[fun ω => Real.exp (GeometricJumpMomentRadius eta*|Z ω|) | m]) ≤ᵐ[μ]
        (fun _ => GeometricJumpMomentBound eta r) := by
  have UnconditionalTail (j : ℕ) : μ {ω | (j : ℝ)≤|Z ω|} ≤ ENNReal.ofReal (r/(1+eta)^j) := by
    let : MeasurableSpace Ω := m0
    have EventMeasurable : MeasurableSet[m0] {ω | (j : ℝ)≤|Z ω|} :=
      Observable.abs measurableSet_Ici
    have Bound := integral_mono_ae integrable_condExp (integrable_const (r/(1+eta)^j)) (Tail j)
    rw [integral_condExp Below,integral_indicator_const (μ := μ) _ EventMeasurable,smul_eq_mul,mul_one,
      integral_const,probReal_univ,one_smul] at Bound
    have Converted := ENNReal.ofReal_le_ofReal Bound
    rw [ofReal_measureReal] at Converted
    exact Converted
  have Global := @AbsoluteExponentialMomentOfJumpTail Ω m0 μ Z eta r PositiveEta NonnegativeR Observable UnconditionalTail
  refine ⟨Global.1,?_⟩
  have IdentityMeasurable : @Measurable Ω Ω m0 m id :=
    measurable_iff_comap_le.mpr (by simpa only [MeasurableSpace.comap_id] using Below)
  let K : @Kernel Ω ℝ m inferInstance := condDistrib Z id μ
  have KernelTail (j : ℕ) : ∀ᵐ ω ∂μ,
      (K ω) {z : ℝ | (j : ℝ)≤|z|} ≤ ENNReal.ofReal (r/(1+eta)^j) := by
    have Law := condDistrib_ae_eq_condExp (μ := μ) IdentityMeasurable Observable
      (measurableSet_le measurable_const measurable_id.abs (f := fun _ : ℝ => (j : ℝ)))
    simp only [MeasurableSpace.comap_id] at Law
    filter_upwards [Law,Tail j] with ω Equal Bound
    change (K ω).real {z : ℝ | (j : ℝ)≤|z|}=
      (μ[({u | (j : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ω at Equal
    rw [← Equal] at Bound
    have Converted := ENNReal.ofReal_le_ofReal Bound
    rw [ofReal_measureReal] at Converted
    exact Converted
  have IntegralLaw := condExp_ae_eq_integral_condDistrib (μ := μ) IdentityMeasurable Observable.aemeasurable
    (Real.measurable_exp.comp (measurable_id.abs.const_mul (GeometricJumpMomentRadius eta))).stronglyMeasurable Global.1
  simp only [MeasurableSpace.comap_id] at IntegralLaw
  filter_upwards [IntegralLaw,ae_all_iff.mpr KernelTail] with ω Equal Tails
  change (μ[fun u => Real.exp (GeometricJumpMomentRadius eta*|Z u|) | m]) ω =
    ∫ z, Real.exp (GeometricJumpMomentRadius eta*|z|) ∂K ω at Equal
  rw [Equal]
  exact (AbsoluteExponentialMomentOfJumpTail (K ω) id eta r PositiveEta NonnegativeR measurable_id Tails).2

/-- Exponential absolute integrability also certifies the signed increment
is integrable. Its real integral therefore cannot use the default value. -/
theorem IntegrableOfAbsoluteExponential (μ : Measure Ω) (Z : Ω → ℝ) (q : ℝ)
    (PositiveQ : 0<q) (Observable : Measurable Z)
    (ExponentialIntegrable : Integrable (fun ω => Real.exp (q*|Z ω|)) μ) :
    Integrable Z μ := by
  apply (ExponentialIntegrable.const_mul (1/q)).mono' Observable.aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖Z ω‖≤(1/q)*Real.exp (q*|Z ω|)
    rw [Real.norm_eq_abs,one_div,inv_mul_eq_div]
    apply (le_div_iff₀ PositiveQ).mpr
    have Bound := Real.add_one_le_exp (q*|Z ω|)
    nlinarith)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- A tail bound imposed only on a past-measurable active event becomes a
global conditional tail after setting the observation to zero off that event.
The prefactor r>=1 handles the integer threshold zero exactly. -/
theorem ConditionalJumpTailOfRestriction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (Below : m ≤ m0) (A : Set Ω) (Event : MeasurableSet[m] A)
    (Z : Ω → ℝ) (Observable : Measurable[m0] Z) (eta r : ℝ)
    (PositiveEta : 0<eta) (OneLeR : 1≤r)
    (Tail : ∀ j : ℕ, ∀ᵐ ω ∂μ, ω∈A →
      (μ[({u | (j : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ω≤r/(1+eta)^j) :
    ∀ j : ℕ, (μ[({u | (j : ℝ)≤|A.indicator Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ≤ᵐ[μ]
      (fun _ => r/(1+eta)^j) := by
  let : MeasurableSpace Ω := m0
  intro j
  cases j with
  | zero =>
    have Equal : ({u | ((0 : ℕ) : ℝ)≤|A.indicator Z u|}).indicator (fun _ => (1 : ℝ)) =
        (fun _ => (1 : ℝ)) := by
      funext u
      have Member : u∈{u | ((0 : ℕ) : ℝ)≤|A.indicator Z u|} := by
        simp only [Set.mem_ofPred_eq,Nat.cast_zero,abs_nonneg]
      exact Set.indicator_of_mem Member _
    rw [Equal,condExp_const Below]
    exact ae_of_all _ (fun _ => by simpa only [pow_zero,div_one] using OneLeR)
  | succ j =>
    have Positive : (0 : ℝ)<(j+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos j)
    have RawMeasurable : MeasurableSet {u | ((j+1 : ℕ) : ℝ)≤|Z u|} :=
      Observable.abs measurableSet_Ici
    have Equal : ({u | ((j+1 : ℕ) : ℝ)≤|A.indicator Z u|}).indicator (fun _ => (1 : ℝ)) =
        A.indicator (({u | ((j+1 : ℕ) : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ))) := by
      funext u
      by_cases Active : u∈A
      · rw [Set.indicator_of_mem Active]
        change (if ((j+1 : ℕ) : ℝ)≤|A.indicator Z u| then (1 : ℝ) else 0) =
          (if ((j+1 : ℕ) : ℝ)≤|Z u| then (1 : ℝ) else 0)
        rw [Set.indicator_of_mem Active]
      · rw [Set.indicator_of_notMem Active]
        apply Set.indicator_of_notMem
        change ¬((j+1 : ℕ) : ℝ)≤|A.indicator Z u|
        rw [Set.indicator_of_notMem Active,abs_zero]
        exact not_le_of_gt Positive
    rw [Equal]
    have Conditional := condExp_indicator (m := m)
      ((integrable_const (1 : ℝ) (μ := μ)).indicator RawMeasurable) Event
    filter_upwards [Conditional,Tail (j+1)] with ω Equal Bound
    rw [Equal]
    by_cases Active : ω∈A
    · rw [Set.indicator_of_mem Active]
      exact Bound Active
    · rw [Set.indicator_of_notMem Active]
      exact div_nonneg (by linarith) (pow_nonneg (by linarith) _)

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- An almost sure unit jump has a simple conditional geometric tail,
including the thresholds zero and one. -/
theorem ConditionalUnitJumpTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (Below : m ≤ m0) (Z : Ω → ℝ)
    (Observable : Measurable[m0] Z) (Bound : ∀ᵐ ω ∂μ, |Z ω|≤1) (j : ℕ) :
    (μ[({u | (j : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ≤ᵐ[μ]
      (fun _ => 2/(1+(1 : ℝ))^j) := by
  let : MeasurableSpace Ω := m0
  by_cases Small : j≤1
  · have IndicatorIntegrable : Integrable (({u | (j : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ) (μ := μ)).indicator
      (Observable.abs measurableSet_Ici)
    have Upper := condExp_mono (m := m) IndicatorIntegrable (integrable_const (1 : ℝ) (μ := μ))
      (ae_of_all μ (fun u => Set.indicator_le_self' (fun _ _ => zero_le_one) u))
    rw [condExp_const Below] at Upper
    filter_upwards [Upper] with ω Upper
    apply Upper.trans
    interval_cases j <;> norm_num
  · have Zero : ({u | (j : ℝ)≤|Z u|}).indicator (fun _ => (1 : ℝ)) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [Bound] with ω Bound
      apply Set.indicator_of_notMem
      change ¬(j : ℝ)≤|Z ω|
      have Large : (1 : ℝ)<(j : ℝ) := by exact_mod_cast Nat.lt_of_not_ge Small
      linarith
    have Equal := condExp_congr_ae (m := m) Zero
    rw [condExp_const Below] at Equal
    filter_upwards [Equal] with ω Equal
    rw [Equal]
    positivity

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability

open MeasureTheory

noncomputable section
variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Strict integer absolute-jump tails on an active event imply closed integer
tails on that same event, with an explicit shift cost. The zero threshold is
handled by the constant conditional expectation one. -/
theorem ConditionalClosedJumpTailOfStrict (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (Below : m ≤ m0) (A : Set Ω)
    (Z : Ω → ℝ) (Observable : Measurable[m0] Z) (eta r : ℝ)
    (PositiveEta : 0 < eta) (PositiveR : 0 < r)
    (Tail : ∀ j : ℕ, ∀ᵐ ω ∂μ, ω ∈ A →
      (μ[({u | (j : ℝ) < |Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ω ≤
        r / (1 + eta) ^ j) :
    ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ A →
      (μ[({u | (k : ℝ) ≤ |Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ω ≤
        max 1 (r * (1 + eta)) / (1 + eta) ^ k := by
  classical
  let : MeasurableSpace Ω := m0
  have PositiveBase : (0 : ℝ) < 1 + eta := by linarith
  have NonnegativePrefactor : (0 : ℝ) ≤ max 1 (r * (1 + eta)) :=
    (mul_pos PositiveR PositiveBase).le.trans (le_max_right _ _)
  intro k
  cases k with
  | zero =>
    have Equal : ({u | ((0 : ℕ) : ℝ) ≤ |Z u|}).indicator (fun _ => (1 : ℝ)) =
        (fun _ => (1 : ℝ)) := by
      funext u
      have Member : u ∈ {u | ((0 : ℕ) : ℝ) ≤ |Z u|} := by
        simpa only [Set.mem_ofPred_eq, Nat.cast_zero] using abs_nonneg (Z u)
      exact Set.indicator_of_mem Member _
    rw [Equal, condExp_const Below]
    exact ae_of_all _ (fun _ _ => by
      simpa only [pow_zero, div_one] using
        (le_max_left (1 : ℝ) (r * (1 + eta))))
  | succ j =>
    have ClosedMeasurable : MeasurableSet {u | ((j + 1 : ℕ) : ℝ) ≤ |Z u|} :=
      Observable.abs measurableSet_Ici
    have StrictMeasurable : MeasurableSet {u | (j : ℝ) < |Z u|} :=
      Observable.abs measurableSet_Ioi
    have Included : {u | ((j + 1 : ℕ) : ℝ) ≤ |Z u|} ⊆
        {u | (j : ℝ) < |Z u|} := by
      intro u Member
      have Next : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self j
      exact Next.trans_le Member
    have IndicatorOrder :
        ({u | ((j + 1 : ℕ) : ℝ) ≤ |Z u|}).indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
          ({u | (j : ℝ) < |Z u|}).indicator (fun _ => (1 : ℝ)) := by
      apply ae_of_all
      intro u
      by_cases Closed : u ∈ {u | ((j + 1 : ℕ) : ℝ) ≤ |Z u|}
      · simp only [Set.indicator_of_mem Closed, Set.indicator_of_mem (Included Closed), le_refl]
      · rw [Set.indicator_of_notMem Closed]
        by_cases Strict : u ∈ {u | (j : ℝ) < |Z u|}
        · rw [Set.indicator_of_mem Strict]
          exact zero_le_one
        · simp only [Set.indicator_of_notMem Strict, le_refl]
    have Comparison := condExp_mono (m := m)
      ((integrable_const (1 : ℝ) (μ := μ)).indicator ClosedMeasurable)
      ((integrable_const (1 : ℝ) (μ := μ)).indicator StrictMeasurable)
      IndicatorOrder
    have Shift : r / (1 + eta) ^ j =
        (r * (1 + eta)) / (1 + eta) ^ (j + 1) := by
      rw [pow_succ, mul_div_mul_right r ((1 + eta) ^ j) PositiveBase.ne']
    have PrefactorBound : (r * (1 + eta)) / (1 + eta) ^ (j + 1) ≤
        max 1 (r * (1 + eta)) / (1 + eta) ^ (j + 1) :=
      div_le_div₀ NonnegativePrefactor (le_max_right _ _)
        (pow_pos PositiveBase _) le_rfl
    filter_upwards [Comparison, Tail j] with ω Compare Bound
    intro Active
    calc
      _ ≤ (μ[({u | (j : ℝ) < |Z u|}).indicator (fun _ => (1 : ℝ)) | m]) ω :=
        Compare
      _ ≤ r / (1 + eta) ^ j := Bound Active
      _ = (r * (1 + eta)) / (1 + eta) ^ (j + 1) := Shift
      _ ≤ max 1 (r * (1 + eta)) / (1 + eta) ^ (j + 1) := PrefactorBound

end
end ECTheoryLib.Probability
