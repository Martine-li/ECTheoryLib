import ECTheoryLib.Tools.Drift.Potential
import ECTheoryLib.Probability.Processes.ConditionalDrift
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

/-!
# Exponential drift upper tails

This proves a non-strict version of Lengler Theorem 2.4.8(a), retaining its
weak comparison g(s) >= g(a). The printed strict conclusion is false for flat g;
see the source audit E06i and the original Lehre-Witt Theorem 2(iii).

The exponential potential is set to zero inside the absorbing target interval.
This matters when beta < 1: the ordinary exponential stays positive after
absorption and does not satisfy the claimed recursive contraction.

The state range is pointwise finite. State-event exponential moments suffice;
a separate interface accepts full Mathlib filtration-conditioned moments.
No Markov property, independence of increments, or finite-runtime premise is used.
Arbitrary initial laws and nonnegative time-dependent beta are retained; the
fixed-initial version displays the usual exponential factor. The early-hit
bound in part (b) requires a separate audited theorem and is not claimed here.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponential potential is killed when the target interval is reached. -/
def KilledExponentialPotential (a Lambda : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ≤ a then 0 else Real.exp (Lambda*(g s-g a))

theorem KilledExponentialNonnegative (a Lambda : ℝ) (g : ℝ → ℝ) (s : ℝ) :
    0 ≤ KilledExponentialPotential a Lambda g s := by
  unfold KilledExponentialPotential
  split
  · exact le_rfl
  · exact (Real.exp_pos _).le

/-- Averaging the conditional exponential moment contracts the killed potential. -/
theorem ExponentialPotentialExpectedStep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a Lambda β : ℝ) (g : ℝ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a) (t : ℕ)
    (MomentBound : ∀ s, s ∈ S → a < s → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω))))
        (StateEvent X t s) ≤ β) :
    (∫ ω, KilledExponentialPotential a Lambda g (X (t+1) ω) ∂μ) ≤
      β*(∫ ω, KilledExponentialPotential a Lambda g (X t ω) ∂μ) := by
  classical
  let W := KilledExponentialPotential a Lambda g
  have CurrentIntegrable := FiniteStateCompositionIntegrable μ (X t) S W (Coordinates t) (Values t)
  have NextIntegrable := FiniteStateCompositionIntegrable μ (X (t+1)) S W (Coordinates (t+1)) (Values (t+1))
  have Local (s : ℝ) (InS : s ∈ S) :
      (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ) ≤
        β*(∫ ω in StateEvent X t s, W (X t ω) ∂μ) := by
    have EventMeasurable := StateEventMeasurable X t s (Coordinates t)
    have CurrentConstant : (∫ ω in StateEvent X t s, W (X t ω) ∂μ)=
        W s*(μ (StateEvent X t s)).toReal := by
      rw [setIntegral_congr_fun EventMeasurable (show Set.EqOn (fun ω => W (X t ω)) (fun _ => W s) (StateEvent X t s) from
        fun _ InEvent => congrArg W InEvent), setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
    rw [CurrentConstant]
    by_cases AtTarget : s ≤ a
    · have NextZero : (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ)=0 := by
        apply integral_eq_zero_of_ae
        apply (ae_restrict_iff' EventMeasurable).mpr
        filter_upwards [Absorbing t] with ω Stays
        intro InEvent
        have Current : X t ω=s := InEvent
        have Next : X (t+1) ω ≤ a := Stays (by rw [Current]; exact AtTarget)
        exact if_pos Next
      rw [NextZero]
      simp only [W, KilledExponentialPotential, if_pos AtTarget, zero_mul, mul_zero, le_refl]
    · have Above : a < s := lt_of_not_ge AtTarget
      by_cases Null : μ (StateEvent X t s)=0
      · rw [Null, ENNReal.toReal_zero, mul_zero, mul_zero,
          Measure.restrict_eq_zero.mpr Null, integral_zero_measure]
      · let Zs := fun ω => Real.exp (Lambda*(g (X (t+1) ω)-g s))
        have ZsIntegrable := FiniteStateCompositionIntegrable μ (X (t+1)) S
          (fun r => Real.exp (Lambda*(g r-g s))) (Coordinates (t+1)) (Values (t+1))
        have Moment : (∫ ω in StateEvent X t s, Zs ω ∂μ) ≤ β*(μ (StateEvent X t s)).toReal := by
          have Bound := MomentBound s InS Above (bot_lt_iff_ne_bot.mpr Null)
          have PositiveReal := ENNReal.toReal_pos Null (measure_ne_top μ (StateEvent X t s))
          apply (div_le_iff₀ PositiveReal).mp
          change EventConditionalExpectation μ Zs (StateEvent X t s) ≤ β
          unfold EventConditionalExpectation at Bound ⊢
          have Same : (∫ ω in StateEvent X t s, Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω))) ∂μ)=
              ∫ ω in StateEvent X t s, Zs ω ∂μ := by
            apply setIntegral_congr_fun EventMeasurable
            intro ω InEvent
            have Current : X t ω=s := InEvent
            change Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω)))=Real.exp (Lambda*(g (X (t+1) ω)-g s))
            rw [Current]
          rw [Same] at Bound
          exact Bound
        have Comparison : (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ) ≤
            W s*(∫ ω in StateEvent X t s, Zs ω ∂μ) := by
          rw [← integral_const_mul]
          apply integral_mono_ae NextIntegrable.integrableOn (ZsIntegrable.const_mul (W s)).integrableOn
          apply ae_of_all
          intro ω
          by_cases NextTarget : X (t+1) ω ≤ a
          · simp only [W, KilledExponentialPotential, if_pos NextTarget, if_neg AtTarget]
            exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
          · simp only [W, KilledExponentialPotential, if_neg NextTarget, if_neg AtTarget]
            rw [← Real.exp_add]
            have Exponent : Lambda*(g s-g a)+Lambda*(g (X (t+1) ω)-g s)=Lambda*(g (X (t+1) ω)-g a) := by ring
            rw [Exponent]
        calc
          _ ≤ W s*(∫ ω in StateEvent X t s, Zs ω ∂μ) := Comparison
          _ ≤ W s*(β*(μ (StateEvent X t s)).toReal) :=
            mul_le_mul_of_nonneg_left Moment (KilledExponentialNonnegative a Lambda g s)
          _ = β*(W s*(μ (StateEvent X t s)).toReal) := by ring
  rw [FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) NextIntegrable,
    FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) CurrentIntegrable,
    Finset.mul_sum]
  exact Finset.sum_le_sum Local

/-- The non-strict upper-tail version permits flat transformed potentials. -/
theorem ExponentialDriftUpperTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a Lambda : ℝ) (g : ℝ → ℝ) (β : ℕ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ t, 0 ≤ β t)
    (PotentialAbove : ∀ s ∈ S, a < s → g a ≤ g s)
    (MomentBound : ∀ t s, s ∈ S → a < s → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω))))
        (StateEvent X t s) ≤ β t) (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*
        (∫ ω, KilledExponentialPotential a Lambda g (X 0 ω) ∂μ)) := by
  let W := KilledExponentialPotential a Lambda g
  have Decay (n : ℕ) : (∫ ω, W (X n ω) ∂μ) ≤
      (∏ j ∈ Finset.range n, β j)*(∫ ω, W (X 0 ω) ∂μ) := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.prod_empty, one_mul, le_refl]
    | succ n Before =>
      have Step := ExponentialPotentialExpectedStep μ X S a Lambda (β n) g Coordinates Values Absorbing n
        (MomentBound n)
      calc
        _ ≤ β n*(∫ ω, W (X n ω) ∂μ) := Step
        _ ≤ β n*((∏ j ∈ Finset.range n, β j)*(∫ ω, W (X 0 ω) ∂μ)) :=
          mul_le_mul_of_nonneg_left Before (NonnegativeBeta n)
        _ = _ := by rw [Finset.prod_range_succ]; ring
  have IntegrableW := FiniteStateCompositionIntegrable μ (X t) S W (Coordinates t) (Values t)
  have Markov := IntegrableW.measure_le_integral (ae_of_all _ (fun ω => KilledExponentialNonnegative a Lambda g (X t ω)))
    (s := {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)}) (by
      intro ω Survives
      have Above : a < X t ω := by
        apply lt_of_not_ge
        intro AtTarget
        have Hit := (FirstHittingTimeLeIff (fun s : ℝ => s ≤ a) (fun j => X j ω) t).mpr ⟨t, le_rfl, AtTarget⟩
        exact (not_le_of_gt Survives) Hit
      change 1 ≤ KilledExponentialPotential a Lambda g (X t ω)
      rw [KilledExponentialPotential, if_neg (not_le_of_gt Above)]
      exact Real.one_le_exp_iff.mpr (mul_nonneg NonnegativeLambda (sub_nonneg.mpr (PotentialAbove _ (Values t ω) Above))))
  exact Markov.trans (ENNReal.ofReal_le_ofReal (Decay t))

/-- Fixed initialization gives the book's exponential factor with a non-strict sign. -/
theorem ExponentialDriftUpperTailOfFixedInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a Lambda s₀ : ℝ) (g : ℝ → ℝ) (β : ℕ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ t, 0 ≤ β t)
    (PotentialAbove : ∀ s ∈ S, a < s → g a ≤ g s)
    (MomentBound : ∀ t s, s ∈ S → a < s → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω))))
        (StateEvent X t s) ≤ β t)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω=s₀) (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*Real.exp (Lambda*(g s₀-g a))) := by
  have Bound := ExponentialDriftUpperTail μ X S a Lambda g β Coordinates Values Absorbing
    NonnegativeLambda NonnegativeBeta PotentialAbove MomentBound t
  have InitialMean : (∫ ω, KilledExponentialPotential a Lambda g (X 0 ω) ∂μ)=
      Real.exp (Lambda*(g s₀-g a)) := by
    calc
      _ = ∫ _ω, Real.exp (Lambda*(g s₀-g a)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [FixedInitial] with ω Initial
        rw [Initial, KilledExponentialPotential, if_neg (not_le_of_gt InitialAbove)]
      _ = _ := by rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [InitialMean] at Bound
  exact Bound

/-- Full-history conditional exponential moments imply the finite state-event version. -/
theorem ExponentialDriftUpperTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (S : Finset ℝ) (a Lambda s₀ : ℝ)
    (g : ℝ → ℝ) (β : ℕ → ℝ) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeBeta : ∀ t, 0 ≤ β t)
    (PotentialAbove : ∀ s ∈ S, a < s → g a ≤ g s)
    (MomentBound : ∀ t, ∀ᵐ ω ∂μ, a < X t ω →
      (μ[fun ω => Real.exp (Lambda*(g (X (t+1) ω)-g (X t ω))) | F t]) ω ≤ β t)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω=s₀) (t : ℕ) :
    μ {ω | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*Real.exp (Lambda*(g s₀-g a))) := by
  classical
  have Coordinates (j : ℕ) : Measurable (X j) := (ProcessAdapted j).mono (F.le j) le_rfl
  apply ExponentialDriftUpperTailOfFixedInitial μ X S a Lambda s₀ g β Coordinates Values Absorbing
    NonnegativeLambda NonnegativeBeta PotentialAbove _ InitialAbove FixedInitial t
  intro j s InS Above PositiveEvent
  let D := fun ω => g (X (j+1) ω)-g (X j ω)
  let R := (S.product S).image (fun p => g p.1-g p.2)
  have MeasurableD : Measurable D :=
    (FiniteStateCompositionMeasurable (X (j+1)) S g (Coordinates (j+1)) (Values (j+1))).sub
      (FiniteStateCompositionMeasurable (X j) S g (Coordinates j) (Values j))
  have RangeD (ω : Ω) : D ω ∈ R :=
    Finset.mem_image.mpr ⟨(X (j+1) ω, X j ω), Finset.mem_product.mpr ⟨Values (j+1) ω, Values j ω⟩, rfl⟩
  have ExponentialIntegrable := FiniteStateCompositionIntegrable μ D R
    (fun r => Real.exp (Lambda*r)) MeasurableD RangeD
  have PastEvent : MeasurableSet[F j] (StateEvent X j s) :=
    measurableSet_eq_fun (ProcessAdapted j) measurable_const
  have AmbientEvent := StateEventMeasurable X j s (Coordinates j)
  have IntegralBound : (∫ ω in StateEvent X j s, Real.exp (Lambda*(g (X (j+1) ω)-g (X j ω))) ∂μ) ≤
      ∫ _ω in StateEvent X j s, β j ∂μ := by
    rw [← setIntegral_condExp (F.le j) ExponentialIntegrable PastEvent]
    apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
    apply (ae_restrict_iff' AmbientEvent).mpr
    filter_upwards [MomentBound j] with ω Moment
    intro InEvent
    have Current : X j ω=s := InEvent
    exact Moment (by rw [Current]; exact Above)
  rw [setIntegral_const, measureReal_def, smul_eq_mul] at IntegralBound
  unfold EventConditionalExpectation
  apply (div_le_iff₀ (ENNReal.toReal_pos PositiveEvent.ne' (measure_ne_top μ _))).mpr
  rw [mul_comm]
  exact IntegralBound

end
end ECTheoryLib.Tools.Drift
