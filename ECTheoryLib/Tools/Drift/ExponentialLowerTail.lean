import ECTheoryLib.Tools.Drift.ExponentialTail
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime

/-!
# Exponential drift bounds for early hits of zero

This supplies a corrected, restricted counterpart of Lengler 2.4.8(b).
The exponential moment must be bounded above, as in the original Lehre-Witt
Theorem 2(iv), rather than below as printed in the book. We additionally require
beta(t) >= 1: a bound imposed only outside the target does not control an
arbitrarily shrinking product after absorption. Tests include a counterexample.

The target is zero, g(0)=0, and zero is absorbing. The potential exp(-lambda*g)
equals one on the hit event. Its integral is controlled by successive beta
factors. This gives the closed early-hit event T <= t, including its endpoint.
The initial law may be random and the pointwise state range is finite.
No Markov property, independence, or finite-runtime assumption is required.

State-event and full-filtration conditional moments are supported. The latter
reuse Mathlib conditional expectations and the existing conditional-event bridge.
This is not claimed as full coverage of the book's arbitrary-target statement.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- With beta at least one, the exponential potential remains controlled after absorption. -/
theorem ExponentialLowerPotentialExpectedStep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (Lambda β : ℝ) (g : ℝ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ZeroIsAbsorbing μ X) (PotentialZero : g 0=0) (OneLeBeta : 1 ≤ β) (t : ℕ)
    (MomentBound : ∀ s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω))))
        (StateEvent X t s) ≤ β) :
    (∫ ω, Real.exp (-Lambda*g (X (t+1) ω)) ∂μ) ≤
      β*(∫ ω, Real.exp (-Lambda*g (X t ω)) ∂μ) := by
  classical
  let W := fun s => Real.exp (-Lambda*g s)
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
    by_cases Zero : s=0
    · subst s
      have NextOne : (∫ ω in StateEvent X t 0, W (X (t+1) ω) ∂μ)=(μ (StateEvent X t 0)).toReal := by
        calc
          _ = ∫ _ω in StateEvent X t 0, (1 : ℝ) ∂μ := by
            apply integral_congr_ae
            apply (ae_restrict_iff' EventMeasurable).mpr
            filter_upwards [Absorbing t] with ω Stays
            intro InEvent
            have Next : X (t+1) ω=0 := Stays InEvent
            simp only [W, Next, PotentialZero, mul_zero, Real.exp_zero]
          _ = _ := by rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
      rw [NextOne]
      simp only [W, PotentialZero, mul_zero, Real.exp_zero, one_mul]
      exact le_mul_of_one_le_left ENNReal.toReal_nonneg OneLeBeta
    · by_cases Null : μ (StateEvent X t s)=0
      · rw [Null, ENNReal.toReal_zero, mul_zero, mul_zero,
          Measure.restrict_eq_zero.mpr Null, integral_zero_measure]
      · let Zs := fun ω => Real.exp (Lambda*(g s-g (X (t+1) ω)))
        have Moment : (∫ ω in StateEvent X t s, Zs ω ∂μ) ≤ β*(μ (StateEvent X t s)).toReal := by
          have Bound := MomentBound s InS Zero (bot_lt_iff_ne_bot.mpr Null)
          have PositiveReal := ENNReal.toReal_pos Null (measure_ne_top μ (StateEvent X t s))
          apply (div_le_iff₀ PositiveReal).mp
          change EventConditionalExpectation μ Zs (StateEvent X t s) ≤ β
          unfold EventConditionalExpectation at Bound ⊢
          have Same : (∫ ω in StateEvent X t s, Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω))) ∂μ)=
              ∫ ω in StateEvent X t s, Zs ω ∂μ := by
            apply setIntegral_congr_fun EventMeasurable
            intro ω InEvent
            have Current : X t ω=s := InEvent
            change Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω)))=Real.exp (Lambda*(g s-g (X (t+1) ω)))
            rw [Current]
          rw [Same] at Bound
          exact Bound
        have Product : (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ)=
            W s*(∫ ω in StateEvent X t s, Zs ω ∂μ) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          apply ae_of_all
          intro ω
          change Real.exp (-Lambda*g (X (t+1) ω))=
            Real.exp (-Lambda*g s)*Real.exp (Lambda*(g s-g (X (t+1) ω)))
          rw [← Real.exp_add]
          congr 1
          ring
        rw [Product]
        calc
          _ ≤ W s*(β*(μ (StateEvent X t s)).toReal) := mul_le_mul_of_nonneg_left Moment (Real.exp_pos _).le
          _ = _ := by ring
  rw [FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) NextIntegrable,
    FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) CurrentIntegrable,
    Finset.mul_sum]
  exact Finset.sum_le_sum Local

/-- A corrected zero-target early-hit bound, including the threshold atom and arbitrary initial laws. -/
theorem ExponentialDriftLowerTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (Lambda : ℝ) (g : ℝ → ℝ) (β : ℕ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ZeroIsAbsorbing μ X) (PotentialZero : g 0=0) (OneLeBeta : ∀ t, 1 ≤ β t)
    (MomentBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω))))
        (StateEvent X t s) ≤ β t) (t : ℕ) :
    μ {ω | ZeroHittingTime X ω ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*(∫ ω, Real.exp (-Lambda*g (X 0 ω)) ∂μ)) := by
  have Decay (n : ℕ) : (∫ ω, Real.exp (-Lambda*g (X n ω)) ∂μ) ≤
      (∏ j ∈ Finset.range n, β j)*(∫ ω, Real.exp (-Lambda*g (X 0 ω)) ∂μ) := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.prod_empty, one_mul, le_refl]
    | succ n Before =>
      have Step := ExponentialLowerPotentialExpectedStep μ X S Lambda (β n) g Coordinates Values
        Absorbing PotentialZero (OneLeBeta n) n (MomentBound n)
      calc
        _ ≤ β n*(∫ ω, Real.exp (-Lambda*g (X n ω)) ∂μ) := Step
        _ ≤ β n*((∏ j ∈ Finset.range n, β j)*(∫ ω, Real.exp (-Lambda*g (X 0 ω)) ∂μ)) :=
          mul_le_mul_of_nonneg_left Before (zero_le_one.trans (OneLeBeta n))
        _ = _ := by rw [Finset.prod_range_succ]; ring
  have IntegrableW := FiniteStateCompositionIntegrable μ (X t) S (fun s => Real.exp (-Lambda*g s))
    (Coordinates t) (Values t)
  have Markov := IntegrableW.measure_le_integral (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (s := {ω | X t ω=0}) (by intro ω Zero; rw [Zero, PotentialZero, mul_zero, Real.exp_zero])
  have Event : μ {ω | ZeroHittingTime X ω ≤ (t : WithTop ℕ)}=μ {ω | X t ω=0} := by
    apply measure_congr
    filter_upwards [ZeroHittingTimeLeIffOfAbsorbing μ X Absorbing t] with ω Same
    exact propext Same
  rw [Event]
  exact Markov.trans (ENNReal.ofReal_le_ofReal (Decay t))

/-- Fixed-start form; no finite-runtime premise or positive-initial restriction is needed. -/
theorem ExponentialDriftLowerTailOfFixedInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (Lambda s₀ : ℝ) (g : ℝ → ℝ) (β : ℕ → ℝ)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ZeroIsAbsorbing μ X) (PotentialZero : g 0=0) (OneLeBeta : ∀ t, 1 ≤ β t)
    (MomentBound : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω))))
        (StateEvent X t s) ≤ β t)
    (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω=s₀) (t : ℕ) :
    μ {ω | ZeroHittingTime X ω ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*Real.exp (-Lambda*g s₀)) := by
  have Bound := ExponentialDriftLowerTail μ X S Lambda g β Coordinates Values Absorbing
    PotentialZero OneLeBeta MomentBound t
  have InitialMean : (∫ ω, Real.exp (-Lambda*g (X 0 ω)) ∂μ)=Real.exp (-Lambda*g s₀) := by
    calc
      _ = ∫ _ω, Real.exp (-Lambda*g s₀) ∂μ := by
        apply integral_congr_ae
        filter_upwards [FixedInitial] with ω Initial
        rw [Initial]
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  rw [InitialMean] at Bound
  exact Bound

/-- Full-history version of the corrected zero-target bound. -/
theorem ExponentialDriftLowerTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (S : Finset ℝ) (Lambda s₀ : ℝ)
    (g : ℝ → ℝ) (β : ℕ → ℝ) (Values : ∀ t ω, X t ω ∈ S)
    (Absorbing : ZeroIsAbsorbing μ X) (PotentialZero : g 0=0) (OneLeBeta : ∀ t, 1 ≤ β t)
    (MomentBound : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun ω => Real.exp (Lambda*(g (X t ω)-g (X (t+1) ω))) | F t]) ω ≤ β t)
    (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω=s₀) (t : ℕ) :
    μ {ω | ZeroHittingTime X ω ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((∏ j ∈ Finset.range t, β j)*Real.exp (-Lambda*g s₀)) := by
  classical
  have Coordinates (j : ℕ) : Measurable (X j) := (ProcessAdapted j).mono (F.le j) le_rfl
  apply ExponentialDriftLowerTailOfFixedInitial μ X S Lambda s₀ g β Coordinates Values
    Absorbing PotentialZero OneLeBeta _ FixedInitial t
  intro j s _InS Nonzero PositiveEvent
  let D := fun ω => g (X j ω)-g (X (j+1) ω)
  let R := (S.product S).image (fun p => g p.1-g p.2)
  have MeasurableD : Measurable D :=
    (FiniteStateCompositionMeasurable (X j) S g (Coordinates j) (Values j)).sub
      (FiniteStateCompositionMeasurable (X (j+1)) S g (Coordinates (j+1)) (Values (j+1)))
  have RangeD (ω : Ω) : D ω ∈ R :=
    Finset.mem_image.mpr ⟨(X j ω, X (j+1) ω), Finset.mem_product.mpr ⟨Values j ω, Values (j+1) ω⟩, rfl⟩
  have ExponentialIntegrable := FiniteStateCompositionIntegrable μ D R
    (fun r => Real.exp (Lambda*r)) MeasurableD RangeD
  exact StateEventExpectationUpperBoundOfCondExp μ X F ProcessAdapted (fun _ => β j) j
    (fun ω => Real.exp (Lambda*(g (X j ω)-g (X (j+1) ω)))) ExponentialIntegrable
    (MomentBound j) s Nonzero PositiveEvent

end
end ECTheoryLib.Tools.Drift
