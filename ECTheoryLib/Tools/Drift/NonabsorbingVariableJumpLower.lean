import ECTheoryLib.Tools.Drift.VariableJumpLower
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative

/-!
# Jump-floor lower drift before the first hit

Source counterpart: Lengler Theorem 2.4.2, printed pages 114-115.
Retain positivity of h at zero and a nonnegative floor on active states.
Both zero-safe and displayed-integral forms allow arbitrary initialization.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The jump-floor lower bound only needs path descent before the first hit.
The original requirement that h be positive at zero is retained. -/
theorem VariableDriftLowerBoundOfJumpFloorNonabsorbing
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ)
    (MinimumPositive : 0<smin) (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s)
    (Values : ∀ t ω, X t ω∈S)
    (Descent : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → X (t+1) ω≤X t ω)
    (DriftPositive : ∀ x, 0≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s∈S, s≠0 → 0≤ξ s)
    (JumpFloor : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → ξ (X t ω)≤X (t+1) ω)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤h (ξ (X t ω))) :
    ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω)))≤
      ExpectedZeroHittingTime μ X := by
  have Nonnegative : ∀ s∈S, 0≤s := by
    intro s InS
    rcases StateLowerBound s InS with Zero | Lower
    · rw [Zero]
    · exact MinimumPositive.le.trans Lower
  have Pointwise : ∀ t ω, 0≤X t ω := fun t ω => Nonnegative _ (Values t ω)
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ t ω, Y t ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have Bound := VariableDriftLowerBoundOfJumpFloor μ Y S smin h ξ (fun _ => AdaptedY.measurable)
    MinimumPositive StateLowerBound YValues (StopAtNonpositiveNonincreasing μ X Pointwise Descent)
    DriftPositive DriftMonotone FloorNonnegative
    (StopAtNonpositiveActiveRelation μ X Pointwise (fun s r => ξ s≤r) JumpFloor) (by
      intro t s _ Nonzero Positive
      exact StoppedStateDriftUpperBoundOfCondExp μ X F AdaptedX S Nonnegative Values
        (fun s => h (ξ s)) Drift t s Nonzero Positive)
  have Times : ExpectedZeroHittingTime μ Y=ExpectedZeroHittingTime μ X := by
    apply lintegral_congr
    intro ω
    rw [StopAtNonpositiveZeroTime X Pointwise]
  have Initial : Y 0=X 0 := funext (StopAtFirstHitInitial _ X)
  rwa [Times,Initial] at Bound

/-- Positivity of h on the whole nonnegative axis also justifies the book's
displayed integral with initial zero mass. -/
theorem VariableDriftIntegralLowerBoundOfJumpFloorNonabsorbing
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ)
    (MinimumPositive : 0<smin) (StateLowerBound : ∀ s∈S, s=0 ∨ smin≤s)
    (Values : ∀ t ω, X t ω∈S)
    (Descent : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → X (t+1) ω≤X t ω)
    (DriftPositive : ∀ x, 0≤x → 0<h x) (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s∈S, s≠0 → 0≤ξ s)
    (JumpFloor : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → ξ (X t ω)≤X (t+1) ω)
    (Drift : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤h (ξ (X t ω))) :
    ENNReal.ofReal (smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x))≤
      ExpectedZeroHittingTime μ X := by
  have Bound := VariableDriftLowerBoundOfJumpFloorNonabsorbing μ X F AdaptedX S smin h ξ
    MinimumPositive StateLowerBound Values Descent DriftPositive DriftMonotone FloorNonnegative JumpFloor Drift
  apply le_trans _ Bound
  apply ENNReal.ofReal_le_ofReal
  unfold ExpectedValue
  have IntegralIntegrable := FiniteStateCompositionIntegrable μ (X 0) S
    (fun s => ∫ x in smin..s, 1/h x) AdaptedX.measurable (Values 0)
  have PotentialIntegrable := FiniteStateCompositionIntegrable μ (X 0) S
    (VariableDriftPotential smin h) AdaptedX.measurable (Values 0)
  have Mean : (∫ ω, smin/h smin+(∫ x in smin..X 0 ω, 1/h x) ∂μ)≤
      ∫ ω, VariableDriftPotential smin h (X 0 ω) ∂μ := by
    apply integral_mono_ae ((integrable_const _).add IntegralIntegrable) PotentialIntegrable
    exact ae_of_all _ (fun ω => VariableDriftIntegralExpressionLePotential smin h MinimumPositive
      DriftPositive DriftMonotone (X 0 ω))
  rw [integral_add (integrable_const _) IntegralIntegrable,integral_const,probReal_univ,one_smul] at Mean
  exact Mean

end
end ECTheoryLib.Tools.Drift
