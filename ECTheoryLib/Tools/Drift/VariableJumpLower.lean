import ECTheoryLib.Tools.Drift.VariableLower
import ECTheoryLib.Probability.Processes.ConditionalDrift

/-!
# Variable drift lower bound with a deterministic jump floor

Source: Lengler, Drift Analysis, Theorem 2.4.2, pp.114-115, in Doerr and
Neumann (eds.), Theory of Evolutionary Computation (2020),
<https://doi.org/10.1007/978-3-030-29414-4_2>.
Original: Doerr, Fouz and Witt, GECCO 2011, Theorem 7, pp.2086-2087,
<https://doi.org/10.1145/2001576.2001856>.

The floor xi is allowed to be zero, unlike the printed strictly-positive
codomain: the adjacent RLS example uses xi(1)=0 at its final transition.
The drift function h remains positive on all nonnegative reals, including
zero. Therefore the displayed integral through an initial zero exists;
its value need not be positive. The zero-safe potential gives a stronger
initial-mixture bound. Both forms allow arbitrary initial laws.

The filtration entry uses Mathlib conditional expectation. Its state-event
consequence is derived, not assumed. No Markov, termination, finite-mean,
continuity or differentiability requirement is added. Finite range remains
pointwise; monotone paths imply zero absorption.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A deterministic lower bound on the next state controls the transformed decrease. -/
theorem VariableDriftPotentialDifferenceOfJumpFloor (smin : ℝ) (h : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (DriftPositive : ∀ x, 0 ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (s r z : ℝ) (LowerS : smin ≤ s) (RangeR : r=0 ∨ smin ≤ r)
    (Nonincreasing : r ≤ s) (FloorNonnegative : 0 ≤ z) (JumpFloor : z ≤ r) :
    VariableDriftPotential smin h s-VariableDriftPotential smin h r ≤ (s-r)/h z := by
  have PositiveCurrent : 0 < h s := DriftPositive s (MinimumPositive.le.trans LowerS)
  have PositiveFloor : 0 < h z := DriftPositive z FloorNonnegative
  have RestrictedPositive (x : ℝ) (Lower : smin ≤ x) : 0 < h x :=
    DriftPositive x (MinimumPositive.le.trans Lower)
  have RestrictedMonotone : MonotoneOn h (Set.Ici smin) :=
    DriftMonotone.mono (Set.Ici_subset_Ici.mpr MinimumPositive.le)
  have Ratio : 1/(h s/h z) ≤ h (max r smin)/h s := by
    rw [one_div_div]
    apply div_le_div_of_nonneg_right _ PositiveCurrent.le
    exact DriftMonotone FloorNonnegative (MinimumPositive.le.trans (le_max_right _ _))
      (JumpFloor.trans (le_max_left _ _))
  have Bound := VariableDriftPotentialDifferenceUpper smin h MinimumPositive
    RestrictedPositive RestrictedMonotone s r (h s/h z) (div_pos PositiveCurrent PositiveFloor)
    LowerS RangeR Nonincreasing Ratio
  have Scale : (h s/h z)*((s-r)/h s) = (s-r)/h z := by
    field_simp
  rw [Scale] at Bound
  exact Bound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Variable-drift lower bound with a deterministic jump floor, allowing a zero floor. -/
theorem VariableDriftLowerBoundOfJumpFloor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftPositive : ∀ x, 0 ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s ∈ S, s ≠ 0 → 0 ≤ ξ s)
    (JumpFloor : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 → ξ (X t ω) ≤ X (t+1) ω)
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h (ξ s)) :
    ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))) ≤
      ExpectedZeroHittingTime μ X := by
  have ZeroAbsorbing : ZeroIsAbsorbing μ X := by
    intro t
    filter_upwards [Nonincreasing t] with ω NextLe
    intro CurrentZero
    have NextNonnegative : 0 ≤ X (t+1) ω := by
      rcases StateLowerBound _ (ValuesInS (t+1) ω) with NextZero | LowerNext
      · rw [NextZero]
      · exact MinimumPositive.le.trans LowerNext
    rw [CurrentZero] at NextLe
    exact le_antisymm NextLe NextNonnegative
  have Bound := PotentialDriftLowerBound μ X S (fun s => h (ξ s))
    (VariableDriftPotential smin h) 1 CoordinatesMeasurable ValuesInS ZeroAbsorbing zero_lt_one
    (by simp only [VariableDriftPotential, ↓reduceIte])
    (fun s InS => VariableDriftPotentialNonnegative smin h MinimumPositive
      (fun x Lower => DriftPositive x (MinimumPositive.le.trans Lower)) s (StateLowerBound s InS))
    (fun s InS Nonzero => DriftPositive _ (FloorNonnegative s InS Nonzero))
    (by
      intro t
      filter_upwards [Nonincreasing t, JumpFloor t] with ω NextLe Floor
      intro Nonzero
      rw [one_mul]
      exact VariableDriftPotentialDifferenceOfJumpFloor smin h MinimumPositive DriftPositive
        DriftMonotone (X t ω) (X (t+1) ω) (ξ (X t ω))
        ((StateLowerBound _ (ValuesInS t ω)).resolve_left Nonzero)
        (StateLowerBound _ (ValuesInS (t+1) ω)) NextLe
        (FloorNonnegative _ (ValuesInS t ω) Nonzero) (Floor Nonzero))
    StateDriftUpperBound
  rw [div_one] at Bound
  exact Bound

/-- Positivity at zero makes the displayed integral well-defined; at zero it can be negative. -/
theorem VariableDriftIntegralExpressionLePotential (smin : ℝ) (h : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (DriftPositive : ∀ x, 0 ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici 0)) (s : ℝ) :
    smin/h smin+(∫ x in smin..s, 1/h x) ≤ VariableDriftPotential smin h s := by
  unfold VariableDriftPotential
  by_cases Zero : s=0
  · rw [if_pos Zero, Zero, intervalIntegral.integral_symm]
    have IntegralBound := ReciprocalDriftIntegralLowerBound 0 h DriftPositive
      DriftMonotone 0 smin le_rfl MinimumPositive.le
    rw [sub_zero] at IntegralBound
    linarith
  · rw [if_neg Zero]

/-- The book's displayed integral bound holds even with initial zero mass when h is positive at zero. -/
theorem VariableDriftIntegralLowerBoundOfJumpFloor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftPositive : ∀ x, 0 ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s ∈ S, s ≠ 0 → 0 ≤ ξ s)
    (JumpFloor : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 → ξ (X t ω) ≤ X (t+1) ω)
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h (ξ s)) :
    ENNReal.ofReal (smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x)) ≤
      ExpectedZeroHittingTime μ X := by
  have Bound := VariableDriftLowerBoundOfJumpFloor μ X S smin h ξ CoordinatesMeasurable
    MinimumPositive StateLowerBound ValuesInS Nonincreasing DriftPositive DriftMonotone
    FloorNonnegative JumpFloor StateDriftUpperBound
  apply le_trans _ Bound
  apply ENNReal.ofReal_le_ofReal
  unfold ExpectedValue
  have IntegralIntegrable := FiniteStateCompositionIntegrable μ (X 0) S
    (fun s => ∫ x in smin..s, 1/h x) (CoordinatesMeasurable 0) (ValuesInS 0)
  have PotentialIntegrable := FiniteStateCompositionIntegrable μ (X 0) S
    (VariableDriftPotential smin h) (CoordinatesMeasurable 0) (ValuesInS 0)
  have MeanComparison : (∫ ω, smin/h smin+(∫ x in smin..X 0 ω, 1/h x) ∂μ) ≤
      ∫ ω, VariableDriftPotential smin h (X 0 ω) ∂μ := by
    apply integral_mono_ae ((integrable_const _).add IntegralIntegrable) PotentialIntegrable
    exact ae_of_all _ (fun ω => VariableDriftIntegralExpressionLePotential smin h
      MinimumPositive DriftPositive DriftMonotone (X 0 ω))
  rw [integral_add (integrable_const _) IntegralIntegrable, integral_const,
    probReal_univ, one_smul] at MeanComparison
  exact MeanComparison

/-- Filtration formulation of Theorem 2.4.2, using Mathlib conditional expectation and allowing ξ=0. -/
theorem VariableDriftLowerBoundOfJumpFloorCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (ProcessAdapted : Adapted F X) (S : Finset ℝ) (smin : ℝ) (h ξ : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s=0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftPositive : ∀ x, 0 ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici 0))
    (FloorNonnegative : ∀ s ∈ S, s ≠ 0 → 0 ≤ ξ s)
    (JumpFloor : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 → ξ (X t ω) ≤ X (t+1) ω)
    (ConditionalBound : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ h (ξ (X t ω))) :
    ENNReal.ofReal (smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x)) ≤
      ExpectedZeroHittingTime μ X := by
  have CoordinatesMeasurable (t : ℕ) : Measurable (X t) := ProcessAdapted.measurable
  apply VariableDriftIntegralLowerBoundOfJumpFloor μ X S smin h ξ CoordinatesMeasurable
    MinimumPositive StateLowerBound ValuesInS Nonincreasing DriftPositive DriftMonotone
    FloorNonnegative JumpFloor
  intro t s _InS Nonzero PositiveEvent
  have DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ :=
    (FiniteStateIntegrable μ (X t) S (CoordinatesMeasurable t) (ae_of_all _ (ValuesInS t))).sub
      (FiniteStateIntegrable μ (X (t+1)) S (CoordinatesMeasurable (t+1)) (ae_of_all _ (ValuesInS (t+1))))
  exact StateDriftUpperBoundOfCondExp μ X F ProcessAdapted (fun s => h (ξ s)) t
    DecreaseIntegrable (ConditionalBound t) s Nonzero PositiveEvent

end
end ECTheoryLib.Tools.Drift
