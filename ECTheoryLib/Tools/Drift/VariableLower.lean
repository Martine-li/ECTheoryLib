import ECTheoryLib.Tools.Drift.Variable
import ECTheoryLib.Tools.Drift.PotentialLower

/-!
# Variable drift lower bound with controlled drift ratios

Source: Lengler, Drift Analysis, Theorem 2.4.1, pp.113-114, in Doerr and
Neumann (eds.), Theory of Evolutionary Computation (2020),
<https://doi.org/10.1007/978-3-030-29414-4_2>.

The process has a pointwise finite range and almost-sure nonincreasing
steps. The reciprocal drift integral and its upper slope estimate are
reused from Variable. The ratio condition is exactly
1/c <= h(max(next,smin))/h(current) on nonzero states, with c>=1.
Zero absorption is derived, not required as a separate premise.

The general theorem uses zero potential at an already optimal initial
state. The source integral expression is exposed for positive initialization: 
a reciprocal integral through zero need not exist, for example for h(s)=s.
No Markov property, finite expected runtime or termination premise is added.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Monotone descent and the drift-ratio condition bound the transformed decrease from above. -/
theorem VariableDriftPotentialDifferenceUpper (smin : ℝ) (h : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (s r c : ℝ) (PositiveC : 0 < c) (LowerS : smin ≤ s)
    (RangeR : r = 0 ∨ smin ≤ r) (Nonincreasing : r ≤ s)
    (RatioBound : 1/c ≤ h (max r smin)/h s) :
    VariableDriftPotential smin h s - VariableDriftPotential smin h r ≤ c*((s-r)/h s) := by
  have PositiveCurrent : 0 < h s := DriftPositive s LowerS
  have PositiveNext : 0 < h (max r smin) := DriftPositive _ (le_max_right _ _)
  have SlopeBound : h s ≤ c*h (max r smin) := by
    have Cross := (div_le_div_iff₀ PositiveC PositiveCurrent).mp RatioBound
    nlinarith
  have RawBound : VariableDriftPotential smin h s - VariableDriftPotential smin h r ≤
      (s-r)/h (max r smin) := by
    have CurrentNonzero : s ≠ 0 := (MinimumPositive.trans_le LowerS).ne'
    unfold VariableDriftPotential
    rw [if_neg CurrentNonzero]
    by_cases NextZero : r = 0
    · rw [if_pos NextZero, NextZero, sub_zero, sub_zero, max_eq_right MinimumPositive.le]
      have IntegralBound := ReciprocalDriftIntegralUpperBound smin h DriftPositive
        DriftMonotone smin s le_rfl LowerS
      calc
        _ ≤ smin/h smin + (s-smin)/h smin := add_le_add le_rfl IntegralBound
        _ = s/h smin := by ring
    · rw [if_neg NextZero]
      have LowerR : smin ≤ r := RangeR.resolve_left NextZero
      rw [max_eq_left LowerR]
      have IntegralDifference :
          (∫ x in smin..s, 1/h x)-(∫ x in smin..r, 1/h x) = ∫ x in r..s, 1/h x := by
        exact intervalIntegral.integral_interval_sub_left
          (ReciprocalDriftIntervalIntegrable smin h DriftPositive DriftMonotone smin s le_rfl LowerS)
          (ReciprocalDriftIntervalIntegrable smin h DriftPositive DriftMonotone smin r le_rfl LowerR)
      have Cancel : smin/h smin+(∫ x in smin..s, 1/h x)-
          (smin/h smin+∫ x in smin..r, 1/h x) =
          (∫ x in smin..s, 1/h x)-(∫ x in smin..r, 1/h x) := by ring
      rw [Cancel, IntegralDifference]
      exact ReciprocalDriftIntegralUpperBound smin h DriftPositive DriftMonotone r s LowerR Nonincreasing
  apply RawBound.trans
  have ProductBound := mul_le_mul_of_nonneg_left SlopeBound (sub_nonneg.mpr Nonincreasing)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ PositiveNext PositiveCurrent).mpr
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lengler Theorem 2.4.1 with a zero-safe initial potential; zero absorption follows from monotone nonnegative paths. -/
theorem VariableDriftLowerBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ) (c : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (_ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin)) (ConstantAtLeastOne : 1 ≤ c)
    (DriftRatio : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 → 1/c ≤ h (max (X (t+1) ω) smin)/h (X t ω))
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h s) :
    ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))/c) ≤
      ExpectedZeroHittingTime μ X := by
  have PositiveC : 0 < c := lt_of_lt_of_le zero_lt_one ConstantAtLeastOne
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
  apply PotentialDriftLowerBound μ X S h (VariableDriftPotential smin h) c
    CoordinatesMeasurable ValuesInS ZeroAbsorbing PositiveC
  · simp only [VariableDriftPotential, ↓reduceIte]
  · intro s InS
    exact VariableDriftPotentialNonnegative smin h MinimumPositive DriftPositive s (StateLowerBound s InS)
  · intro s InS Nonzero
    exact DriftPositive s ((StateLowerBound s InS).resolve_left Nonzero)
  · intro t
    filter_upwards [Nonincreasing t, DriftRatio t] with ω NextLe Ratio
    intro Nonzero
    exact VariableDriftPotentialDifferenceUpper smin h MinimumPositive DriftPositive DriftMonotone
      (X t ω) (X (t+1) ω) c PositiveC
      ((StateLowerBound _ (ValuesInS t ω)).resolve_left Nonzero)
      (StateLowerBound _ (ValuesInS (t+1) ω)) NextLe (Ratio Nonzero)
  · exact StateDriftUpperBound

/-- The displayed integral lower bound for almost surely nonzero initialization, retaining the factor 1/c. -/
theorem VariableDriftLowerBoundOfPositiveInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ) (c : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S) (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (Nonincreasing : ∀ t, ∀ᵐ ω ∂μ, X (t+1) ω ≤ X t ω)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin)) (ConstantAtLeastOne : 1 ≤ c)
    (DriftRatio : ∀ t, ∀ᵐ ω ∂μ, X t ω ≠ 0 → 1/c ≤ h (max (X (t+1) ω) smin)/h (X t ω))
    (StateDriftUpperBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ h s)
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ENNReal.ofReal ((smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x))/c) ≤
      ExpectedZeroHittingTime μ X := by
  have Bound := VariableDriftLowerBound μ X S smin h c CoordinatesMeasurable ZeroInS
    MinimumPositive StateLowerBound ValuesInS Nonincreasing DriftPositive DriftMonotone
    ConstantAtLeastOne DriftRatio StateDriftUpperBound
  have IntegralIntegrable : Integrable (fun ω => ∫ x in smin..X 0 ω, 1/h x) μ :=
    FiniteStateCompositionIntegrable μ (X 0) S (fun s => ∫ x in smin..s, 1/h x)
      (CoordinatesMeasurable 0) (ValuesInS 0)
  have PotentialExpectation : ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω)) =
      smin/h smin+ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1/h x) := by
    unfold ExpectedValue
    have Formula : (fun ω => VariableDriftPotential smin h (X 0 ω)) =ᵐ[μ]
        (fun ω => smin/h smin+∫ x in smin..X 0 ω, 1/h x) := by
      filter_upwards [InitialNonzero] with ω Nonzero
      simp only [VariableDriftPotential, if_neg Nonzero]
    rw [integral_congr_ae Formula, integral_add (integrable_const _) IntegralIntegrable,
      integral_const, probReal_univ, one_smul]
  rw [PotentialExpectation] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift
