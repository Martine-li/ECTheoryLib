import ECTheoryLib.Tools.Drift.Variable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Multiplicative drift upper bound

Source: Johannes Lengler, *Drift Analysis*, Theorem 2.3.11, p. 110,
in Doerr and Neumann (eds.), *Theory of Evolutionary Computation* (2020),
<https://doi.org/10.1007/978-3-030-29414-4_2>.
The preprint <https://arxiv.org/abs/1712.00964> labels it Theorem 11.
This is derived from the integral variable
drift theorem with `h(s) = Delta * s`; evaluating the integral gives the log.

The general theorem includes random initial zero states by assigning them
zero rescaled potential.  For almost surely positive initialization, the
corollary is exactly `(1 + E[log(X_0 / smin)]) / Delta`.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- The logarithmic runtime potential, with zero for an initially optimal state. -/
def MultiplicativeDriftPotential (smin Delta s : ℝ) : ℝ :=
  if s = 0 then 0 else (1 + Real.log (s / smin)) / Delta

/-- Evaluating Lengler's rescaling for a linear drift function yields the
logarithmic potential.  The zero branch never evaluates an integral through zero. -/
theorem LinearVariableDriftPotential (smin Delta s : ℝ)
    (MinimumPositive : 0 < smin) (PositiveDelta : 0 < Delta)
    (StateLowerBound : s = 0 ∨ smin ≤ s) :
    VariableDriftPotential smin (fun x => Delta * x) s =
      MultiplicativeDriftPotential smin Delta s := by
  unfold VariableDriftPotential MultiplicativeDriftPotential
  by_cases StateZero : s = 0
  · rw [if_pos StateZero, if_pos StateZero]
  · rw [if_neg StateZero, if_neg StateZero]
    have StatePositive : 0 < s := MinimumPositive.trans_le (StateLowerBound.resolve_left StateZero)
    have ReciprocalFormula : (fun x : ℝ => 1 / (Delta * x)) =
        (fun x : ℝ => (1 / x) / Delta) := by
      funext x
      rw [div_div, mul_comm]
    rw [ReciprocalFormula, intervalIntegral.integral_div,
      integral_one_div_of_pos MinimumPositive StatePositive]
    have MinimumTerm : smin / (Delta * smin) = 1 / Delta := by
      field_simp
    rw [MinimumTerm]
    ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplicative drift upper bound for a general finite-valued process with
random initialization. The original drift is at least `Delta * s`; no transformed
drift or runtime bound is assumed. -/
theorem MultiplicativeDriftUpperBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PositiveDelta : 0 < Delta)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω))) := by
  have LinearDriftPositive : ∀ x, smin ≤ x → 0 < Delta * x := by
    intro x LowerX
    exact mul_pos PositiveDelta (MinimumPositive.trans_le LowerX)
  have LinearDriftMonotone : MonotoneOn (fun x => Delta * x) (Set.Ici smin) := by
    intro x _InX y _InY BeforeY
    exact mul_le_mul_of_nonneg_left BeforeY PositiveDelta.le
  have Bound := VariableDriftUpperBound μ X S smin (fun x => Delta * x)
    CoordinatesMeasurable ZeroInS MinimumPositive StateLowerBound ValuesInS
    ZeroAbsorbing LinearDriftPositive LinearDriftMonotone StateDriftLowerBound
  have PotentialEquality :
      (fun ω => VariableDriftPotential smin (fun x => Delta * x) (X 0 ω)) =
        (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) := by
    funext ω
    exact LinearVariableDriftPotential smin Delta (X 0 ω) MinimumPositive PositiveDelta
      (StateLowerBound (X 0 ω) (ValuesInS 0 ω))
  rw [PotentialEquality] at Bound
  exact Bound

/-- Lengler's displayed multiplicative bound for almost surely positive
random initialization. -/
theorem MultiplicativeDriftUpperBoundOfPositiveInitial (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PositiveDelta : 0 < Delta)
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta * s ≤ StateDrift μ X t s)
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      ((1 + ExpectedValue μ (fun ω => Real.log (X 0 ω / smin))) / Delta) := by
  have Bound := MultiplicativeDriftUpperBound μ X S smin Delta CoordinatesMeasurable
    ZeroInS MinimumPositive StateLowerBound ValuesInS ZeroAbsorbing PositiveDelta
    StateDriftLowerBound
  have LogIntegrable : Integrable (fun ω => Real.log (X 0 ω / smin)) μ := by
    exact FiniteStateCompositionIntegrable μ (X 0) S (fun s => Real.log (s / smin))
      (CoordinatesMeasurable 0) (ValuesInS 0)
  have PotentialExpectation :
      ExpectedValue μ (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =
        (1 + ExpectedValue μ (fun ω => Real.log (X 0 ω / smin))) / Delta := by
    unfold ExpectedValue
    have PotentialFormula : (fun ω => MultiplicativeDriftPotential smin Delta (X 0 ω)) =ᵐ[μ]
        (fun ω => (1 + Real.log (X 0 ω / smin)) / Delta) := by
      filter_upwards [InitialNonzero] with ω Nonzero
      unfold MultiplicativeDriftPotential
      rw [if_neg Nonzero]
    rw [integral_congr_ae PotentialFormula, integral_div]
    rw [integral_add (integrable_const 1) LogIntegrable, integral_const,
      probReal_univ, one_smul]
  rw [PotentialExpectation] at Bound
  exact Bound

end

end ECTheoryLib.Tools.Drift
