import ECTheoryLib.Tools.Drift.ExponentialTail
import ECTheoryLib.Probability.Moments.BoundedExponentialMoment
import Mathlib.Tactic.FieldSimp

/-!
# Bounded-jump additive drift upper tail

Positive state-event drift and a bounded absolute jump give a Gaussian upper
tail for the first hit of an absorbing interval. The sample space is arbitrary;
only the common scalar range is finite. Thresholds may be negative, and the
drift-time equality is included. Time counts transitions after initialization.

This derives a bounded-jump strict upper-tail variant using the existing
Hoeffding moment bound and killed-exponential drift theorem. It is not the
full geometric-jump upper/lower-tail statement printed as Lengler Theorem 2.4.7.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Positive additive drift with bounded jumps gives a Gaussian-shaped upper
tail beyond the drift-time bound. Time counts transitions after initialization. -/
theorem BoundedAdditiveDriftUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a s₀ c Delta : ℝ)
    (Coordinates : ∀ j, Measurable (X j))
    (Values : ∀ j ω, X j ω ∈ S)
    (Absorbing : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ a → X (j + 1) ω ≤ a)
    (Jumps : ∀ j, ∀ᵐ ω ∂μ, a < X j ω → |X (j + 1) ω - X j ω| ≤ c)
    (StateMean : ∀ (j : ℕ) (s : ℝ), s ∈ S → a < s →
      0 < μ (StateEvent X j s) → Delta ≤ StateDrift μ X j s)
    (PositiveC : 0 < c) (PositiveDelta : 0 < Delta)
    (InitialAbove : a < s₀) (FixedInitial : ∀ᵐ ω ∂μ, X 0 ω = s₀)
    (t : ℕ) (PositiveTime : 0 < t)
    (LateEnough : s₀ - a ≤ Delta * (t : ℝ)) :
    μ {ω | (t : WithTop ℕ) <
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω)} ≤
      ENNReal.ofReal (Real.exp
        (-((Delta * (t : ℝ) - (s₀ - a)) ^ 2) / (2 * (t : ℝ) * c ^ 2))) := by
  classical
  let Lambda := (Delta * (t : ℝ) - (s₀ - a)) / ((t : ℝ) * c ^ 2)
  have TimePositive : 0 < (t : ℝ) := Nat.cast_pos.mpr PositiveTime
  have DenominatorPositive : 0 < (t : ℝ) * c ^ 2 :=
    mul_pos TimePositive (sq_pos_of_pos PositiveC)
  have NonnegativeLambda : 0 ≤ Lambda :=
    div_nonneg (sub_nonneg.mpr LateEnough) DenominatorPositive.le
  have Moment (j : ℕ) (s : ℝ) (InS : s ∈ S) (Above : a < s)
      (Positive : 0 < μ (StateEvent X j s)) :
      EventConditionalExpectation μ
        (fun ω => Real.exp (Lambda * (X (j + 1) ω - X j ω)))
        (StateEvent X j s) ≤ Real.exp (-Lambda * Delta + c ^ 2 * Lambda ^ 2 / 2) := by
    let ν := cond μ (StateEvent X j s)
    let : IsProbabilityMeasure ν := cond_isProbabilityMeasure Positive.ne'
    have Current : ∀ᵐ ω ∂ν, X j ω = s :=
      ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have Bounded : ∀ᵐ ω ∂ν, X j ω - X (j + 1) ω ∈ Set.Icc (-c) c := by
      filter_upwards [Current, cond_absolutelyContinuous.ae_le (Jumps j)] with ω Equal Jump
      have Bound := Jump (by rw [Equal]; exact Above)
      rw [abs_sub_comm] at Bound
      exact abs_le.mp Bound
    have MeanLower : Delta ≤ ∫ ω, X j ω - X (j + 1) ω ∂ν := by
      have Bound := StateMean j s InS Above Positive
      rw [StateDrift, EventConditionalExpectationEqCondIntegral] at Bound
      exact Bound
    have Hoeffding := BoundedVariableExponentialMoment ν
      (fun ω => X j ω - X (j + 1) ω) (-c) c (-Lambda)
      ((Coordinates j).sub (Coordinates (j + 1))).aemeasurable Bounded
    have ScaledMean : Lambda * Delta ≤ Lambda * (∫ ω, X j ω - X (j + 1) ω ∂ν) :=
      mul_le_mul (le_refl Lambda) MeanLower PositiveDelta.le NonnegativeLambda
    rw [EventConditionalExpectationEqCondIntegral]
    calc
      (∫ ω, Real.exp (Lambda * (X (j + 1) ω - X j ω)) ∂ν) =
          ∫ ω, Real.exp ((-Lambda) * (X j ω - X (j + 1) ω)) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ (fun ω => congrArg Real.exp (by ring))
      _ ≤ Real.exp ((-Lambda) * (∫ ω, X j ω - X (j + 1) ω ∂ν) +
          (c - -c) ^ 2 * (-Lambda) ^ 2 / 8) := Hoeffding
      _ = Real.exp (-Lambda * (∫ ω, X j ω - X (j + 1) ω ∂ν) +
          c ^ 2 * Lambda ^ 2 / 2) := by
        congr 1
        ring
      _ ≤ Real.exp (-Lambda * Delta + c ^ 2 * Lambda ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [ScaledMean]
  have Bound := ExponentialDriftUpperTailOfFixedInitial μ X S a Lambda s₀ id
    (fun _ => Real.exp (-Lambda * Delta + c ^ 2 * Lambda ^ 2 / 2))
    Coordinates Values Absorbing NonnegativeLambda
    (fun _ => (Real.exp_pos _).le) (fun _ _ Above => Above.le)
    Moment InitialAbove FixedInitial t
  have OptimizedExponent :
      (t : ℝ) * (-Lambda * Delta + c ^ 2 * Lambda ^ 2 / 2) + Lambda * (s₀ - a) =
        -((Delta * (t : ℝ) - (s₀ - a)) ^ 2) / (2 * (t : ℝ) * c ^ 2) := by
    dsimp [Lambda]
    field_simp [TimePositive.ne', PositiveC.ne']
    ring
  simp only [id_eq, Finset.prod_const, Finset.card_range] at Bound
  rw [← Real.exp_nat_mul, ← Real.exp_add, OptimizedExponent] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Drift
