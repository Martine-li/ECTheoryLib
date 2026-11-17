import ECTheoryLib.Probability.Moments.ConditionalSubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-horizon Azuma-Hoeffding adapters

Reuse fixed Mathlib conditional-MGF iteration. All process assumptions are local to the displayed
horizon; no exponential moment or deterministic value for the initial state
is imposed. The ambient standard Borel qualification is explicit.
-/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- A bounded, genuinely conditionally centered finite sum is sub-Gaussian. -/
theorem BoundedConditionalSumSubGaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0) (horizon : ℕ)
    (NextObservable : ∀ i < horizon, StronglyMeasurable[F (i + 1)] (Z i))
    (Bounded : ∀ i < horizon, ∀ᵐ ω ∂P, |Z i ω| ≤ (c i : ℝ))
    (Centered : ∀ i < horizon, P[Z i | F i] =ᵐ[P] (fun _ => 0)) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.range horizon, Z i ω)
      (∑ i ∈ Finset.range horizon, c i ^ 2) P := by
  let Y : ℕ → Ω → ℝ
    | 0 => fun _ => 0
    | i + 1 => if i < horizon then Z i else fun _ => 0
  let q : ℕ → ℝ≥0
    | 0 => 0
    | i + 1 => if i < horizon then c i ^ 2 else 0
  have AdaptedY : StronglyAdapted F Y := by
    intro j
    cases j with
    | zero => exact stronglyMeasurable_const
    | succ i =>
      by_cases Within : i < horizon
      · simpa only [Y, if_pos Within] using NextObservable i Within
      · simpa only [Y, if_neg Within] using
          (stronglyMeasurable_const : StronglyMeasurable[F (i + 1)] (fun _ : Ω => (0 : ℝ)))
  have First : HasSubgaussianMGF (Y 0) (q 0) P := by
    simpa only [Y, q] using (HasSubgaussianMGF.fun_zero (μ := P))
  have Conditional (i : ℕ) (Inside : i < (horizon + 1) - 1) :
      HasCondSubgaussianMGF (F i) (F.le i) (Y (i + 1)) (q (i + 1)) P := by
    have Within : i < horizon := by simpa only [Nat.add_sub_cancel] using Inside
    have Ambient : AEMeasurable (Z i) P :=
      ((NextObservable i Within).mono (F.le (i + 1))).measurable.aemeasurable
    simpa only [Y, q, if_pos Within] using
      (ConditionalSubGaussianOfBoundedCentered (mΩ := mΩ) P (F i) (F.le i)
        (Z i) (c i) Ambient (Bounded i Within) (Centered i Within))
  have Whole := HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
    AdaptedY First (horizon + 1) Conditional
  have SumY (ω : Ω) :
      (∑ j ∈ Finset.range (horizon + 1), Y j ω) =
        ∑ i ∈ Finset.range horizon, Z i ω := by
    rw [Finset.sum_range_succ']
    simp only [Y, add_zero]
    apply Finset.sum_congr rfl
    intro i Member
    rw [if_pos (Finset.mem_range.mp Member)]
  have SumQ : (∑ j ∈ Finset.range (horizon + 1), q j) =
      ∑ i ∈ Finset.range horizon, c i ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [q, add_zero]
    apply Finset.sum_congr rfl
    intro i Member
    rw [if_pos (Finset.mem_range.mp Member)]
  simpa only [SumY, SumQ] using Whole

/-- Closed upper tail for a finite sum of bounded conditionally centered increments. -/
theorem BoundedConditionalSumUpperTail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0) (horizon : ℕ)
    (NextObservable : ∀ i < horizon, StronglyMeasurable[F (i + 1)] (Z i))
    (Bounded : ∀ i < horizon, ∀ᵐ ω ∂P, |Z i ω| ≤ (c i : ℝ))
    (Centered : ∀ i < horizon, P[Z i | F i] =ᵐ[P] (fun _ => 0))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | threshold ≤ ∑ i ∈ Finset.range horizon, Z i ω} ≤
      Real.exp (-threshold ^ 2 / (2 * ∑ i ∈ Finset.range horizon, (c i : ℝ) ^ 2)) := by
  have Bound := (BoundedConditionalSumSubGaussian P F Z c horizon
    NextObservable Bounded Centered).measure_ge_le Nonnegative
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using Bound

/-- Finite martingale Azuma bound; integrable random initial values are allowed. -/
theorem FiniteMartingaleAzumaUpperTail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0) (horizon : ℕ)
    (Observable : ∀ i ≤ horizon, StronglyMeasurable[F i] (X i))
    (IntegrableX : ∀ i ≤ horizon, Integrable (X i) P)
    (OneStepMean : ∀ i < horizon, P[X (i + 1) | F i] =ᵐ[P] X i)
    (Bounded : ∀ i < horizon, ∀ᵐ ω ∂P, |X (i + 1) ω - X i ω| ≤ (c i : ℝ))
    (threshold : ℝ) (Nonnegative : 0 ≤ threshold) :
    P.real {ω | threshold ≤ X horizon ω - X 0 ω} ≤
      Real.exp (-threshold ^ 2 / (2 * ∑ i ∈ Finset.range horizon, (c i : ℝ) ^ 2)) := by
  have NextObservable (i : ℕ) (Within : i < horizon) :
      StronglyMeasurable[F (i + 1)] (fun ω => X (i + 1) ω - X i ω) :=
    (Observable (i + 1) (Nat.succ_le_of_lt Within)).sub
      ((Observable i Within.le).mono (F.mono (Nat.le_succ i)))
  have Centered (i : ℕ) (Within : i < horizon) :
      P[fun ω => X (i + 1) ω - X i ω | F i] =ᵐ[P] (fun _ => 0) := by
    have Subtract := condExp_sub (IntegrableX (i + 1) (Nat.succ_le_of_lt Within))
      (IntegrableX i Within.le) (F i)
    have Now := condExp_of_stronglyMeasurable (F.le i)
      (Observable i Within.le) (IntegrableX i Within.le)
    filter_upwards [Subtract, OneStepMean i Within] with ω SubtractAt MeanAt
    calc
      _ = (P[X (i + 1) | F i]) ω - (P[X i | F i]) ω := SubtractAt
      _ = 0 := by rw [Now, MeanAt, sub_self]
  have Bound := BoundedConditionalSumUpperTail P F
    (fun i ω => X (i + 1) ω - X i ω) c horizon
    NextObservable Bounded Centered threshold Nonnegative
  have Telescope (ω : Ω) : (∑ i ∈ Finset.range horizon, (X (i + 1) ω - X i ω)) =
      X horizon ω - X 0 ω := Finset.sum_range_sub (fun i => X i ω) horizon
  simpa only [Telescope] using Bound

end
end ECTheoryLib.Probability

