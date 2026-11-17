import ECTheoryLib.Tools.Drift.Potential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Variable drift upper bound

Source: Johannes Lengler, *Drift Analysis*, Theorem 2.3.3, pp. 100-102,
in Doerr and Neumann (eds.), *Theory of Evolutionary Computation* (2020),
<https://doi.org/10.1007/978-3-030-29414-4_2>.
The corresponding preprint is <https://arxiv.org/abs/1712.00964>, Theorem 3.

The process has a finite pointwise range, an absorbing zero, and arbitrary
random initialization.  `smin` is any positive lower bound for the nonzero
states; choosing the actual minimum gives the paper's bound.  `h` need only
be positive and nondecreasing on `[smin, infinity)`.  Integrability of its
reciprocal on compact intervals is proved from monotonicity, not assumed.

The main bound uses a potential which is zero at an already optimal initial
state.  The displayed formula in the paper is given separately for positive
initialization, so no integral through zero is silently evaluated.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- Lengler's rescaling on the attainable states, including an initial zero. -/
def VariableDriftPotential (smin : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s = 0 then 0 else smin / h smin + ∫ x in smin..s, 1 / h x

/-- A positive monotone drift function has an integrable reciprocal on every
compact interval above the smallest positive state. -/
theorem ReciprocalDriftIntervalIntegrable (smin : ℝ) (h : ℝ → ℝ)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (a b : ℝ) (LowerA : smin ≤ a) (LowerB : smin ≤ b) :
    IntervalIntegrable (fun x => 1 / h x) volume a b := by
  have ReciprocalAntitone : AntitoneOn (fun x => 1 / h x) (Set.uIcc a b) := by
    intro x InX y InY BeforeY
    have LowerX : smin ≤ x := by
      exact (le_min LowerA LowerB).trans InX.1
    have LowerY : smin ≤ y := LowerX.trans BeforeY
    exact one_div_le_one_div_of_le (DriftPositive x LowerX)
      (DriftMonotone LowerX LowerY BeforeY)
  exact ReciprocalAntitone.intervalIntegrable

/-- Integrating the supporting slope below the current state. -/
theorem ReciprocalDriftIntegralLowerBound (smin : ℝ) (h : ℝ → ℝ)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (a b : ℝ) (LowerA : smin ≤ a) (BeforeB : a ≤ b) :
    (b - a) / h b ≤ ∫ x in a..b, 1 / h x := by
  have ReciprocalIntegrable := ReciprocalDriftIntervalIntegrable smin h
    DriftPositive DriftMonotone a b LowerA (LowerA.trans BeforeB)
  have IntegralComparison : (∫ _x in a..b, 1 / h b) ≤ ∫ x in a..b, 1 / h x := by
    apply intervalIntegral.integral_mono_on BeforeB intervalIntegrable_const ReciprocalIntegrable
    intro x InInterval
    have LowerX : smin ≤ x := LowerA.trans InInterval.1
    exact one_div_le_one_div_of_le (DriftPositive x LowerX)
      (DriftMonotone LowerX (LowerA.trans BeforeB) InInterval.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at IntegralComparison
  have ConstantIntegral : (b - a) * (1 / h b) = (b - a) / h b := by ring
  rw [ConstantIntegral] at IntegralComparison
  exact IntegralComparison

/-- Integrating the supporting slope above the current state. -/
theorem ReciprocalDriftIntegralUpperBound (smin : ℝ) (h : ℝ → ℝ)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (a b : ℝ) (LowerA : smin ≤ a) (BeforeB : a ≤ b) :
    (∫ x in a..b, 1 / h x) ≤ (b - a) / h a := by
  have ReciprocalIntegrable := ReciprocalDriftIntervalIntegrable smin h
    DriftPositive DriftMonotone a b LowerA (LowerA.trans BeforeB)
  have IntegralComparison : (∫ x in a..b, 1 / h x) ≤ ∫ _x in a..b, 1 / h a := by
    apply intervalIntegral.integral_mono_on BeforeB ReciprocalIntegrable intervalIntegrable_const
    intro x InInterval
    have LowerX : smin ≤ x := LowerA.trans InInterval.1
    exact one_div_le_one_div_of_le (DriftPositive a LowerA)
      (DriftMonotone LowerA LowerX InInterval.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at IntegralComparison
  have ConstantIntegral : (b - a) * (1 / h a) = (b - a) / h a := by ring
  rw [ConstantIntegral] at IntegralComparison
  exact IntegralComparison

/-- The potential is nonnegative on zero and all allowed positive states. -/
theorem VariableDriftPotentialNonnegative (smin : ℝ) (h : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (s : ℝ) (StateLowerBound : s = 0 ∨ smin ≤ s) :
    0 ≤ VariableDriftPotential smin h s := by
  unfold VariableDriftPotential
  by_cases StateZero : s = 0
  · rw [if_pos StateZero]
  · rw [if_neg StateZero]
    have LowerS : smin ≤ s := StateLowerBound.resolve_left StateZero
    have IntegralNonnegative : 0 ≤ ∫ x in smin..s, 1 / h x := by
      apply intervalIntegral.integral_nonneg LowerS
      intro x InInterval
      exact div_nonneg zero_le_one (DriftPositive x InInterval.1).le
    exact add_nonneg (div_nonneg MinimumPositive.le (DriftPositive smin le_rfl).le)
      IntegralNonnegative

/-- The key deterministic inequality behind variable drift.  Upward jumps
are allowed; their negative potential difference is controlled as well. -/
theorem VariableDriftPotentialDifference (smin : ℝ) (h : ℝ → ℝ)
    (MinimumPositive : 0 < smin)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (s r : ℝ) (LowerS : smin ≤ s) (RangeR : r = 0 ∨ smin ≤ r) :
    (s - r) / h s ≤
      VariableDriftPotential smin h s - VariableDriftPotential smin h r := by
  have StateNonzero : s ≠ 0 := ne_of_gt (MinimumPositive.trans_le LowerS)
  unfold VariableDriftPotential
  rw [if_neg StateNonzero]
  by_cases NextZero : r = 0
  · rw [if_pos NextZero, NextZero, sub_zero, sub_zero]
    have IntegralBound := ReciprocalDriftIntegralLowerBound smin h DriftPositive
      DriftMonotone smin s le_rfl LowerS
    have MinimumContribution : smin / h s ≤ smin / h smin := by
      exact div_le_div_of_nonneg_left MinimumPositive.le
        (DriftPositive smin le_rfl)
        (DriftMonotone (by
          change smin ≤ smin
          exact le_rfl) LowerS LowerS)
    have SplitSlope : s / h s = smin / h s + (s - smin) / h s := by ring
    rw [SplitSlope]
    exact add_le_add MinimumContribution IntegralBound
  · rw [if_neg NextZero]
    have LowerR : smin ≤ r := RangeR.resolve_left NextZero
    have IntegralDifference :
        (∫ x in smin..s, 1 / h x) - (∫ x in smin..r, 1 / h x) =
          ∫ x in r..s, 1 / h x := by
      exact intervalIntegral.integral_interval_sub_left
        (ReciprocalDriftIntervalIntegrable smin h DriftPositive DriftMonotone
          smin s le_rfl LowerS)
        (ReciprocalDriftIntervalIntegrable smin h DriftPositive DriftMonotone
          smin r le_rfl LowerR)
    have CancelConstant :
        smin / h smin + (∫ x in smin..s, 1 / h x) -
          (smin / h smin + ∫ x in smin..r, 1 / h x) =
            (∫ x in smin..s, 1 / h x) - (∫ x in smin..r, 1 / h x) := by ring
    rw [CancelConstant, IntegralDifference]
    by_cases NextBelow : r ≤ s
    · exact ReciprocalDriftIntegralLowerBound smin h DriftPositive DriftMonotone
        r s LowerR NextBelow
    · have CurrentBelow : s ≤ r := le_of_not_ge NextBelow
      have IntegralBound := ReciprocalDriftIntegralUpperBound smin h DriftPositive
        DriftMonotone s r LowerS CurrentBelow
      rw [intervalIntegral.integral_symm]
      have SlopeNegation : (s - r) / h s = -((r - s) / h s) := by ring
      rw [SlopeNegation]
      exact neg_le_neg IntegralBound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- General variable drift upper bound, including random already-optimal
initialization.  No Markov property or pointwise monotone trajectory is assumed. -/
theorem VariableDriftUpperBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (_ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → h s ≤ StateDrift μ X t s) :
    ExpectedZeroHittingTime μ X ≤
      ENNReal.ofReal (ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω))) := by
  apply PotentialDriftUpperBound μ X S h (VariableDriftPotential smin h)
    CoordinatesMeasurable ValuesInS ZeroAbsorbing
  · intro s InS
    exact VariableDriftPotentialNonnegative smin h MinimumPositive DriftPositive
      s (StateLowerBound s InS)
  · intro s InS Nonzero
    exact DriftPositive s ((StateLowerBound s InS).resolve_left Nonzero)
  · intro s InS Nonzero r InR
    exact VariableDriftPotentialDifference smin h MinimumPositive DriftPositive
      DriftMonotone s r ((StateLowerBound s InS).resolve_left Nonzero)
      (StateLowerBound r InR)
  · exact StateDriftLowerBound

/-- Lengler's displayed integral formula for positive random initialization.
The extra initial-state hypothesis is exactly what makes the integral stay
above `smin` even when the initial state is random. -/
theorem VariableDriftUpperBoundOfPositiveInitial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (smin : ℝ) (h : ℝ → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (ZeroInS : 0 ∈ S)
    (MinimumPositive : 0 < smin)
    (StateLowerBound : ∀ s ∈ S, s = 0 ∨ smin ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (DriftPositive : ∀ x, smin ≤ x → 0 < h x)
    (DriftMonotone : MonotoneOn h (Set.Ici smin))
    (StateDriftLowerBound : ∀ t s, s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → h s ≤ StateDrift μ X t s)
    (InitialNonzero : ∀ᵐ ω ∂μ, X 0 ω ≠ 0) :
    ExpectedZeroHittingTime μ X ≤ ENNReal.ofReal
      (smin / h smin + ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1 / h x)) := by
  have Bound := VariableDriftUpperBound μ X S smin h CoordinatesMeasurable
    ZeroInS MinimumPositive StateLowerBound ValuesInS ZeroAbsorbing
    DriftPositive DriftMonotone StateDriftLowerBound
  have IntegralIntegrable : Integrable (fun ω => ∫ x in smin..X 0 ω, 1 / h x) μ := by
    exact FiniteStateCompositionIntegrable μ (X 0) S
      (fun s => ∫ x in smin..s, 1 / h x) (CoordinatesMeasurable 0) (ValuesInS 0)
  have PotentialExpectation :
      ExpectedValue μ (fun ω => VariableDriftPotential smin h (X 0 ω)) =
        smin / h smin + ExpectedValue μ (fun ω => ∫ x in smin..X 0 ω, 1 / h x) := by
    unfold ExpectedValue
    have PotentialFormula : (fun ω => VariableDriftPotential smin h (X 0 ω)) =ᵐ[μ]
        (fun ω => smin / h smin + ∫ x in smin..X 0 ω, 1 / h x) := by
      filter_upwards [InitialNonzero] with ω Nonzero
      unfold VariableDriftPotential
      rw [if_neg Nonzero]
    rw [integral_congr_ae PotentialFormula]
    rw [integral_add (integrable_const _) IntegralIntegrable, integral_const,
      probReal_univ, one_smul]
  rw [PotentialExpectation] at Bound
  exact Bound

end

end ECTheoryLib.Tools.Drift
