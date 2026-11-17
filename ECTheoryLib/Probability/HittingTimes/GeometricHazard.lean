import ECTheoryLib.Probability.Distributions.GeometricDomination
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import Mathlib.Probability.ConditionalProbability

/-!
# Geometric waiting bounds from conditional success probabilities

A measurable time may be zero or infinite. At each positive-probability survival
event, a lower bound on the probability of finishing in the next step gives a
geometric tail. No Markov property or independence of successive attempts is
assumed. Strictly positive success probability also gives finite extended mean
and almost-sure termination.

The reference geometric waiting time counts trials (1, 2, ...); mathlib counts
failures (0, 1, ...), so its law is shifted by one. This is the single-level
waiting argument used in Theorem 1.8.6 of Doerr (2020), not the whole theorem.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
noncomputable section

/-- A conditional success bound contracts the next survival probability, including null survival events. -/
theorem WaitingSurvivalStep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ) (MeasurableT : Measurable T)
    (p : I) (t : ℕ)
    (Hazard : P {ω | (t : WithTop ℕ) < T ω} ≠ 0 →
      (p : ℝ) ≤ (P[|{ω | (t : WithTop ℕ) < T ω}]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)}) :
    P.real {ω | ((t+1 : ℕ) : WithTop ℕ) < T ω} ≤
      (1-(p : ℝ)) * P.real {ω | (t : WithTop ℕ) < T ω} := by
  let C := {ω | (t : WithTop ℕ) < T ω}
  let D := {ω | ((t+1 : ℕ) : WithTop ℕ) < T ω}
  have MeasurableC : MeasurableSet C := MeasurableT measurableSet_Ioi
  have MeasurableD : MeasurableSet D := MeasurableT measurableSet_Ioi
  have Subset : D ⊆ C := by
    intro ω Later
    have Times : (t : WithTop ℕ) ≤ ((t+1 : ℕ) : WithTop ℕ) := by exact_mod_cast Nat.le_succ t
    exact lt_of_le_of_lt Times Later
  change P.real D ≤ (1-(p : ℝ)) * P.real C
  by_cases ZeroSurvival : P C = 0
  · have NextZero : P D = 0 := measure_mono_null Subset ZeroSurvival
    simp only [measureReal_def, NextZero, ZeroSurvival, ENNReal.toReal_zero, mul_zero, le_refl]
  · have ConditionalProbability : IsProbabilityMeasure P[|C] := cond_isProbabilityMeasure ZeroSurvival
    have Success := Hazard ZeroSurvival
    have FailureBound : (P[|C]).real D ≤ 1-(p : ℝ) := by
      have Complement : Dᶜ = {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)} := by
        ext ω
        change (¬((t+1 : ℕ) : WithTop ℕ) < T ω) ↔ T ω ≤ ((t+1 : ℕ) : WithTop ℕ)
        exact not_lt
      have Total := measureReal_add_measureReal_compl (μ := P[|C]) MeasurableD
      rw [probReal_univ, Complement] at Total
      change (p : ℝ) ≤ (P[|C]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)} at Success
      linarith
    have Product := congrArg ENNReal.toReal (cond_mul_eq_inter MeasurableC D P)
    rw [ENNReal.toReal_mul, inter_eq_right.mpr Subset] at Product
    change (P[|C]).real D * P.real C = P.real D at Product
    rw [← Product]
    exact mul_le_mul_of_nonneg_right FailureBound measureReal_nonneg

/-- Iteration of the survival contraction; the parameter may be zero in this tail-only statement. -/
theorem WaitingSurvivalBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ) (MeasurableT : Measurable T)
    (p : I)
    (Hazard : ∀ t : ℕ, P {ω | (t : WithTop ℕ) < T ω} ≠ 0 →
      (p : ℝ) ≤ (P[|{ω | (t : WithTop ℕ) < T ω}]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)})
    (t : ℕ) : P.real {ω | (t : WithTop ℕ) < T ω} ≤ (1-(p : ℝ))^t := by
  induction t with
  | zero =>
      rw [pow_zero]
      exact measureReal_le_one
  | succ t InductionHypothesis =>
      calc
        _ ≤ (1-(p : ℝ)) * P.real {ω | (t : WithTop ℕ) < T ω} :=
          WaitingSurvivalStep P T MeasurableT p t (Hazard t)
        _ ≤ (1-(p : ℝ)) * (1-(p : ℝ))^t :=
          mul_le_mul_of_nonneg_left InductionHypothesis (sub_nonneg.mpr p.2.2)
        _ = _ := (pow_succ' _ _).symm

/-- The complete waiting-time law is dominated by a geometric trial count; infinity is retained. -/
theorem WaitingGeometricDomination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ) (MeasurableT : Measurable T)
    (p : I) (Positive : 0 < (p : ℝ))
    (Hazard : ∀ t : ℕ, P {ω | (t : WithTop ℕ) < T ω} ≠ 0 →
      (p : ℝ) ≤ (P[|{ω | (t : WithTop ℕ) < T ω}]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)}) :
    StochasticDominated (P.map T)
      ((geometricMeasure p).map (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ))) := by
  have ActualProbability : IsProbabilityMeasure (P.map T) := Measure.isProbabilityMeasure_map MeasurableT.aemeasurable
  have ReferenceProbability : IsProbabilityMeasure
      ((geometricMeasure p).map (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ))) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (StochasticDominatedIffStrictTail _ _).mpr
  intro a
  cases a using WithTop.recTopCoe with
  | top => simp only [Ioi_top, measure_empty, le_refl]
  | coe t =>
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change (P.map T).real (Ioi (t : WithTop ℕ)) ≤
        ((geometricMeasure p).map (fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ))).real (Ioi (t : WithTop ℕ))
      rw [map_measureReal_apply MeasurableT measurableSet_Ioi, GeometricWaitingExtendedTail p Positive]
      exact WaitingSurvivalBound P T MeasurableT p Hazard t


/-- Sum the geometric tail in ENNReal, without assuming a finite expectation in advance. -/
theorem WaitingExpectationBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ) (MeasurableT : Measurable T)
    (p : I) (Positive : 0 < (p : ℝ))
    (Hazard : ∀ t : ℕ, P {ω | (t : WithTop ℕ) < T ω} ≠ 0 →
      (p : ℝ) ≤ (P[|{ω | (t : WithTop ℕ) < T ω}]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)}) :
    (∫⁻ ω, ENat.toENNReal (T ω) ∂P) ≤ ENNReal.ofReal (1/(p : ℝ)) := by
  have NonnegativeFailure : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.2.2
  have TailBound (t : ℕ) : P {ω | (t : WithTop ℕ) < T ω} ≤ (ENNReal.ofReal (1-(p : ℝ)))^t := by
    calc
      P {ω | (t : WithTop ℕ) < T ω} = ENNReal.ofReal (P.real {ω | (t : WithTop ℕ) < T ω}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((1-(p : ℝ))^t) :=
        ENNReal.ofReal_le_ofReal (WaitingSurvivalBound P T MeasurableT p Hazard t)
      _ = _ := ENNReal.ofReal_pow NonnegativeFailure t
  have Complement : 1-ENNReal.ofReal (1-(p : ℝ)) = ENNReal.ofReal (p : ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 NonnegativeFailure]
    congr 1
    ring
  rw [ExpectedWithTopNatEqTailSum P T MeasurableT]
  calc
    _ ≤ ∑' t : ℕ, (ENNReal.ofReal (1-(p : ℝ)))^t := ENNReal.tsum_le_tsum TailBound
    _ = (1-ENNReal.ofReal (1-(p : ℝ)))⁻¹ := ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (1/(p : ℝ)) := by
      rw [Complement, ENNReal.ofReal_div_of_pos Positive, ENNReal.ofReal_one, one_div]

/-- Positive success probability rules out nontermination as a consequence of the finite mean. -/
theorem WaitingFiniteAlmostSurely {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → WithTop ℕ) (MeasurableT : Measurable T)
    (p : I) (Positive : 0 < (p : ℝ))
    (Hazard : ∀ t : ℕ, P {ω | (t : WithTop ℕ) < T ω} ≠ 0 →
      (p : ℝ) ≤ (P[|{ω | (t : WithTop ℕ) < T ω}]).real {ω | T ω ≤ ((t+1 : ℕ) : WithTop ℕ)}) :
    ∀ᵐ ω ∂P, T ω ≠ ⊤ := by
  have ExpectedBound := WaitingExpectationBound P T MeasurableT p Positive Hazard
  have FiniteExpected : (∫⁻ ω, ENat.toENNReal (T ω) ∂P) ≠ ⊤ :=
    (lt_of_le_of_lt ExpectedBound ENNReal.ofReal_lt_top).ne
  have EmbeddedMeasurable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp MeasurableT
  filter_upwards [ae_lt_top EmbeddedMeasurable FiniteExpected] with ω FiniteValue
  intro Infinite
  rw [Infinite] at FiniteValue
  change (⊤ : ENNReal) < ⊤ at FiniteValue
  exact (lt_irrefl _) FiniteValue


/-- Recover the conditional success bound from survival contraction when the conditioning event is nonnull. -/
theorem WaitingHazardOfSurvivalStep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω -> WithTop Nat) (MeasurableT : Measurable T)
    (p : I) (t : Nat) (Nonzero : P {w | (t : WithTop Nat) < T w} ≠ 0)
    (StepBound : P.real {w | ((t+1 : Nat) : WithTop Nat) < T w} ≤
      (1-(p : Real)) * P.real {w | (t : WithTop Nat) < T w}) :
    (p : Real) ≤ (P[|{w | (t : WithTop Nat) < T w}]).real {w | T w ≤ ((t+1 : Nat) : WithTop Nat)} := by
  let C := {w | (t : WithTop Nat) < T w}
  let D := {w | ((t+1 : Nat) : WithTop Nat) < T w}
  have MeasurableC : MeasurableSet C := MeasurableT measurableSet_Ioi
  have MeasurableD : MeasurableSet D := MeasurableT measurableSet_Ioi
  have Subset : D ⊆ C := by
    intro w Later
    have Times : (t : WithTop Nat) ≤ ((t+1 : Nat) : WithTop Nat) := by exact_mod_cast Nat.le_succ t
    exact lt_of_le_of_lt Times Later
  have ConditionalProbability : IsProbabilityMeasure P[|C] := cond_isProbabilityMeasure Nonzero
  have PositiveSurvival : 0 < P.real C := ENNReal.toReal_pos Nonzero (measure_ne_top _ _)
  have Product := congrArg ENNReal.toReal (cond_mul_eq_inter MeasurableC D P)
  rw [ENNReal.toReal_mul, inter_eq_right.mpr Subset] at Product
  change (P[|C]).real D * P.real C = P.real D at Product
  change P.real D ≤ (1-(p : Real))*P.real C at StepBound
  rw [← Product] at StepBound
  have FailureBound : (P[|C]).real D ≤ 1-(p : Real) :=
    (mul_le_mul_iff_left₀ PositiveSurvival).mp StepBound
  have Complement : Dᶜ = {w | T w ≤ ((t+1 : Nat) : WithTop Nat)} := by
    ext w
    change (¬((t+1 : Nat) : WithTop Nat) < T w) ↔ T w ≤ ((t+1 : Nat) : WithTop Nat)
    exact not_lt
  have Total := measureReal_add_measureReal_compl (μ := P[|C]) MeasurableD
  rw [probReal_univ, Complement] at Total
  change (p : Real) ≤ (P[|C]).real {w | T w ≤ ((t+1 : Nat) : WithTop Nat)}
  linarith


end
end ECTheoryLib.Probability
