import ECTheoryLib.Probability.Distributions.GeometricDomination
import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Analysis.OneMax.RLS.UniformRuntimeBound
import ECTheoryLib.Probability.Processes.PathDrift
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime

/-!
# The actual RLS runtime from one remaining zero bit

The shared StochasticProgress mean contraction and elitist preservation identify
the full hitting-time
law with a shifted geometric law of success probability 1/n. This is proved
from the actual trajectory measure, not supplied as an independence or waiting-law
assumption. The runtime keeps its extended-natural type, including infinity.
The corrected geometric parameter comparison then compares different lengths.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Elitist updates bound each later potential by its fixed initial value almost surely. -/
theorem PotentialAtTimeLEInitial {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) (PMF.pure InitialState),
      Potential (Path t) ≤ Potential InitialState := by
  exact PathPotentialLeInitial PositiveLength InitialState t

/-- With one initial zero, the potential is the indicator of not having reached zero. -/
private theorem LastBitPotentialIndicator {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    (fun Path => Potential (Path t)) =ᵐ[PathMeasure (Step PositiveLength) (PMF.pure InitialState)]
      Set.indicator {Path | Potential (Path t) ≠ 0} (fun _ => (1 : ℝ)) := by
  classical
  filter_upwards [PotentialAtTimeLEInitial PositiveLength InitialState t] with Path BelowInitial
  change (ZeroCount (Path t) : ℝ) ≤ (ZeroCount InitialState : ℝ) at BelowInitial
  rw [OneZero, Nat.cast_one] at BelowInitial
  have CountAtMostOne : ZeroCount (Path t) ≤ 1 := by exact_mod_cast BelowInitial
  by_cases Zero : ZeroCount (Path t) = 0
  · have PotentialZero : Potential (Path t) = 0 := by
      change (ZeroCount (Path t) : ℝ) = 0
      rw [Zero, Nat.cast_zero]
    rw [Set.indicator_of_notMem (show Path ∉ {Path | Potential (Path t) ≠ 0} by
      exact not_not.mpr PotentialZero), PotentialZero]
  · have CountOne : ZeroCount (Path t) = 1 := by omega
    have PotentialOne : Potential (Path t) = 1 := by
      change (ZeroCount (Path t) : ℝ) = 1
      rw [CountOne, Nat.cast_one]
    rw [Set.indicator_of_mem (show Path ∈ {Path | Potential (Path t) ≠ 0} by
      rw [Set.mem_ofPred_eq, PotentialOne]
      exact one_ne_zero), PotentialOne]

/-- Exact runtime tail from one remaining zero bit; no prior termination assumption. -/
theorem LastBitRuntimeTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState)).real
      {Path | (t : WithTop ℕ) < FirstHittingTime IsTarget Path} =
        (1 - 1 / (n : ℝ)) ^ t := by
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun k Path => Potential (Path k)
  have MeasurableX : ∀ k, Measurable (X k) :=
    fun k => (measurable_of_finite Potential).comp (measurable_pi_apply k)
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro k
    have Follows := PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) k
    filter_upwards [Follows] with Path Nonincreasing
    intro AtZero
    apply le_antisymm
    · exact Nonincreasing.trans AtZero.le
    · exact PotentialNonnegative _
  have TailEvent := ZeroHittingTimeTailMeasureOfAbsorbing μ X Absorbing t
  have RuntimeEq : ZeroHittingTime X = FirstHittingTime (IsTarget (n := n)) := by
    funext Path
    exact ZeroHittingTimeEqRuntime Path
  rw [RuntimeEq] at TailEvent
  have IndicatorMean : (∫ Path, Potential (Path t) ∂μ) =
      μ.real {Path | Potential (Path t) ≠ 0} := by
    have EventMeasurable : MeasurableSet {Path : ℕ → Bits n | Potential (Path t) ≠ 0} :=
      (measurableSet_eq_fun (MeasurableX t) measurable_const).compl
    rw [integral_congr_ae (LastBitPotentialIndicator PositiveLength InitialState OneZero t)]
    rw [integral_indicator_const (μ := μ) (1 : ℝ) EventMeasurable]
    simp only [smul_eq_mul, mul_one]
  change μ.real {Path | (t : WithTop ℕ) < FirstHittingTime IsTarget Path} = _
  rw [measureReal_def, TailEvent, ← measureReal_def, ← IndicatorMean]
  rw [ExpectedPotentialExact, PMF.toMeasure_pure, integral_dirac]
  change (1 - 1 / (n : ℝ)) ^ t * (ZeroCount InitialState : ℝ) = _
  rw [OneZero, Nat.cast_one, mul_one]

/-- The positive probability 1/n of selecting the sole remaining zero coordinate. -/
def LastBitSuccessProbability (n : ℕ) (PositiveLength : 0 < n) : unitInterval :=
  ⟨1 / (n : ℝ), by
    have PositiveReal : (0 : ℝ) < n := by exact_mod_cast PositiveLength
    have AtLeastOne : (1 : ℝ) ≤ n := by exact_mod_cast PositiveLength
    exact ⟨(one_div_pos.mpr PositiveReal).le, (div_le_one PositiveReal).mpr AtLeastOne⟩⟩

/-- Complete shifted geometric law for the actual hitting time, retaining its infinity value. -/
theorem LastBitRuntimeHasLaw {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    HasLaw (FirstHittingTime (IsTarget (n := n)))
      ((geometricMeasure (LastBitSuccessProbability n PositiveLength)).map
        (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ)))
      (PathMeasure (Step PositiveLength) (PMF.pure InitialState)) := by
  have RuntimeMeasurable : Measurable (FirstHittingTime (IsTarget (n := n))) :=
    FirstHittingTimeProcessMeasurable IsTarget (fun k (Path : ℕ → Bits n) => Path k)
      (Set.to_countable _).measurableSet (fun k => measurable_pi_apply k)
  have RuntimeProbability : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (FirstHittingTime (IsTarget (n := n)))) :=
    Measure.isProbabilityMeasure_map RuntimeMeasurable.aemeasurable
  have GeometricProbability : IsProbabilityMeasure
      ((geometricMeasure (LastBitSuccessProbability n PositiveLength)).map
        (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have PositiveRate : 0 < (LastBitSuccessProbability n PositiveLength : ℝ) := by
    change 0 < 1 / (n : ℝ)
    apply one_div_pos.mpr
    exact_mod_cast PositiveLength
  refine ⟨RuntimeMeasurable.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro a
  cases a using WithTop.recTopCoe with
  | top => simp only [Set.Iic_top, measure_univ]
  | coe k =>
      rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
        prob_compl_eq_one_sub measurableSet_Ioi]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change (((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (FirstHittingTime (IsTarget (n := n)))).real (Set.Ioi (k : WithTop ℕ))) =
          ((geometricMeasure (LastBitSuccessProbability n PositiveLength)).map
            (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))).real (Set.Ioi (k : WithTop ℕ))
      rw [map_measureReal_apply RuntimeMeasurable measurableSet_Ioi,
        GeometricWaitingExtendedTail _ PositiveRate]
      exact LastBitRuntimeTail PositiveLength InitialState OneZero k

/-- When each instance has one initial zero, increasing the length increases runtime in law. -/
theorem LastBitRuntimeStochasticMonotone {n m : ℕ}
    (PositiveN : 0 < n) (PositiveM : 0 < m) (Lengths : n ≤ m)
    (InitialN : Bits n) (InitialM : Bits m)
    (OneZeroN : ZeroCount InitialN = 1) (OneZeroM : ZeroCount InitialM = 1) :
    StochasticDominated
      ((PathMeasure (Step PositiveN) (PMF.pure InitialN)).map
        (FirstHittingTime (IsTarget (n := n))))
      ((PathMeasure (Step PositiveM) (PMF.pure InitialM)).map
        (FirstHittingTime (IsTarget (n := m)))) := by
  rw [(LastBitRuntimeHasLaw PositiveN InitialN OneZeroN).map_eq,
    (LastBitRuntimeHasLaw PositiveM InitialM OneZeroM).map_eq]
  apply GeometricWaitingExtendedStochasticAntitone
  · change 0 < 1 / (m : ℝ)
    apply one_div_pos.mpr
    exact_mod_cast PositiveM
  · change 1 / (m : ℝ) ≤ 1 / (n : ℝ)
    apply one_div_le_one_div_of_le
    · exact_mod_cast PositiveN
    · exact_mod_cast Lengths

/-- The full geometric law implies that actual nontermination has probability zero. -/
theorem LastBitRuntimeNonterminationProbability {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path = ⊤} = 0 := by
  have Law := LastBitRuntimeHasLaw PositiveLength InitialState OneZero
  rw [Law.measure_eq (p := fun t : WithTop ℕ => t = ⊤)
    (measurableSet_singleton (⊤ : WithTop ℕ))]
  change ((geometricMeasure (LastBitSuccessProbability n PositiveLength)).map
    (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ))) {⊤} = 0
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (⊤ : WithTop ℕ))]
  have EmptyFiber : (fun j : ℕ => ((j + 1 : ℕ) : WithTop ℕ)) ⁻¹' {⊤} = ∅ := by
    ext j
    simp
  rw [EmptyFiber, measure_empty]

end
end ECTheoryLib.Analysis.RLSOnOneMax
