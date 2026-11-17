import ECTheoryLib.Probability.Distributions.BinarySumLaw
import ECTheoryLib.Analysis.OneMax.RLS.AccumulatedPotential
import ECTheoryLib.Analysis.OneMax.RLS.LastBitRuntime

/-!
# Binomial bounds for last-bit RLS accumulated potential

The independent reference law is derived from the actual one-step kernel:
the potential is binary and its success mass is computed from exact drift.
The accumulated trajectory cost stays dependent; its earlier comparison
transfers the full binomial reference and every strict upper-tail bound.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- After one actual step from one zero, the potential is almost surely binary. -/
theorem LastBitStepPotentialBinary {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    ∀ᵐ y ∂(Step PositiveLength InitialState).toMeasure,
      Potential y = 0 ∨ Potential y = 1 := by
  filter_upwards [StepPotentialNonincreasing PositiveLength InitialState] with y Bound
  change (ZeroCount y : ℝ) ≤ (ZeroCount InitialState : ℝ) at Bound
  rw [OneZero, Nat.cast_one] at Bound
  have CountBound : ZeroCount y ≤ 1 := by exact_mod_cast Bound
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp CountBound with Zero | One
  · left
    change (ZeroCount y : ℝ) = 0
    rw [Zero, Nat.cast_zero]
  · right
    change (ZeroCount y : ℝ) = 1
    rw [One, Nat.cast_one]

/-- Probability of leaving the last zero unchanged in one iteration: 1 - 1/n. -/
def LastBitRemainingProbability (n : ℕ) (PositiveLength : 0 < n) : I :=
  unitInterval.symm (LastBitSuccessProbability n PositiveLength)

/-- The exact remaining-bit probability, derived from the real transition drift. -/
theorem LastBitOneStepRemainingProbability {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) :
    (Step PositiveLength InitialState).toMeasure {y | Potential y = 1} =
      ENNReal.ofReal (LastBitRemainingProbability n PositiveLength : ℝ) := by
  have InitialPotential : Potential InitialState = 1 := by
    change (ZeroCount InitialState : ℝ) = 1
    rw [OneZero, Nat.cast_one]
  have Drift := OneStepDrift PositiveLength InitialState
  rw [integral_sub (integrable_const _) Integrable.of_finite,
    integral_const, probReal_univ, one_smul, InitialPotential] at Drift
  have Mean := BinaryVariableMean (Step PositiveLength InitialState).toMeasure Potential
    (measurable_of_finite Potential) (LastBitStepPotentialBinary PositiveLength InitialState OneZero)
  have RealMass : (Step PositiveLength InitialState).toMeasure.real {y | Potential y = 1} =
      1 - 1 / (n : ℝ) := by linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (Step PositiveLength InitialState).toMeasure _)]
  change ENNReal.ofReal ((Step PositiveLength InitialState).toMeasure.real {y | Potential y = 1}) = _
  rw [RealMass]
  rfl

/-- The complete binomial law of independent actual first-step experiments. -/
theorem IndependentLastBitPotentialSumLaw {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    HasLaw (fun Draws : ℕ → Bits n => ∑ i ∈ Finset.range t, Potential (Draws i))
      ((binomial t (LastBitRemainingProbability n PositiveLength)).map (Nat.cast : ℕ → ℝ))
      (IndependentOneStepMeasure PositiveLength InitialState) := by
  let Q := IndependentOneStepMeasure PositiveLength InitialState
  have MeasurableY (i : ℕ) : Measurable (fun Draws : ℕ → Bits n => Potential (Draws i)) :=
    (measurable_of_finite Potential).comp (measurable_pi_apply i)
  have Marginal (i : ℕ) : HasLaw (fun Draws : ℕ → Bits n => Potential (Draws i))
      ((Step PositiveLength InitialState).toMeasure.map Potential) Q := by
    refine ⟨(MeasurableY i).aemeasurable, ?_⟩
    have MeasurablePotential : Measurable (Potential (n := n)) := measurable_of_finite _
    have MeasurableCoordinate : Measurable (fun Draws : ℕ → Bits n => Draws i) := measurable_pi_apply i
    change Measure.map ((Potential (n := n)) ∘ (fun Draws : ℕ → Bits n => Draws i))
      (Measure.infinitePi (fun _ : ℕ => (Step PositiveLength InitialState).toMeasure)) = _
    rw [← Measure.map_map MeasurablePotential MeasurableCoordinate, Measure.infinitePi_map_eval]
  have BinaryY (i : ℕ) : ∀ᵐ Draws ∂Q, Potential (Draws i) = 0 ∨ Potential (Draws i) = 1 := by
    apply ((Marginal i).ae_iff (p := fun x => x = 0 ∨ x = 1) (by fun_prop)).mpr
    apply (ae_map_iff (measurable_of_finite Potential).aemeasurable
      ((measurableSet_singleton (0 : ℝ)).union (measurableSet_singleton 1))).mpr
    exact LastBitStepPotentialBinary PositiveLength InitialState OneZero
  have SuccessY (i : ℕ) : Q {Draws | Potential (Draws i) = 1} =
      ENNReal.ofReal (LastBitRemainingProbability n PositiveLength : ℝ) := by
    rw [(Marginal i).measure_eq (p := fun x => x = 1) (measurableSet_singleton 1)]
    have MeasurablePotential : Measurable (Potential (n := n)) := measurable_of_finite _
    change ((Step PositiveLength InitialState).toMeasure.map (Potential (n := n))) {1} = _
    rw [Measure.map_apply MeasurablePotential (measurableSet_singleton 1)]
    exact LastBitOneStepRemainingProbability PositiveLength InitialState OneZero
  have IndependentAll : iIndepFun (fun i => fun Draws : ℕ → Bits n => Potential (Draws i)) Q :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_of_finite Potential)
  have Law := IndependentBinarySumLaw Q t (LastBitRemainingProbability n PositiveLength)
    (fun i : Fin t => fun Draws => Potential (Draws i)) (fun i => MeasurableY i)
    (fun i => BinaryY i) (IndependentAll.precomp Fin.val_injective) (fun i => SuccessY i)
  have FunctionEq : (fun Draws : ℕ → Bits n => ∑ i : Fin t, Potential (Draws i)) =
      (fun Draws => ∑ i ∈ Finset.range t, Potential (Draws i)) := by
    funext Draws
    exact Fin.sum_univ_eq_sum_range (fun i => Potential (Draws i)) t
  rw [FunctionEq] at Law
  exact Law

/-- A binomial upper reference for dependent finite-horizon RLS accumulated potential. -/
theorem LastBitAccumulatedPotentialBinomialBound {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (fun Path => ∑ i ∈ Finset.range t, Potential (Path (i + 1))))
      ((binomial t (LastBitRemainingProbability n PositiveLength)).map (Nat.cast : ℕ → ℝ)) := by
  have Bound := LastBitAccumulatedPotentialDominated PositiveLength InitialState OneZero t
  rw [(IndependentLastBitPotentialSumLaw PositiveLength InitialState OneZero t).map_eq] at Bound
  exact Bound

/-- Any binomial strict upper-tail bound transfers to the actual accumulated potential. -/
theorem LastBitAccumulatedPotentialTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) (a : ℝ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | a < ∑ i ∈ Finset.range t, Potential (Path (i + 1))} ≤
      ((binomial t (LastBitRemainingProbability n PositiveLength)).map (Nat.cast : ℕ → ℝ))
        (Set.Ioi a) := by
  have MeasurableSum : Measurable (fun Path : ℕ → Bits n =>
      ∑ i ∈ Finset.range t, Potential (Path (i + 1))) :=
    Finset.measurable_sum _ (fun i _ => (measurable_of_finite Potential).comp
      (measurable_pi_apply (i + 1)))
  have ProbabilitySum : IsProbabilityMeasure
      ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (fun Path => ∑ i ∈ Finset.range t, Potential (Path (i + 1)))) :=
    Measure.isProbabilityMeasure_map MeasurableSum.aemeasurable
  have Bound := (StochasticDominatedIffStrictTail _ _).mp
    (LastBitAccumulatedPotentialBinomialBound PositiveLength InitialState OneZero t) a
  rw [Measure.map_apply MeasurableSum measurableSet_Ioi] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
