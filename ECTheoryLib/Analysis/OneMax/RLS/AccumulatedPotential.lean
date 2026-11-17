import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Probability.Processes.PathInvariant
import ECTheoryLib.Probability.Processes.PathSumDomination
import Mathlib.Probability.Independence.InfinitePi

/-!
# Accumulated RLS potential from one remaining zero

The real sequence is dependent: after optimization it stays zero. Its total
potential through a finite horizon is dominated by independent repetitions of
the actual first-step experiment. Reachability, local domination, independence
and marginal laws are all proved here; callers supply only the initial state.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- From one zero bit, the real RLS state is either the initial state or an optimum. -/
theorem LastBitStates {n : ℕ} (PositiveLength : 0 < n) (InitialState : Bits n)
    (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) (PMF.pure InitialState),
      Path t = InitialState ∨ Potential (Path t) = 0 := by
  have Initially : ∀ᵐ x ∂(PMF.pure InitialState).toMeasure,
      x = InitialState ∨ Potential x = 0 := by
    rw [PMF.toMeasure_pure]
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr (Or.inl rfl)
  have Preserved (x : Bits n) : ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      (x = InitialState ∨ Potential x = 0) → (y = InitialState ∨ Potential y = 0) := by
    have InRange : ∀ᵐ y ∂(Step PositiveLength x).toMeasure, y ∈ Set.range (Update x) := by
      rw [Step, RLSStepEqUniformUpdate,
        ← PMF.toMeasure_map (Update x) (UniformBitIndex n PositiveLength) (measurable_of_finite _)]
      apply ae_map_mem_range
      exact (Set.to_countable _).measurableSet
    filter_upwards [InRange, StepPotentialNonincreasing PositiveLength x] with y Supported Nonincreasing
    intro Valid
    rcases Valid with Fixed | Optimum
    · subst x
      obtain ⟨i, UpdateEq⟩ := Supported
      rw [← UpdateEq]
      by_cases One : InitialState i = true
      · exact Or.inl (RLSRejectsOneFlip InitialState i One)
      · right
        have Decrease := PotentialDecrease InitialState i
        rw [if_neg One] at Decrease
        have InitialPotential : Potential InitialState = 1 := by
          change (ZeroCount InitialState : ℝ) = 1
          rw [OneZero, Nat.cast_one]
        linarith
    · right
      rw [Optimum] at Nonincreasing
      exact le_antisymm Nonincreasing (PotentialNonnegative y)
  exact PathMeasurePreservesProperty (Step PositiveLength) (PMF.pure InitialState)
    (fun x => x = InitialState ∨ Potential x = 0) Initially Preserved t

/-- The next-state potential from either reachable case is dominated by one fresh initial step. -/
theorem LastBitStepPotentialDominated {n : ℕ} (PositiveLength : 0 < n)
    (InitialState x : Bits n) (Legal : x = InitialState ∨ Potential x = 0) :
    StochasticDominated ((Step PositiveLength x).toMeasure.map Potential)
      ((Step PositiveLength InitialState).toMeasure.map Potential) := by
  rcases Legal with Fixed | Optimum
  · rw [Fixed]
    exact StochasticDominatedRefl _
  · have ZeroAE : Potential =ᵐ[(Step PositiveLength x).toMeasure] (fun _ => 0) := by
      filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Bound
      rw [Optimum] at Bound
      exact le_antisymm Bound (PotentialNonnegative y)
    have Lower := StochasticDominatedOfAELe (Step PositiveLength InitialState).toMeasure
      (fun _ => (0 : ℝ)) Potential measurable_const.aemeasurable
      (measurable_of_finite Potential).aemeasurable
      (ae_of_all _ (fun y => PotentialNonnegative y))
    rw [Measure.map_congr ZeroAE, Measure.map_const, measure_univ, one_smul]
    rw [Measure.map_const, measure_univ, one_smul] at Lower
    exact Lower

/-- Independent repetitions of the actual one-step experiment from the initial state. -/
abbrev IndependentOneStepMeasure {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) : Measure (ℕ → Bits n) :=
  Measure.infinitePi (fun _ : ℕ => (Step PositiveLength InitialState).toMeasure)

/-- The accumulated actual potential is dominated by independent one-step potentials.
This compares a finite-horizon cost, not independent runs of the full algorithm. -/
theorem LastBitAccumulatedPotentialDominated {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (OneZero : ZeroCount InitialState = 1) (t : ℕ) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) (PMF.pure InitialState)).map
        (fun Path => ∑ i ∈ Finset.range t, Potential (Path (i + 1))))
      ((IndependentOneStepMeasure PositiveLength InitialState).map
        (fun Draws => ∑ i ∈ Finset.range t, Potential (Draws i))) := by
  have MeasurableY (i : ℕ) : Measurable (fun Draws : ℕ → Bits n => Potential (Draws i)) :=
    (measurable_of_finite Potential).comp (measurable_pi_apply i)
  have IndependentY : iIndepFun (fun i => fun Draws : ℕ → Bits n => Potential (Draws i))
      (IndependentOneStepMeasure PositiveLength InitialState) :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_of_finite Potential)
  apply PathPotentialSumStochasticDominated (Step PositiveLength) (PMF.pure InitialState)
    Potential (IndependentOneStepMeasure PositiveLength InitialState)
    (fun i Draws => Potential (Draws i)) MeasurableY IndependentY t
  intro i _
  have Marginal : (IndependentOneStepMeasure PositiveLength InitialState).map
      (fun Draws => Potential (Draws i)) =
      (Step PositiveLength InitialState).toMeasure.map Potential := by
    have MeasurablePotential : Measurable (Potential (n := n)) := measurable_of_finite _
    have MeasurableCoordinate : Measurable (fun Draws : ℕ → Bits n => Draws i) :=
      measurable_pi_apply i
    change Measure.map ((Potential (n := n)) ∘ (fun Draws : ℕ → Bits n => Draws i))
      (Measure.infinitePi (fun _ : ℕ => (Step PositiveLength InitialState).toMeasure)) = _
    rw [← Measure.map_map MeasurablePotential MeasurableCoordinate,
      Measure.infinitePi_map_eval]
  rw [Marginal]
  filter_upwards [LastBitStates PositiveLength InitialState OneZero i] with Path Legal
  exact LastBitStepPotentialDominated PositiveLength InitialState (Path i) Legal

end
end ECTheoryLib.Analysis.RLSOnOneMax
