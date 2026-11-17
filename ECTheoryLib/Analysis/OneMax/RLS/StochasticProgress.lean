import ECTheoryLib.Analysis.OneMax.RLS.Drift
import ECTheoryLib.Probability.Processes.Process
import ECTheoryLib.Probability.StochasticOrder.StochasticDomination
import ECTheoryLib.Probability.StochasticOrder.StochasticExpectation
import ECTheoryLib.Probability.StochasticOrder.StochasticMonotone
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Evolution of the actual RLS potential

Elitist RLS on OneMax never increases its zero-count potential. We lift this
property from the actual transition kernel to its trajectory law, derive
the exact mean contraction from one-step drift, and apply
Doerr's Lemma 1.8.5(a). Initialization may be any PMF, including a correlated
distribution on the bits. These are comparisons across times of the same
algorithm; they do not compare runtimes of two different algorithms.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax

open MeasureTheory ECTheoryLib.Probability

noncomputable section

/-- The actual one-step kernel cannot increase the zero-count potential. -/
theorem StepPotentialNonincreasing {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential y ≤ Potential x := by
  have InRange :
      ∀ᵐ y ∂((UniformBitIndex n PositiveLength).toMeasure.map (Update x)),
        y ∈ Set.range (Update x) := by
    apply ae_map_mem_range
    exact (Set.to_countable _).measurableSet
  rw [PMF.toMeasure_map (Update x) (UniformBitIndex n PositiveLength)
    (measurable_of_finite _)] at InRange
  rw [Step, RLSStepEqUniformUpdate]
  filter_upwards [InRange] with y PossibleUpdate
  obtain ⟨i, UpdateEq⟩ := PossibleUpdate
  rw [← UpdateEq]
  have Decrease := PotentialDecrease x i
  have NonnegativeDecrease : (0 : ℝ) ≤ if x i then 0 else 1 := by
    cases x i
    · norm_num
    · norm_num
  linarith

/-- Reachable potentials never exceed the actual fixed initial zero count. -/
theorem PathPotentialLeInitial {n : ℕ} (PositiveLength : 0 < n) (InitialState : Bits n) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure (Step PositiveLength) (PMF.pure InitialState),
      Potential (Path t) ≤ Potential InitialState := by
  have Initially : ∀ᵐ x ∂(PMF.pure InitialState).toMeasure, Potential x ≤ Potential InitialState := by
    rw [PMF.toMeasure_pure]
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr le_rfl
  have Preserved (x : Bits n) : ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      Potential x ≤ Potential InitialState → Potential y ≤ Potential InitialState := by
    filter_upwards [StepPotentialNonincreasing PositiveLength x] with y Decreases
    intro Before
    exact Decreases.trans Before
  exact PathMeasurePreservesProperty (Step PositiveLength) (PMF.pure InitialState)
    (fun x => Potential x ≤ Potential InitialState) Initially Preserved t

/-- Exact potential mean at every time, for any initial PMF on the actual RLS path law. -/
theorem ExpectedPotentialExact (n : ℕ) (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    (∫ Path, Potential (Path t) ∂PathMeasure (Step PositiveLength) Initial) =
      (1 - 1 / (n : ℝ)) ^ t * (∫ x, Potential x ∂Initial.toMeasure) := by
  have LocalMean (x : Bits n) :
      (∫ y, Potential y ∂(Step PositiveLength x).toMeasure) =
        (1 - 1 / (n : ℝ)) * Potential x := by
    have Drift := OneStepDrift PositiveLength x
    rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const,
      probReal_univ, one_smul] at Drift
    calc
      (∫ y, Potential y ∂(Step PositiveLength x).toMeasure) =
          Potential x - Potential x / (n : ℝ) := by linarith
      _ = (1 - 1 / (n : ℝ)) * Potential x := by ring
  induction t with
  | zero =>
      rw [pow_zero, one_mul]
      exact PathMeasureInitialIntegral (Step PositiveLength) Initial Potential
  | succ t InductionHypothesis =>
      rw [PathMeasureTransitionIntegral (Step PositiveLength) Initial t (fun _ y => Potential y)]
      simp_rw [LocalMean]
      rw [integral_const_mul, InductionHypothesis, pow_succ]
      ring

/-- Successive potentials on the actual random trajectory are ordered in law. -/
theorem PotentialLawStochasticStep {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (t : ℕ) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) Initial).map
        (fun Path => Potential (Path (t + 1))))
      ((PathMeasure (Step PositiveLength) Initial).map
        (fun Path => Potential (Path t))) := by
  have MeasurablePotential (s : ℕ) :
      Measurable (fun Path : ℕ → Bits n => Potential (Path s)) := by
    exact (measurable_of_finite Potential).comp (measurable_pi_apply s)
  apply StochasticDominatedOfAELe _ _ _
    (MeasurablePotential (t + 1)).aemeasurable (MeasurablePotential t).aemeasurable
  exact PathMeasureFollowsTransition (Step PositiveLength) Initial
    (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) t

/-- For any two iteration counts, the later potential is stochastically smaller. -/
theorem PotentialLawStochasticAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (s t : ℕ) (Earlier : s ≤ t) :
    StochasticDominated
      ((PathMeasure (Step PositiveLength) Initial).map
        (fun Path => Potential (Path t)))
      ((PathMeasure (Step PositiveLength) Initial).map
        (fun Path => Potential (Path s))) := by
  induction t, Earlier using Nat.le_induction with
  | base => exact StochasticDominatedRefl _
  | succ t _ InductionHypothesis =>
      exact StochasticDominatedTrans
        (PotentialLawStochasticStep PositiveLength Initial t) InductionHypothesis

/-- The probability of exceeding any real potential threshold cannot increase.
This includes atomic thresholds and an arbitrary random initial state. -/
theorem PotentialStrictTailAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (s t : ℕ) (Earlier : s ≤ t) (a : ℝ) :
    (PathMeasure (Step PositiveLength) Initial) {Path | a < Potential (Path t)} ≤
      (PathMeasure (Step PositiveLength) Initial) {Path | a < Potential (Path s)} := by
  have MeasurablePotential (k : ℕ) :
      Measurable (fun Path : ℕ → Bits n => Potential (Path k)) := by
    exact (measurable_of_finite Potential).comp (measurable_pi_apply k)
  have ProbabilityLaw (k : ℕ) :
      IsProbabilityMeasure ((PathMeasure (Step PositiveLength) Initial).map
        (fun Path => Potential (Path k))) := by
    exact Measure.isProbabilityMeasure_map (MeasurablePotential k).aemeasurable
  have Bound := (StochasticDominatedIffStrictTail _ _).mp
    (PotentialLawStochasticAntitone PositiveLength Initial s t Earlier) a
  rw [Measure.map_apply (MeasurablePotential t) measurableSet_Ioi,
    Measure.map_apply (MeasurablePotential s) measurableSet_Ioi] at Bound
  exact Bound

/-- Expected potential is nonincreasing, derived from distribution order.
Finite state supplies integrability; callers need not assume finite means. -/
theorem ExpectedPotentialAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (s t : ℕ) (Earlier : s ≤ t) :
    (∫ Path, Potential (Path t) ∂PathMeasure (Step PositiveLength) Initial) ≤
      ∫ Path, Potential (Path s) ∂PathMeasure (Step PositiveLength) Initial := by
  apply StochasticDominatedExpectationLE _ _ _ _
    (PathMeasureCoordinateIntegrable (Step PositiveLength) Initial Potential t)
    (PathMeasureCoordinateIntegrable (Step PositiveLength) Initial Potential s)
  exact PotentialLawStochasticAntitone PositiveLength Initial s t Earlier

/-- Any nondecreasing real cost of the potential has nonincreasing expectation.
Finite state ensures integrability even for discontinuous or unbounded costs. -/
theorem ExpectedMonotonePotentialAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (s t : ℕ) (Earlier : s ≤ t)
    (f : ℝ → ℝ) (Increasing : Monotone f) :
    (∫ Path, f (Potential (Path t)) ∂PathMeasure (Step PositiveLength) Initial) ≤
      ∫ Path, f (Potential (Path s)) ∂PathMeasure (Step PositiveLength) Initial := by
  have MeasurablePotential (k : ℕ) :
      Measurable (fun Path : ℕ → Bits n => Potential (Path k)) := by
    exact (measurable_of_finite Potential).comp (measurable_pi_apply k)
  exact StochasticDominatedMonotoneExpectationLE _ _ _ _
    (MeasurablePotential t).aemeasurable (MeasurablePotential s).aemeasurable
    (PotentialLawStochasticAntitone PositiveLength Initial s t Earlier) f Increasing
    (PathMeasureCoordinateIntegrable (Step PositiveLength) Initial (fun x => f (Potential x)) t)
    (PathMeasureCoordinateIntegrable (Step PositiveLength) Initial (fun x => f (Potential x)) s)

end
end ECTheoryLib.Analysis.RLSOnOneMax
