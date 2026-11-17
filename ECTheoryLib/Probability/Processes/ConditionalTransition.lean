import ECTheoryLib.Probability.Processes.PathMarginal

/-!
# Conditional one-step expectation on a current-state event

The actual finite-state trajectory transition kernel is retained when averaging
on a current-state event. The proof reuses the unconditional transition integral,
the marginal-law bridge, and Mathlib restriction and scaling of measures.
The identity includes null events as zero measures; interpreting conditioning
as a probability law still requires positive event mass.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Conditioning on a current-state event preserves the actual transition kernel.
Both sides are zero for a null conditioning event; positive mass is only needed
when interpreting the conditional measures as probability measures. -/
theorem PathMeasureConditionalTransitionIntegral (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (A : Set State) (f : State → State → ℝ) :
    (∫ Path, f (Path t) (Path (t+1)) ∂cond (PathMeasure Step Initial) {Path | Path t ∈ A}) =
      ∫ x, (∫ y, f x y ∂(Step x).toMeasure) ∂cond (Evolve Step Initial t).toMeasure A := by
  classical
  have AMeasurable : MeasurableSet A := (Set.to_countable _).measurableSet
  have EventMeasurable : MeasurableSet {Path : ℕ → State | Path t ∈ A} :=
    AMeasurable.preimage (measurable_pi_apply t)
  let G : State → State → ℝ := fun x y => if x ∈ A then f x y else 0
  have RestrictedIntegral :
      (∫ Path in {Path : ℕ → State | Path t ∈ A}, f (Path t) (Path (t+1)) ∂PathMeasure Step Initial) =
        ∫ x in A, (∫ y, f x y ∂(Step x).toMeasure) ∂(Evolve Step Initial t).toMeasure := by
    rw [← integral_indicator EventMeasurable, ← integral_indicator AMeasurable]
    change (∫ Path, G (Path t) (Path (t+1)) ∂PathMeasure Step Initial) = _
    rw [PathMeasureTransitionIntegral Step Initial t G,
      PathMeasureMarginalIntegral Step Initial t (fun x => ∫ y, G x y ∂(Step x).toMeasure)]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases InA : x ∈ A
    · simp only [G, if_pos InA, Set.indicator_of_mem InA]
    · simp only [G, if_neg InA, integral_zero, Set.indicator_of_notMem InA]
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    PathMeasureCoordinateEvent Step Initial t A, RestrictedIntegral]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A pointwise bound on actual kernel expectations also bounds the trajectory
expectation conditional on a positive current-state event. -/
theorem PathMeasureConditionalTransitionIntegralUpperBound
    (Step : Transition State) (Initial : PMF State) (t : ℕ) (A : Set State)
    (f : State → State → ℝ) (c : ℝ)
    (Positive : 0 < PathMeasure Step Initial {Path | Path t ∈ A})
    (Local : ∀ x ∈ A, (∫ y, f x y ∂(Step x).toMeasure) ≤ c) :
    (∫ Path, f (Path t) (Path (t+1)) ∂cond (PathMeasure Step Initial) {Path | Path t ∈ A}) ≤ c := by
  rw [PathMeasureConditionalTransitionIntegral]
  have MarginalPositive : 0 < (Evolve Step Initial t).toMeasure A := by
    rw [PathMeasureCoordinateEvent] at Positive
    exact Positive
  let ν := cond (Evolve Step Initial t).toMeasure A
  have Probability : IsProbabilityMeasure ν := cond_isProbabilityMeasure MarginalPositive.ne'
  have InA : ∀ᵐ x ∂ν, x ∈ A := ae_cond_mem (Set.to_countable A).measurableSet
  have Bound := integral_mono_ae (Integrable.of_finite (μ := ν)
    (f := fun x => ∫ y, f x y ∂(Step x).toMeasure)) (integrable_const c) (by
      filter_upwards [InA] with x Member
      exact Local x Member)
  rw [integral_const, probReal_univ, one_smul] at Bound
  exact Bound

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A bound on actual one-step event probabilities persists when conditioning
the trajectory on any positive current-state event. -/
theorem PathMeasureConditionalTransitionProbabilityUpperBound
    (Step : Transition State) (Initial : PMF State) (t : ℕ) (A : Set State)
    (R : State → State → Prop) (c : ℝ) (NonnegativeC : 0≤c)
    (Positive : 0<PathMeasure Step Initial {Path | Path t∈A})
    (Local : ∀ x∈A, (Step x).toMeasure {y | R x y} ≤ ENNReal.ofReal c) :
    (cond (PathMeasure Step Initial) {Path | Path t∈A}) {Path | R (Path t) (Path (t+1))} ≤
      ENNReal.ofReal c := by
  classical
  have EventMeasurable : MeasurableSet {Path : ℕ → State | R (Path t) (Path (t+1))} := by
    apply MeasurableSet.preimage (f := fun Path : ℕ → State => (Path t,Path (t+1)))
      (Set.to_countable {p : State×State | R p.1 p.2}).measurableSet
    exact (measurable_pi_apply t).prodMk (measurable_pi_apply (t+1))
  have Bound := PathMeasureConditionalTransitionIntegralUpperBound Step Initial t A
    (fun x y => ({z | R x z}).indicator (fun _ => (1 : ℝ)) y) c Positive (by
      intro x Member
      rw [integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul, mul_one]
      apply (ENNReal.ofReal_le_ofReal_iff NonnegativeC).mp
      rw [ofReal_measureReal]
      exact Local x Member)
  change (∫ Path, ({Path | R (Path t) (Path (t+1))}).indicator (fun _ => (1 : ℝ)) Path
    ∂cond (PathMeasure Step Initial) {Path | Path t∈A}) ≤ c at Bound
  rw [integral_indicator_const _ EventMeasurable, smul_eq_mul, mul_one] at Bound
  have ConditionalProbability : IsProbabilityMeasure
      (cond (PathMeasure Step Initial) {Path | Path t∈A}) := cond_isProbabilityMeasure Positive.ne'
  have BoundENN := ENNReal.ofReal_le_ofReal Bound
  rw [ofReal_measureReal] at BoundENN
  exact BoundENN

end
end ECTheoryLib.Probability
