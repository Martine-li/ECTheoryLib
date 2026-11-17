import ECTheoryLib.Probability.HittingTimes.Expectation

/-!
# Total expectation over a random initial state

The mixture identity follows directly from composition of the Ionescu–Tulcea
trajectory kernel with the initial distribution. Nonnegative trajectory functions
and runtimes may be infinite; no drift, absorption, or finite-expectation premise
is required. The runtime corollary supports reuse of fixed-initial-state results.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

variable {State : Type*} [MeasurableSpace State] [Countable State]
  [MeasurableSingletonClass State]

/-- A nonnegative measurable trajectory functional satisfies total expectation
over the initial PMF, with both sides interpreted as extended integrals. -/
theorem PathMeasureInitialMixture (Step : Transition State) (Initial : PMF State)
    (f : (Nat → State) → ENNReal) (MeasurableFunction : Measurable f) :
    (∫⁻ Path, f Path ∂PathMeasure Step Initial) =
      ∫⁻ x, (∫⁻ Path, f Path ∂PathMeasure Step (PMF.pure x)) ∂Initial.toMeasure := by
  unfold PathMeasure Kernel.trajMeasure
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) MeasurableFunction.aemeasurable]
  rw [lintegral_map (Measurable.lintegral_kernel MeasurableFunction)
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => State)).symm.measurable]
  apply lintegral_congr
  intro x
  rw [PMF.toMeasure_pure, Measure.map_dirac, Measure.dirac_bind (Kernel.measurable _)]

/-- Expected first hitting time is the initial-state mixture of fixed-state
expectations, including initially optimal states and nontermination. -/
theorem ExpectedHittingTimeInitialMixture (Step : Transition State) (Goal : State → Prop)
    (Initial : PMF State) :
    ExpectedHittingTime Step Goal Initial =
      ∫⁻ x, ExpectedHittingTime Step Goal (PMF.pure x) ∂Initial.toMeasure := by
  exact PathMeasureInitialMixture Step Initial _ (FirstHittingTimeValueMeasurable Goal)

end
end ECTheoryLib.Probability
