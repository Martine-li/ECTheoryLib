import ECTheoryLib.Analysis.RandomSearch.RuntimeBounds
import ECTheoryLib.Tools.Runtime.NonabsorbingFiniteRange
import Mathlib.Probability.Distributions.Geometric

/-!
# Random search on countable spaces with arbitrary initialization

The upper bound retains the initial failure probability. A geometric
candidate distribution gives a genuinely infinite-support example.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift ECTheoryLib.Tools.Runtime
open scoped unitInterval
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem CountableOneStepDrift (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (x : State) (Away : ¬Goal x) :
    (∫ y, Potential Goal x-Potential Goal y ∂(IndependentRandomSearchStep Samples x).toMeasure)=
      Samples.toMeasure.real {y | Goal y} := by
  have Equal : (fun y => Potential Goal x-Potential Goal y)=({y | Goal y}).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases Reached : Goal y <;> simp [Potential,Away,Reached]
  rw [Equal,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rfl

/-- Arbitrary countable search space and arbitrary initialization. The initial
failure probability is retained, so initially successful runs contribute zero. -/
theorem CountableRuntimeUpperBound (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal Initial ≤
      ENNReal.ofReal (Initial.toMeasure.real {x | ¬Goal x}/Samples.toMeasure.real {y | Goal y}) := by
  let q := Samples.toMeasure.real {y | Goal y}
  have Bound := MultiplicativeRuntimeUpperBoundOfFiniteRangeNonabsorbing
    (IndependentRandomSearchStep Samples) Initial (Potential Goal) Goal (fun _ => True) {0,1} 1 q
    (by simp) (by norm_num) (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      exact InS.imp id (fun Equal => Equal.ge))
    (PotentialValues Goal) (fun x => by simp [Potential])
    (ae_of_all _ (fun _ => True.intro)) (fun _ => ae_of_all _ (fun _ _ => True.intro))
    PositiveSuccess (by
      intro x _ Nonzero
      have Away : ¬Goal x := by simpa [Potential] using Nonzero
      rw [CountableOneStepDrift Samples Goal x Away]
      simp [Potential,Away,q])
  have Mean : (∫ x, MultiplicativeDriftPotential 1 q (Potential Goal x) ∂Initial.toMeasure)=
      Initial.toMeasure.real {x | ¬Goal x}/q := by
    have Equal : (fun x => MultiplicativeDriftPotential 1 q (Potential Goal x)) =
        (fun x => ({x | ¬Goal x}).indicator (fun _ => (1 : ℝ)) x/q) := by
      funext x
      by_cases Reached : Goal x <;> simp [MultiplicativeDriftPotential,Potential,Reached]
    rw [Equal,integral_div,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rwa [Mean] at Bound

theorem CountableFixedRuntimeUpperBound (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) ≤
      ENNReal.ofReal (1/Samples.toMeasure.real {y | Goal y}) := by
  have Bound := CountableRuntimeUpperBound Samples (PMF.pure InitialState) Goal PositiveSuccess
  have InitialFailure : (PMF.pure InitialState).toMeasure.real {x | ¬Goal x}=1 := by
    simp [Measure.real,PMF.toMeasure_pure,Away]
  rwa [InitialFailure] at Bound

end

noncomputable section
/-- A genuinely infinite-support sampling kernel: repeatedly draw a geometric
natural number and seek zero. The geometric law describes each candidate,
not an assumed distribution of the algorithm's hitting time. -/
theorem GeometricSampleRuntimeUpperBound (p : I) (Positive : 0<(p : ℝ)) (InitialState : ℕ)
    (Away : InitialState≠0) :
    ExpectedHittingTime (IndependentRandomSearchStep (geometricMeasure p).toPMF)
      (fun x => x=0) (PMF.pure InitialState) ≤ ENNReal.ofReal (1/(p : ℝ)) := by
  have Nonzero : p≠0 := by
    intro Equal
    have Zero : (p : ℝ)=0 := congrArg (fun q : I => (q : ℝ)) Equal
    linarith
  have Probability : (geometricMeasure p).toPMF.toMeasure.real {y | y=0}=(p : ℝ) := by
    rw [Measure.toPMF_toMeasure]
    change (geometricMeasure p).real {0}=(p : ℝ)
    rw [geometricMeasure_real_singleton Nonzero]
    simp
  have Bound := CountableFixedRuntimeUpperBound (geometricMeasure p).toPMF (fun x => x=0)
    InitialState Away (by rwa [Probability])
  rwa [Probability] at Bound

end
end ECTheoryLib.Analysis.RandomSearch
