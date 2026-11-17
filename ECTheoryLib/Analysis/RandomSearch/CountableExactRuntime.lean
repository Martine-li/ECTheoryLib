import ECTheoryLib.Analysis.RandomSearch.CountableRuntime
import ECTheoryLib.Tools.Drift.NonabsorbingVariableLower

/-!
# Exact runtime of countable independent random search

Arbitrary initialization contributes its failure mass. Positive one-step
success uses matching drift bounds; zero success retains infinite hitting
times directly from the actual path law.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem CountableRuntimeLowerBound (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ENNReal.ofReal (Initial.toMeasure.real {x | ¬Goal x}/Samples.toMeasure.real {y | Goal y}) ≤
      ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal Initial := by
  let q := Samples.toMeasure.real {y | Goal y}
  let Step := IndependentRandomSearchStep Samples
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => Potential Goal (Path t)
  have Lower : ∀ s∈({0,1} : Finset ℝ), s=0 ∨ 1≤s := by
    intro s InS
    simp only [Finset.mem_insert,Finset.mem_singleton] at InS
    exact InS.imp id (fun Equal => Equal.ge)
  have Bound := VariableDriftLowerBoundNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted (Potential Goal))
    {0,1} 1 (fun _ => q) 1 (by simp) (by norm_num) Lower
    (fun _ Path => PotentialValues Goal (Path _)) (by
      intro t
      apply ae_of_all
      intro Path Active
      have Away : ¬Goal (Path t) := by simpa [X,Potential] using Active
      by_cases Next : Goal (Path (t+1)) <;> simp [X,Potential,Away,Next])
    (fun _ _ => PositiveSuccess) (fun _ _ _ _ _ => le_rfl) le_rfl (by
      intro t
      exact ae_of_all _ (fun _ _ => by simp [ne_of_gt PositiveSuccess,q])) (by
      intro t
      filter_upwards [PathMeasureFinitePotentialConditionalDrift Step Initial (Potential Goal) {0,1}
        (PotentialValues Goal) t] with Path Equal
      intro Active
      have Away : ¬Goal (Path t) := by simpa [X,Potential] using Active
      rw [Equal,CountableOneStepDrift Samples Goal (Path t) Away])
  have Mean : ExpectedValue μ (fun Path => VariableDriftPotential 1 (fun _ => q) (X 0 Path))=
      Initial.toMeasure.real {x | ¬Goal x}/q := by
    unfold ExpectedValue
    change (∫ Path, VariableDriftPotential 1 (fun _ => q) (Potential Goal (Path 0)) ∂PathMeasure Step Initial)=_
    rw [PathMeasureInitialIntegral Step Initial (fun x => VariableDriftPotential 1 (fun _ => q) (Potential Goal x))]
    have Equal : (fun x => VariableDriftPotential 1 (fun _ => q) (Potential Goal x)) =
        (fun x => ({x | ¬Goal x}).indicator (fun _ => (1 : ℝ)) x/q) := by
      funext x
      by_cases Reached : Goal x <;> simp [VariableDriftPotential,Potential,Reached]
    rw [Equal,integral_div,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rw [Mean,div_one] at Bound
  rw [ExpectedHittingTimeEqExpectedZero Step Initial (Potential Goal) Goal (fun x => by simp [Potential])]
  exact Bound

/-- Exact countable-space runtime with arbitrary initialization, obtained by
matching variable lower and multiplicative upper bounds on the same path law. -/
theorem CountableRuntimeExact (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal Initial =
      ENNReal.ofReal (Initial.toMeasure.real {x | ¬Goal x}/Samples.toMeasure.real {y | Goal y}) :=
  le_antisymm (CountableRuntimeUpperBound Samples Initial Goal PositiveSuccess)
    (CountableRuntimeLowerBound Samples Initial Goal PositiveSuccess)

theorem CountableFixedRuntimeExact (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) =
      ENNReal.ofReal (1/Samples.toMeasure.real {y | Goal y}) := by
  have Equal := CountableRuntimeExact Samples (PMF.pure InitialState) Goal PositiveSuccess
  have InitialFailure : (PMF.pure InitialState).toMeasure.real {x | ¬Goal x}=1 := by
    simp [Measure.real,PMF.toMeasure_pure,Away]
  rwa [InitialFailure] at Equal

end

noncomputable section
theorem GeometricSampleRuntimeExact (p : I) (Positive : 0<(p : ℝ)) (InitialState : ℕ)
    (Away : InitialState≠0) :
    ExpectedHittingTime (IndependentRandomSearchStep (geometricMeasure p).toPMF)
      (fun x => x=0) (PMF.pure InitialState) = ENNReal.ofReal (1/(p : ℝ)) := by
  have Nonzero : p≠0 := by
    intro Equal
    have Zero : (p : ℝ)=0 := congrArg (fun q : I => (q : ℝ)) Equal
    linarith
  have Probability : (geometricMeasure p).toPMF.toMeasure.real {y | y=0}=(p : ℝ) := by
    rw [Measure.toPMF_toMeasure]
    change (geometricMeasure p).real {0}=(p : ℝ)
    rw [geometricMeasure_real_singleton Nonzero]
    simp
  have Equal := CountableFixedRuntimeExact (geometricMeasure p).toPMF (fun x => x=0)
    InitialState Away (by rwa [Probability])
  rwa [Probability] at Equal

end
end ECTheoryLib.Analysis.RandomSearch

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Zero success mass makes every positive-time candidate fail. Initial success
still has first-hit time zero, even though the subsequent samples all fail. -/
theorem ZeroSuccessHittingTime (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (ZeroSuccess : Samples.toMeasure.real {y | Goal y}=0) :
    ∀ᵐ Path ∂PathMeasure (IndependentRandomSearchStep Samples) Initial,
      FirstHittingTime Goal Path=if Goal (Path 0) then 0 else ⊤ := by
  have NeverSample : ∀ᵐ y ∂Samples.toMeasure, ¬Goal y := by
    apply ae_iff.mpr
    simpa only [not_not] using (measureReal_eq_zero_iff).mp ZeroSuccess
  have PositiveTimes : ∀ᵐ Path ∂PathMeasure (IndependentRandomSearchStep Samples) Initial,
      ∀ t, ¬Goal (Path (t+1)) := by
    apply ae_all_iff.mpr
    intro t
    exact PathMeasureFollowsTransition (IndependentRandomSearchStep Samples) Initial
      (fun _ y => ¬Goal y) (fun _ => NeverSample) t
  filter_upwards [PositiveTimes] with Path NotGoal
  by_cases InitialGoal : Goal (Path 0)
  · rw [if_pos InitialGoal]
    exact (FirstHittingTimeEqZeroIff Goal Path).mpr InitialGoal
  · rw [if_neg InitialGoal]
    apply (FirstHittingTimeEqTopIff Goal Path).mpr
    intro t
    cases t with
    | zero => exact InitialGoal
    | succ t => exact NotGoal t

/-- The zero-success boundary retains positive-mass nontermination. In ENNReal,
top times zero is zero, so almost-sure initial success is handled correctly. -/
theorem ZeroSuccessRuntimeExact (Samples Initial : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (ZeroSuccess : Samples.toMeasure.real {y | Goal y}=0) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal Initial =
      (⊤ : ENNReal)*Initial.toMeasure {x | ¬Goal x} := by
  let Step := IndependentRandomSearchStep Samples
  let μ := PathMeasure Step Initial
  let Failure : Set State := {x | ¬Goal x}
  have MeasurableFailure : MeasurableSet Failure := (Set.to_countable _).measurableSet
  have Value : FirstHittingTimeValue Goal =ᵐ[μ]
      ((fun Path : ℕ → State => Path 0) ⁻¹' Failure).indicator (fun _ => (⊤ : ENNReal)) := by
    filter_upwards [ZeroSuccessHittingTime Samples Initial Goal ZeroSuccess] with Path Time
    unfold FirstHittingTimeValue
    rw [Time]
    by_cases Reached : Goal (Path 0)
    · simp [Failure,Reached]
      exact ENat.toENNReal_zero
    · simp [Failure,Reached]
      rfl
  unfold ExpectedHittingTime
  rw [lintegral_congr_ae Value,lintegral_indicator_const (MeasurableFailure.preimage (measurable_pi_apply 0))]
  rw [← Measure.map_apply (measurable_pi_apply 0) MeasurableFailure,PathMeasureInitial]

end
end ECTheoryLib.Analysis.RandomSearch
