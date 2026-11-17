import ECTheoryLib.Analysis.RandomSearch.PathPotential
import ECTheoryLib.Tools.Drift.NonabsorbingAdditive
import ECTheoryLib.Probability.Processes.PathDrift

/-!
# Exact first-hitting expectation for independent random search

For a fixed unsuccessful initial state and positive one-step success
probability q, the matching additive drift bounds give expectation 1/q.
Time counts transitions; the initial state is at time zero.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem FixedRuntimeLowerBound (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ENNReal.ofReal (1/Samples.toMeasure.real {y | Goal y}) ≤
      ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) := by
  let μ := PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  have Bound := AdditiveDriftLowerBoundNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted (Potential Goal))
    {0,1} (Samples.toMeasure.real {y | Goal y}) (by simp) (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      rcases InS with Zero | One
      · rw [Zero]
      · rw [One]; norm_num)
    (fun j Path => PotentialValues Goal (Path j)) PositiveSuccess (by
      intro j
      filter_upwards [PathConditionalSuccessDrift Samples (PMF.pure InitialState) Goal j] with Path Conditional
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        exact Active (by simp [X,Potential,Reached])
      rw [Conditional NotGoal])
  have Mean : ExpectedValue μ (X 0)=1 := by
    change (∫ Path, Potential Goal (Path 0) ∂μ)=1
    rw [PathMeasurePureInitialIntegral]
    simp [Potential,Away]
  have Expected : ExpectedZeroHittingTime μ X=
      ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) := by
    apply lintegral_congr
    intro Path
    rw [FailurePotentialHittingTime]
    rfl
  rwa [Mean,Expected] at Bound

/-- Match the two drift bounds on the actual nonabsorbing sampling process.
No geometric law or finite expected runtime is supplied as a premise. -/
theorem FixedRuntimeExact (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) =
      ENNReal.ofReal (1/Samples.toMeasure.real {y | Goal y}) :=
  le_antisymm (FixedRuntimeUpperBound Samples Goal InitialState Away PositiveSuccess)
    (FixedRuntimeLowerBound Samples Goal InitialState Away PositiveSuccess)

theorem UniformSingletonRuntimeExact [Nonempty State] (Target InitialState : State) (Away : InitialState≠Target) :
    ExpectedHittingTime (IndependentRandomSearchStep (PMF.uniformOfFintype State))
      (fun x => x=Target) (PMF.pure InitialState) = ENNReal.ofReal (Fintype.card State : ℝ) := by
  classical
  have Probability : (PMF.uniformOfFintype State).toMeasure.real {y | y=Target} =
      1/(Fintype.card State : ℝ) := by
    change ((PMF.uniformOfFintype State).toMeasure {Target}).toReal=1/(Fintype.card State : ℝ)
    rw [(PMF.uniformOfFintype State).toMeasure_apply_singleton Target (measurableSet_singleton _),
      PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,one_div]
  have PositiveCard : (0 : ℝ)<Fintype.card State := Nat.cast_pos.mpr Fintype.card_pos
  have Equal := FixedRuntimeExact (PMF.uniformOfFintype State) (fun x => x=Target)
    InitialState Away (by rw [Probability]; positivity)
  rwa [Probability,one_div_one_div] at Equal

theorem UniformBitStringRuntimeExact (n : ℕ) (InitialState : Bits n) (Away : InitialState≠AllOnes n) :
    ExpectedHittingTime (IndependentRandomSearchStep (PMF.uniformOfFintype (Bits n)))
      (fun x => x=AllOnes n) (PMF.pure InitialState) = ENNReal.ofReal ((2 : ℝ)^n) := by
  have Equal := UniformSingletonRuntimeExact (AllOnes n) InitialState Away
  simpa only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using Equal

end
end ECTheoryLib.Analysis.RandomSearch
