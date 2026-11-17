import ECTheoryLib.Algorithms.RandomSearch
import ECTheoryLib.Tools.Drift.NonabsorbingAdditive
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Probability.HittingTimes.Expectation
import ECTheoryLib.SearchSpaces.BitString
import Mathlib.Probability.Distributions.Uniform

/-!
# Expected first-hitting bounds for actual independent random search

Use the failure indicator and the genuine complete-history conditional law.
Time counts transitions from a specified initially unsuccessful state.
The uniform finite-space bound specializes to 2^n on binary strings.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*}

def Potential (Goal : State → Prop) [DecidablePred Goal] (x : State) : ℝ := if Goal x then 0 else 1

theorem PotentialValues (Goal : State → Prop) [DecidablePred Goal] (x : State) :
    Potential Goal x∈({0,1} : Finset ℝ) := by
  by_cases Reached : Goal x <;> simp [Potential,Reached]

variable [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem OneStepDrift (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (x : State) (Away : ¬Goal x) :
    (∫ y, Potential Goal x-Potential Goal y ∂(IndependentRandomSearchStep Samples x).toMeasure)=
      Samples.toMeasure.real {y | Goal y} := by
  have Equal : (fun y => Potential Goal x-Potential Goal y)=({y | Goal y}).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases Reached : Goal y <;> simp [Potential,Away,Reached]
  rw [Equal,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rfl

/-- The algorithm keeps sampling after a hit. Apply nonabsorbing additive
drift to the actual path law, using the failure indicator as potential. -/
theorem FixedRuntimeUpperBound (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal (PMF.pure InitialState) ≤
      ENNReal.ofReal (1/Samples.toMeasure.real {y | Goal y}) := by
  let Step := IndependentRandomSearchStep Samples
  let μ := PathMeasure Step (PMF.pure InitialState)
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => State)
  have AdaptedX : Adapted F X := CountablePathPotentialAdapted (Potential Goal)
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) {0,1} AdaptedX.measurable
      (ae_of_all _ (fun Path => PotentialValues Goal (Path j)))
  have Bound := AdditiveDriftUpperBoundNonabsorbing μ X F AdaptedX {0,1}
    (Samples.toMeasure.real {y | Goal y}) (by simp) (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      rcases InS with Zero | One
      · rw [Zero]
      · rw [One]; norm_num)
    (fun j Path => PotentialValues Goal (Path j)) PositiveSuccess (by
      intro j
      have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step (PMF.pure InitialState) j
        (fun x y => Potential Goal x-Potential Goal y) ((IntegrableX j).sub (IntegrableX (j+1)))
      filter_upwards [Conditional] with Path Equal
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        apply Active
        simp [X,Potential,Reached]
      rw [Equal,OneStepDrift Samples Goal (Path j) NotGoal])
  have Initial : ∀ᵐ Path ∂μ, Path 0=InitialState := by
    have Mapped : ∀ᵐ x ∂(PathMeasure Step (PMF.pure InitialState)).map (fun Path : ℕ → State => Path 0), x=InitialState := by
      rw [PathMeasureInitial,PMF.toMeasure_pure]
      exact ae_eq_dirac (fun x : State => x)
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable Mapped
  have InitialMean : ExpectedValue μ (X 0)=1 := by
    unfold ExpectedValue
    have Equal : X 0 =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      filter_upwards [Initial] with Path Equal
      simp [X,Equal,Potential,Away]
    rw [integral_congr_ae Equal,integral_const,probReal_univ,one_smul]
  have Times (Path : ℕ → State) : ZeroHittingTime X Path=FirstHittingTime Goal Path := by
    apply WithTop.eq_of_forall_le_coe_iff
    intro t
    have Left := FirstHittingTimeLeIff (fun s : ℝ => s=0) (fun j => X j Path) t
    have Right := FirstHittingTimeLeIff Goal Path t
    refine Left.trans (Iff.trans ?_ Right.symm)
    simp [X,Potential]
  have Expected : ExpectedZeroHittingTime μ X=
      ExpectedHittingTime Step Goal (PMF.pure InitialState) := by
    apply lintegral_congr
    intro Path
    rw [Times]
    rfl
  rwa [InitialMean,Expected] at Bound

/-- Uniform independent search on a finite space finds any fixed target
within the cardinality bound in expected transitions from a different state. -/
theorem UniformSingletonRuntimeUpperBound [Nonempty State] (Target InitialState : State) (Away : InitialState≠Target) :
    ExpectedHittingTime (IndependentRandomSearchStep (PMF.uniformOfFintype State))
      (fun x => x=Target) (PMF.pure InitialState) ≤ ENNReal.ofReal (Fintype.card State : ℝ) := by
  classical
  have Probability : (PMF.uniformOfFintype State).toMeasure.real {y | y=Target} =
      1/(Fintype.card State : ℝ) := by
    change ((PMF.uniformOfFintype State).toMeasure {Target}).toReal=1/(Fintype.card State : ℝ)
    rw [(PMF.uniformOfFintype State).toMeasure_apply_singleton Target (measurableSet_singleton _),PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv,ENNReal.toReal_natCast,one_div]
  have PositiveCard : (0 : ℝ)<Fintype.card State := Nat.cast_pos.mpr Fintype.card_pos
  have Bound := FixedRuntimeUpperBound (PMF.uniformOfFintype State) (fun x => x=Target)
    InitialState Away (by rw [Probability]; positivity)
  rwa [Probability,one_div_one_div] at Bound

theorem UniformBitStringRuntimeUpperBound (n : ℕ) (InitialState : Bits n) (Away : InitialState≠AllOnes n) :
    ExpectedHittingTime (IndependentRandomSearchStep (PMF.uniformOfFintype (Bits n)))
      (fun x => x=AllOnes n) (PMF.pure InitialState) ≤ ENNReal.ofReal ((2 : ℝ)^n) := by
  have Bound := UniformSingletonRuntimeUpperBound (AllOnes n) InitialState Away
  simpa only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using Bound

end
end ECTheoryLib.Analysis.RandomSearch
