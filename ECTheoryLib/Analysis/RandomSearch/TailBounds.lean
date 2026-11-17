import ECTheoryLib.Analysis.RandomSearch.PathPotential
import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicativeTail

/-!
# First-hitting upper tails for actual independent random search

Complete-history drift follows from the sampling kernel. The general-time
bound allows success probability zero; the ceiling bound requires it positive.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Exponential upper tail for the real, continuously resampling algorithm.
Its target can be left after the first visit. -/
theorem FixedRuntimeTailAtTime (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState) (t : ℕ) :
    PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)
      {Path | (t : WithTop ℕ)<FirstHittingTime Goal Path} ≤
        ENNReal.ofReal (Real.exp (-Samples.toMeasure.real {y | Goal y}*(t : ℝ))) := by
  let μ := PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  have Bound := MultiplicativeDriftTailAtTimeNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted (Potential Goal))
    {0,1} 1 (Samples.toMeasure.real {y | Goal y}) (by norm_num) (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      exact InS.imp id (fun Equal => Equal.ge))
    (fun j Path => PotentialValues Goal (Path j)) (by
      intro j
      filter_upwards [PathConditionalSuccessDrift Samples (PMF.pure InitialState) Goal j] with Path Conditional
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        exact Active (by simp [X,Potential,Reached])
      rw [Conditional NotGoal]
      simp [X,Potential,NotGoal]) t
  have Mean : ExpectedValue μ (X 0)=1 := by
    unfold ExpectedValue
    rw [integral_congr_ae (InitialFailurePotential Samples Goal InitialState Away),integral_const,probReal_univ,one_smul]
  have Times : ZeroHittingTime X=FirstHittingTime Goal := funext (FailurePotentialHittingTime Goal)
  rw [Times,Mean,mul_one,div_one] at Bound
  exact Bound

theorem FixedRuntimeUpperTail (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (InitialState : State) (Away : ¬Goal InitialState)
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) (r : ℝ) (NonnegativeR : 0≤r) :
    PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)
      {Path | (⌈r/Samples.toMeasure.real {y | Goal y}⌉₊ : WithTop ℕ)<FirstHittingTime Goal Path} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  let μ := PathMeasure (IndependentRandomSearchStep Samples) (PMF.pure InitialState)
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => Potential Goal (Path j)
  have Bound := MultiplicativeDriftUpperTailNonabsorbing μ X
    (Filtration.piLE (X := fun _ : ℕ => State)) (CountablePathPotentialAdapted (Potential Goal))
    {0,1} 1 (Samples.toMeasure.real {y | Goal y}) 1 (by simp) (by norm_num) (by
      intro s InS
      simp only [Finset.mem_insert,Finset.mem_singleton] at InS
      exact InS.imp id (fun Equal => Equal.ge))
    (fun j Path => PotentialValues Goal (Path j)) PositiveSuccess (by
      intro j
      filter_upwards [PathConditionalSuccessDrift Samples (PMF.pure InitialState) Goal j] with Path Conditional
      intro Active
      have NotGoal : ¬Goal (Path j) := by
        intro Reached
        exact Active (by simp [X,Potential,Reached])
      rw [Conditional NotGoal]
      simp [X,Potential,NotGoal]) (InitialFailurePotential Samples Goal InitialState Away)
    (by norm_num) r NonnegativeR
  simp only [div_self (one_ne_zero : (1 : ℝ)≠0),Real.log_one,add_zero] at Bound
  have Times : ZeroHittingTime X=FirstHittingTime Goal := funext (FailurePotentialHittingTime Goal)
  rwa [Times] at Bound

end
end ECTheoryLib.Analysis.RandomSearch
