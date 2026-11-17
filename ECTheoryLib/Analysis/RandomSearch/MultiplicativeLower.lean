import ECTheoryLib.Analysis.RandomSearch.CountableRuntime
import ECTheoryLib.Tools.Runtime.NonabsorbingMultiplicativeLower

/-!
# A real nonabsorbing client of multiplicative lower drift

The closed relative-drop event is identified from the candidate law.
The conservative lower bound complements the separate exact runtime.
-/

namespace ECTheoryLib.Analysis.RandomSearch
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift ECTheoryLib.Tools.Runtime
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]

omit [Countable State] [MeasurableSingletonClass State] in
/-- The closed relative-drop event includes the successful transition.
Its probability follows from the actual candidate distribution. -/
theorem RelativeJumpProbability (Samples : PMF State) (Goal : State → Prop) [DecidablePred Goal]
    (x : State) (Away : ¬Goal x) (β : ℝ) (BetaPositive : 0<β) (BetaAtMostOne : β≤1) :
    (IndependentRandomSearchStep Samples x).toMeasure.real
      {y | β*Potential Goal x≤Potential Goal x-Potential Goal y}=Samples.toMeasure.real {y | Goal y} := by
  have Event : {y | β*Potential Goal x≤Potential Goal x-Potential Goal y}={y | Goal y} := by
    ext y
    by_cases Reached : Goal y
    · simp [Potential,Away,Reached,BetaAtMostOne]
    · simp [Potential,Away,Reached,not_le_of_gt BetaPositive]
  rw [Event]
  rfl

/-- A real nonabsorbing client of the rare-large-jump lower theorem. The
constant is conservative; the separate exact runtime remains available. -/
theorem CountableRuntimeMultiplicativeLowerBound (Samples Initial : PMF State)
    (Goal : State → Prop) [DecidablePred Goal]
    (PositiveSuccess : 0<Samples.toMeasure.real {y | Goal y}) :
    ENNReal.ofReal (Initial.toMeasure.real {x | ¬Goal x}/(6*Samples.toMeasure.real {y | Goal y}))≤
      ExpectedHittingTime (IndependentRandomSearchStep Samples) Goal Initial := by
  let q := Samples.toMeasure.real {y | Goal y}
  have Lower : ∀ s∈({0,1} : Finset ℝ), s=0 ∨ 1≤s := by
    intro s InS
    simp only [Finset.mem_insert,Finset.mem_singleton] at InS
    exact InS.imp id (fun Equal => Equal.ge)
  have Bound := MultiplicativeRuntimeLowerBoundOfFiniteRangeNonabsorbing
    (IndependentRandomSearchStep Samples) Initial (Potential Goal) Goal (fun _ => True)
    {0,1} 1 (1/2) (2*q) (by simp) (by norm_num) Lower (PotentialValues Goal)
    (fun x => by simp [Potential]) (ae_of_all _ (fun _ => True.intro))
    (fun _ => ae_of_all _ (fun _ _ => True.intro)) (by norm_num) (by norm_num)
    (mul_pos (by norm_num) PositiveSuccess) (by
      intro x
      apply ae_of_all
      intro y _ Nonzero
      have Away : ¬Goal x := by simpa [Potential] using Nonzero
      by_cases Reached : Goal y <;> simp [Potential,Away,Reached]) (by
      intro x _ Nonzero
      have Away : ¬Goal x := by simpa [Potential] using Nonzero
      rw [CountableOneStepDrift Samples Goal x Away]
      simp only [Potential,if_neg Away,mul_one]
      change q≤2*q
      linarith) (by
      intro x _ Nonzero
      have Away : ¬Goal x := by simpa [Potential] using Nonzero
      rw [RelativeJumpProbability Samples Goal x Away (1/2) (by norm_num) (by norm_num)]
      simp [Potential,Away,q])
  have Mean : (∫ x, MultiplicativeDriftPotential 1 1 (Potential Goal x) ∂Initial.toMeasure)=
      Initial.toMeasure.real {x | ¬Goal x} := by
    have Formula : (fun x => MultiplicativeDriftPotential 1 1 (Potential Goal x))=
        ({x | ¬Goal x}).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases Reached : Goal x <;> simp [MultiplicativeDriftPotential,Potential,Reached]
    rw [Formula,integral_indicator_const _ (Set.to_countable _).measurableSet,smul_eq_mul,mul_one]
  rw [Mean] at Bound
  have Coefficient (m : ℝ) : (((1 : ℝ)-1/2)/(1+1/2))*(m/(2*q))=m/(6*q) := by ring
  rw [Coefficient] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RandomSearch
