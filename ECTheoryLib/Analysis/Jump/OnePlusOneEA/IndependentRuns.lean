import ECTheoryLib.Analysis.Jump.OnePlusOneEA.PlateauRuntime
import ECTheoryLib.Probability.StochasticOrder.ExtendedNatSum

/-!
# Total runtime of independent Jump runs

The sample law is the finite product of actual EA path laws, with possibly
different initial distributions supported on the plateau or optimum. The sum
counts the work of completing all runs, as in sequential independent restarts.
It does not describe the minimum completion time under parallel execution.
Zero runs give the empty sum. Infinite hitting times are preserved.
-/

namespace ECTheoryLib.Analysis.EAJump
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section


/-- Distribution bound for the total work of independent complete runs from the Jump plateau. -/
theorem IndependentPlateauRuntimeSum {n k : ℕ} (PositiveLength : 0 < n) (PositiveGap : 0 < k)
    (GapAtMostLength : k ≤ n) (m : ℕ) (Initial : Fin m → PMF (Bits n))
    (Initially : ∀ i, ∀ᵐ x ∂(Initial i).toMeasure, Region k x) :
    StochasticDominated
      ((Measure.pi (fun i : Fin m => PathMeasure (Step PositiveLength k) (Initial i))).map
        (fun Runs => ∑ i : Fin m, FirstHittingTime (fun x => x = AllOnes n) (Runs i)))
      ((Measure.pi (fun _i : Fin m => geometricMeasure (GapParameter PositiveGap GapAtMostLength))).map
        (fun z : Fin m → ℕ => ∑ i, ((z i+1 : ℕ) : WithTop ℕ))) := by
  let μ := fun i : Fin m => PathMeasure (Step PositiveLength k) (Initial i)
  let p := GapParameter PositiveGap GapAtMostLength
  let P := Measure.pi μ
  let Q := Measure.pi (fun _i : Fin m => geometricMeasure p)
  let T := FirstHittingTime (fun x : Bits n => x = AllOnes n)
  let W := fun j : ℕ => ((j+1 : ℕ) : WithTop ℕ)
  have MeasurableT : Measurable T := FirstHittingTimeMeasurable _
  have MeasurableW : Measurable W := measurable_of_countable _
  have ActualMarginal (i : Fin m) : P.map (fun Runs => T (Runs i)) = (μ i).map T := by
    change P.map (T ∘ Function.eval i) = _
    rw [← Measure.map_map MeasurableT (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]
  have ReferenceMarginal (i : Fin m) : Q.map (fun z => W (z i)) = (geometricMeasure p).map W := by
    change Q.map (W ∘ Function.eval i) = _
    rw [← Measure.map_map MeasurableW (measurable_pi_apply i),
      (measurePreserving_eval (fun _i : Fin m => geometricMeasure p) i).map_eq]
  have ActualIndependent : iIndepFun (fun i : Fin m => fun Runs => T (Runs i)) P :=
    iIndepFun_pi (fun _i => MeasurableT.aemeasurable)
  have ReferenceIndependent : iIndepFun (fun i : Fin m => fun z => W (z i)) Q :=
    iIndepFun_pi (fun _i => MeasurableW.aemeasurable)
  have Bound := ExtendedNatIndependentSum P Q
    (fun i : Fin m => fun Runs => T (Runs i)) (fun i : Fin m => fun z => W (z i))
    (fun i => (MeasurableT.comp (measurable_pi_apply i)).aemeasurable)
    (fun i => (MeasurableW.comp (measurable_pi_apply i)).aemeasurable)
    ActualIndependent ReferenceIndependent (by
      intro i
      rw [ActualMarginal i, ReferenceMarginal i]
      exact PlateauRuntimeGeometricDomination PositiveLength PositiveGap GapAtMostLength
        (Initial i) (Initially i)) Finset.univ
  have ActualSum : (∑ i : Fin m, fun Runs : Fin m → ℕ → Bits n => T (Runs i)) =
      (fun Runs : Fin m → ℕ → Bits n => ∑ i : Fin m, T (Runs i)) := by
    funext Runs
    exact Finset.sum_apply Runs Finset.univ _
  have ReferenceSum : (∑ i : Fin m, fun z : Fin m → ℕ => W (z i)) =
      (fun z : Fin m → ℕ => ∑ i : Fin m, W (z i)) := by
    funext z
    exact Finset.sum_apply z Finset.univ _
  rw [ActualSum, ReferenceSum] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.EAJump
