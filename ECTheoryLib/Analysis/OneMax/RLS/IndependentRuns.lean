import ECTheoryLib.Analysis.OneMax.RLS.StochasticProgress
import ECTheoryLib.Probability.StochasticOrder.StochasticSum

/-!
# Independent replicas of the actual RLS trajectory

The finite product of actual trajectory laws models independent RLS runs.
At two different times, the run-indexed families are each independent, but
may be strongly correlated across time. Doerr's Lemma 1.8.4 applies directly
and compares their total zero-count potentials. This is not a parallel-runtime
or speedup theorem. Zero replicas are allowed and give the empty sum.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Product of actual RLS trajectory laws, one for each replica. -/
abbrev IndependentRunsMeasure {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (m : ℕ) : Measure (Fin m → ℕ → Bits n) :=
  Measure.pi (fun _ : Fin m => PathMeasure (Step PositiveLength) Initial)

/-- Total zero-count potential at the specified iteration across all replicas. -/
def IndependentRunsPotentialSum {n m : ℕ} (t : ℕ) (Runs : Fin m → ℕ → Bits n) : ℝ :=
  ∑ i, Potential (Runs i t)

/-- Total potential is measurable on the finite product of trajectory spaces. -/
theorem IndependentRunsPotentialSumMeasurable {n m : ℕ} (t : ℕ) :
    Measurable (IndependentRunsPotentialSum (n := n) (m := m) t) := by
  unfold IndependentRunsPotentialSum
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_finite Potential).comp
    ((measurable_pi_apply t).comp (measurable_pi_apply i))

/-- The total potential of independent actual runs decreases in stochastic order.
Independence and marginal laws are derived from the product construction. -/
theorem IndependentRunsPotentialSumStochasticAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (m s t : ℕ) (Earlier : s ≤ t) :
    StochasticDominated
      ((IndependentRunsMeasure PositiveLength Initial m).map (IndependentRunsPotentialSum t))
      ((IndependentRunsMeasure PositiveLength Initial m).map (IndependentRunsPotentialSum s)) := by
  let μ := PathMeasure (Step PositiveLength) Initial
  let P := IndependentRunsMeasure PositiveLength Initial m
  have MeasurablePotential (k : ℕ) :
      Measurable (fun Path : ℕ → Bits n => Potential (Path k)) := by
    exact (measurable_of_finite Potential).comp (measurable_pi_apply k)
  have MeasurableRun (k : ℕ) (i : Fin m) :
      Measurable (fun Runs : Fin m → ℕ → Bits n => Potential (Runs i k)) := by
    exact (MeasurablePotential k).comp (measurable_pi_apply i)
  have RunMarginal (k : ℕ) (i : Fin m) :
      P.map (fun Runs => Potential (Runs i k)) =
        μ.map (fun Path => Potential (Path k)) := by
    change (Measure.pi (fun _ : Fin m => μ)).map
      ((fun Path : ℕ → Bits n => Potential (Path k)) ∘ Function.eval i) = _
    rw [← Measure.map_map (MeasurablePotential k) (measurable_pi_apply i),
      (measurePreserving_eval (fun _ : Fin m => μ) i).map_eq]
  have Independent (k : ℕ) :
      iIndepFun (fun i : Fin m => fun Runs : Fin m → ℕ → Bits n => Potential (Runs i k)) P := by
    exact iIndepFun_pi (fun _ : Fin m => (MeasurablePotential k).aemeasurable)
  have Termwise (i : Fin m) :
      StochasticDominated (P.map (fun Runs => Potential (Runs i t)))
        (P.map (fun Runs => Potential (Runs i s))) := by
    rw [RunMarginal t i, RunMarginal s i]
    exact PotentialLawStochasticAntitone PositiveLength Initial s t Earlier
  have Bound := StochasticDominatedIndependentSum P P
    (fun i : Fin m => fun Runs : Fin m → ℕ → Bits n => Potential (Runs i t))
    (fun i : Fin m => fun Runs : Fin m → ℕ → Bits n => Potential (Runs i s))
    (fun i => (MeasurableRun t i).aemeasurable) (fun i => (MeasurableRun s i).aemeasurable)
    (Independent t) (Independent s) Termwise Finset.univ
  have SumFunction (k : ℕ) :
      (∑ i : Fin m, fun Runs : Fin m → ℕ → Bits n => Potential (Runs i k)) =
        IndependentRunsPotentialSum k := by
    funext Runs
    rw [Finset.sum_apply]
    rfl
  rw [SumFunction t, SumFunction s] at Bound
  exact Bound

/-- Exceeding any threshold for the total potential becomes no more likely. -/
theorem IndependentRunsPotentialSumTailAntitone {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (m s t : ℕ) (Earlier : s ≤ t) (a : ℝ) :
    (IndependentRunsMeasure PositiveLength Initial m)
        {Runs | a < IndependentRunsPotentialSum t Runs} ≤
      (IndependentRunsMeasure PositiveLength Initial m)
        {Runs | a < IndependentRunsPotentialSum s Runs} := by
  have ProbabilityLaw (k : ℕ) :
      IsProbabilityMeasure ((IndependentRunsMeasure PositiveLength Initial m).map
        (IndependentRunsPotentialSum k)) := by
    exact Measure.isProbabilityMeasure_map
      (IndependentRunsPotentialSumMeasurable k).aemeasurable
  have Bound := (StochasticDominatedIffStrictTail _ _).mp
    (IndependentRunsPotentialSumStochasticAntitone PositiveLength Initial m s t Earlier) a
  rw [Measure.map_apply (IndependentRunsPotentialSumMeasurable t) measurableSet_Ioi,
    Measure.map_apply (IndependentRunsPotentialSumMeasurable s) measurableSet_Ioi] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
