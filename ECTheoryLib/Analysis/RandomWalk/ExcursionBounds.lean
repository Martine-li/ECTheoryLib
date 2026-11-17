import ECTheoryLib.Probability.RandomWalks.FiniteBiasedWalk
import ECTheoryLib.Probability.HittingTimes.SupermartingaleHitting
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Probability.Processes.PathDriftBounds

/-!
# Upward excursions of the actual finite biased walk

The linear potential is a supermartingale under the real transition law.
-/

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

theorem PathPotentialSupermartingale (N : ℕ) (ε : I) (Initial : PMF (Fin (N+1))) :
    Supermartingale (fun t Path => Probability.FiniteBiasedWalk.Potential (Path t))
      (Filtration.piLE (X := fun _ : ℕ => Fin (N+1)))
      (PathMeasure (Probability.FiniteBiasedWalk.Step N ε) Initial) := by
  let V := @Probability.FiniteBiasedWalk.Potential N
  let Step := Probability.FiniteBiasedWalk.Step N ε
  have IntegrableV (t : ℕ) := PathMeasureCoordinateIntegrable Step Initial V t
  apply supermartingale_of_condExp_sub_nonneg_nat
    (fun t => (CountablePathPotentialAdapted V t).stronglyMeasurable) IntegrableV
  intro t
  have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun x y => V x-V y) ((IntegrableV t).sub (IntegrableV (t+1)))
  filter_upwards [Conditional] with Path Equal
  change 0≤((PathMeasure Step Initial)[fun Path => V (Path t)-V (Path (t+1)) |
    Filtration.piLE (X := fun _ : ℕ => Fin (N+1)) t]) Path
  rw [Equal,Probability.FiniteBiasedWalk.OneStepDrift]
  split_ifs
  · rfl
  · exact ε.2.1

/-- A bound on actual upward excursions, independent of the weak-bias limit. -/
theorem UpperBarrierByTime (N : ℕ) (ε : I) (x : Fin (N+1))
    (m : ℝ) (Positive : 0<m) (t : ℕ) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N ε) (PMF.pure x))
      {Path | FirstHittingTime (fun y => m≤(y.val : ℝ)) Path≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((x.val : ℝ)/m) := by
  let V := @Probability.FiniteBiasedWalk.Potential N
  have Bound := NonnegativeSupermartingaleHittingBound
    (PathMeasure (Probability.FiniteBiasedWalk.Step N ε) (PMF.pure x))
    (fun t Path => V (Path t)) (Filtration.piLE (X := fun _ : ℕ => Fin (N+1)))
    (PathPotentialSupermartingale N ε (PMF.pure x))
    (fun _ => ae_of_all _ (fun Path => Nat.cast_nonneg (Path _).val)) m Positive t
  have TimeEqual (Path : ℕ → Fin (N+1)) :
      FirstHittingTime (fun s : ℝ => m≤s) (fun j => V (Path j))=
        FirstHittingTime (fun y => m≤(y.val : ℝ)) Path := by
    apply WithTop.eq_of_forall_le_coe_iff
    intro j
    exact (FirstHittingTimeLeIff (fun s : ℝ => m≤s) (fun j => V (Path j)) j).trans
      (FirstHittingTimeLeIff (fun y : Fin (N+1) => m≤(y.val : ℝ)) Path j).symm
  simp_rw [TimeEqual] at Bound
  rw [PathMeasurePureInitialIntegral] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.FiniteBiasedWalk
