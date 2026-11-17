import ECTheoryLib.Probability.RandomWalks.ReflectingBiasedWalk
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Tools.Drift.GeneralGeometricJumpNegative

/-!
# First-hitting lower tails for an unbounded nonabsorbing walk

Derive complete-history hypotheses from the actual kernel and apply the
general theorem. Time counts transitions; the first visit to zero is the target.
-/

namespace ECTheoryLib.Analysis.ReflectingBiasedWalk
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Probability.ReflectingBiasedWalk ECTheoryLib.Tools.Drift
noncomputable section

theorem PathAbsoluteJumpBound (Initial : PMF ℕ) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure Step Initial, |(Path (t+1) : ℝ)-(Path t : ℝ)|≤1 :=
  PathMeasureFollowsTransition Step Initial _ StepAbsoluteJumpBound t

theorem PathIncrementIntegrable (Initial : PMF ℕ) (t : ℕ) :
    Integrable (fun Path => (Path (t+1) : ℝ)-(Path t : ℝ)) (PathMeasure Step Initial) := by
  have Observable : Measurable (fun Path : ℕ → ℕ => (Path (t+1) : ℝ)-(Path t : ℝ)) :=
    ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (measurable_pi_apply (t+1))).sub
      ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (measurable_pi_apply t))
  apply (integrable_const (1 : ℝ)).mono' Observable.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using PathAbsoluteJumpBound Initial t

theorem PathConditionalIncrement (Initial : PMF ℕ) (t : ℕ) :
    (PathMeasure Step Initial)[fun Path => (Path (t+1) : ℝ)-(Path t : ℝ) |
      Filtration.piLE (X := fun _ : ℕ => ℕ) t] =ᵐ[PathMeasure Step Initial]
        (fun Path => if Path t=0 then 1 else (1/2 : ℝ)) := by
  have Identity := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun x y => (y : ℝ)-(x : ℝ)) (PathIncrementIntegrable Initial t)
  filter_upwards [Identity] with Path Equal
  rw [Equal,OneStepIncrement]

theorem PathConditionalJumpTail (Initial : PMF ℕ) (t j : ℕ) :
    ((PathMeasure Step Initial)[({Path | (j : ℝ)≤|(Path (t+1) : ℝ)-(Path t : ℝ)|}).indicator
      (fun _ => (1 : ℝ)) | Filtration.piLE (X := fun _ : ℕ => ℕ) t]) ≤ᵐ[PathMeasure Step Initial]
        (fun _ => 2/(1+(1 : ℝ))^j) := by
  apply ConditionalUnitJumpTail (PathMeasure Step Initial) _ (Filtration.le _ t)
    (fun Path => (Path (t+1) : ℝ)-(Path t : ℝ)) _ (PathAbsoluteJumpBound Initial t) j
  exact ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (measurable_pi_apply (t+1))).sub
    ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (measurable_pi_apply t))

def RuntimeExponent : ℝ := GeometricJumpDriftExponent 1 (1/2) 2

theorem RuntimeExponentPositive : 0<RuntimeExponent :=
  GeometricJumpDriftExponentPositive _ _ _ (by norm_num) (by norm_num) (by norm_num)

/-- This actual kernel has infinitely many reachable levels and leaves zero.
The first-hitting bound therefore exercises both removed model restrictions. -/
theorem FixedRuntimeGeometricLowerTail (L : ℕ) (Positive : 0<L) (t : ℕ) :
    PathMeasure Step (PMF.pure L) {Path | FirstHittingTime (fun x : ℕ => x=0) Path≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*12*Real.exp (-RuntimeExponent*(L : ℝ))) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun j Path => (Path j : ℝ)
  let μ := PathMeasure Step (PMF.pure L)
  have Initial : ∀ᵐ Path ∂μ, (L : ℝ)≤X 0 Path := by
    have InitialMap : ∀ᵐ (x : ℕ) ∂(PathMeasure Step (PMF.pure L)).map (fun Path : ℕ → ℕ => Path 0), (L : ℝ)≤(x : ℝ) := by
      rw [PathMeasureInitial,PMF.toMeasure_pure]
      exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr le_rfl
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable InitialMap
  have Bound := GeometricJumpNegativeDriftTailOfIntegrableIncrement μ X
    (Filtration.piLE (X := fun _ : ℕ => ℕ)) (CountablePathPotentialAdapted (fun x : ℕ => (x : ℝ)))
    0 (L : ℝ) 1 (1/2) 2 (Nat.cast_pos.mpr Positive) (by norm_num) (by norm_num) (by norm_num)
    Initial (PathIncrementIntegrable (PMF.pure L)) (by
      intro j k
      exact (PathConditionalJumpTail (PMF.pure L) j k).mono (fun _ Bound _ => Bound)) (by
      intro j
      filter_upwards [PathConditionalIncrement (PMF.pure L) j] with Path Equal
      intro InRegion
      have Nonzero : Path j≠0 := by
        intro Zero
        have Above := InRegion.1
        change 0<(Path j : ℝ) at Above
        simp only [Zero,Nat.cast_zero,lt_self_iff_false] at Above
      rw [Equal,if_neg Nonzero]) t
  have Events : {Path | FirstHittingTime (fun s : ℝ => s≤0) (fun j => X j Path)≤(t : WithTop ℕ)} =
      {Path | FirstHittingTime (fun x : ℕ => x=0) Path≤(t : WithTop ℕ)} := by
    ext Path
    simp only [Set.mem_ofPred_eq,FirstHittingTimeLeIff,X,Nat.cast_nonpos]
  rw [Events] at Bound
  norm_num only [GeometricJumpMomentBound,sub_zero] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.ReflectingBiasedWalk
