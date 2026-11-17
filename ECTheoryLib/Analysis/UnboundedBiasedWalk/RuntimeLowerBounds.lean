import ECTheoryLib.Probability.RandomWalks.UnboundedBiasedWalk
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Tools.Drift.IntegrableExponentialMomentNegative

/-!
# First-hitting lower tails for the actual unbounded walk

The actual kernel yields integrable increments and complete-history moment
bounds. Apply the general negative-drift theorem without a finite-range witness.
-/

namespace ECTheoryLib.Analysis.UnboundedBiasedWalk
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Probability.UnboundedBiasedWalk ECTheoryLib.Tools.Drift
noncomputable section

theorem PathAbsoluteJumpBound (Initial : PMF ℕ) (t : ℕ) :
    ∀ᵐ Path ∂PathMeasure Step Initial, |Potential (Path (t+1))-Potential (Path t)|≤1 :=
  PathMeasureFollowsTransition Step Initial _ StepAbsoluteJumpBound t

theorem PathIncrementIntegrable (Initial : PMF ℕ) (t : ℕ) :
    Integrable (fun Path => Potential (Path (t+1))-Potential (Path t)) (PathMeasure Step Initial) := by
  have Observable : Measurable (fun Path : ℕ → ℕ => Potential (Path (t+1))-Potential (Path t)) :=
    ((measurable_of_countable Potential).comp (measurable_pi_apply (t+1))).sub
      ((measurable_of_countable Potential).comp (measurable_pi_apply t))
  apply (integrable_const (1 : ℝ)).mono' Observable.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using PathAbsoluteJumpBound Initial t

theorem PathAbsoluteMomentIntegrable (Initial : PMF ℕ) (t : ℕ) (q : ℝ) (Nonnegative : 0≤q) :
    Integrable (fun Path => Real.exp (q*|Potential (Path (t+1))-Potential (Path t)|))
      (PathMeasure Step Initial) := by
  apply (integrable_const (Real.exp q)).mono'
    (Real.measurable_exp.comp_aemeasurable ((PathIncrementIntegrable Initial t).aemeasurable.abs.const_mul q)).aestronglyMeasurable
  filter_upwards [PathAbsoluteJumpBound Initial t] with Path Bound
  change ‖Real.exp (q*|Potential (Path (t+1))-Potential (Path t)|)‖≤Real.exp q
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left Bound Nonnegative

theorem PathConditionalIncrement (Initial : PMF ℕ) (t : ℕ) :
    (PathMeasure Step Initial)[fun Path => Potential (Path (t+1))-Potential (Path t) |
      Filtration.piLE (X := fun _ : ℕ => ℕ) t] =ᵐ[PathMeasure Step Initial]
        (fun Path => if Path t=0 then 0 else (1/2 : ℝ)) := by
  have Identity := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun x y => Potential y-Potential x) (PathIncrementIntegrable Initial t)
  filter_upwards [Identity] with Path Equal
  rw [Equal,OneStepIncrement]

theorem PathConditionalAbsoluteMoment (Initial : PMF ℕ) (t : ℕ) (q : ℝ) (Nonnegative : 0≤q) :
    (PathMeasure Step Initial)[fun Path => Real.exp (q*|Potential (Path (t+1))-Potential (Path t)|) |
      Filtration.piLE (X := fun _ : ℕ => ℕ) t] =ᵐ[PathMeasure Step Initial]
        (fun Path => if Path t=0 then 1 else Real.exp q) := by
  have Identity := PathMeasureStateConditionalExpectationOfIntegrable Step Initial t
    (fun x y => Real.exp (q*|Potential y-Potential x|)) (PathAbsoluteMomentIntegrable Initial t q Nonnegative)
  filter_upwards [Identity] with Path Equal
  rw [Equal,OneStepAbsoluteExponentialMoment]

def RuntimeExponent : ℝ := AbsoluteMomentDriftExponent 1 (1/2) (Real.exp 1)

theorem RuntimeExponentPositive : 0<RuntimeExponent :=
  AbsoluteMomentDriftExponentPositive _ _ _ (by norm_num) (by norm_num) (Real.exp_pos _)

/-- The genuine unbounded walk calls the general absolute-moment theorem.
There is no finite-state or finite-potential certificate in this application. -/
theorem FixedRuntimeMomentLowerTail (L : ℕ) (Positive : 0<L) (t : ℕ) :
    PathMeasure Step (PMF.pure L) {Path | FirstHittingTime (fun x : ℕ => x=0) Path≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*Real.exp 1*Real.exp (-RuntimeExponent*(L : ℝ))) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun j Path => Potential (Path j)
  let μ := PathMeasure Step (PMF.pure L)
  have Initial : ∀ᵐ Path ∂μ, (L : ℝ)≤X 0 Path := by
    have InitialMap : ∀ᵐ x ∂(PathMeasure Step (PMF.pure L)).map (fun Path : ℕ → ℕ => Path 0), (L : ℝ)≤Potential x := by
      rw [PathMeasureInitial,PMF.toMeasure_pure]
      exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr le_rfl
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable InitialMap
  have Bound := GeneralExponentialMomentNegativeDriftTail μ X
    (Filtration.piLE (X := fun _ : ℕ => ℕ)) (CountablePathPotentialAdapted Potential)
    0 (L : ℝ) 1 (1/2) (Real.exp 1) (Nat.cast_pos.mpr Positive) (by norm_num) (by norm_num) (Real.exp_pos _)
    Initial (fun j => PathMeasureFollowsTransition Step (PMF.pure L) _ StepZeroAbsorbing j)
    (PathIncrementIntegrable (PMF.pure L))
    (fun j => PathAbsoluteMomentIntegrable (PMF.pure L) j 1 (by norm_num)) (by
      intro j
      filter_upwards [PathConditionalAbsoluteMoment (PMF.pure L) j 1 (by norm_num)] with Path Equal
      intro Above
      have Nonzero : Path j≠0 := by
        intro Zero
        change 0<Potential (Path j) at Above
        simp only [Zero,Potential,Nat.cast_zero,lt_self_iff_false] at Above
      rw [Equal,if_neg Nonzero]) (by
      intro j
      filter_upwards [PathConditionalIncrement (PMF.pure L) j] with Path Equal
      intro InRegion
      have Nonzero : Path j≠0 := by
        intro Zero
        have Above := InRegion.1
        change 0<Potential (Path j) at Above
        simp only [Zero,Potential,Nat.cast_zero,lt_self_iff_false] at Above
      rw [Equal,if_neg Nonzero]) t
  have Events : {Path | FirstHittingTime (fun s : ℝ => s≤0) (fun j => X j Path)≤(t : WithTop ℕ)} =
      {Path | FirstHittingTime (fun x : ℕ => x=0) Path≤(t : WithTop ℕ)} := by
    ext Path
    simp only [Set.mem_ofPred_eq,FirstHittingTimeLeIff,X,Potential,Nat.cast_nonpos]
  rw [Events] at Bound
  simpa only [sub_zero,RuntimeExponent] using Bound

end
end ECTheoryLib.Analysis.UnboundedBiasedWalk
