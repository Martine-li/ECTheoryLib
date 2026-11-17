import ECTheoryLib.Tools.Drift.GeneralExponentialLowerTail
import ECTheoryLib.Analysis.OneMax.RLS.GeometricLowerTailBounds

/-!
# Exponential early-progress bounds for actual RLS on OneMax

The exact conditional exponential moment is derived from the actual binary
increment and full-history conditional mean. The general-target product
theorem then bounds the time until an intermediate zero-count target is
reached. Time counts mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Exact exponential decrease moment conditioned on the complete RLS history,
for arbitrary initialization and real exponential parameter. -/
theorem PathConditionalExponentialDecreaseMoment {n : ℕ} (PositiveLength : 0 < n)
    (Initial : PMF (Bits n)) (j : ℕ) (Lambda : ℝ) :
    (PathMeasure (Step PositiveLength) Initial)[
      fun Path => Real.exp (Lambda * (Potential (Path j) - Potential (Path (j + 1)))) |
      Filtration.piLE (X := fun _ : ℕ => Bits n) j] =ᵐ[
        PathMeasure (Step PositiveLength) Initial]
      (fun Path => 1 + (Real.exp Lambda - 1) * (Potential (Path j) / (n : ℝ))) := by
  let μ := PathMeasure (Step PositiveLength) Initial
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  let D := fun Path : ℕ → Bits n => Potential (Path j) - Potential (Path (j + 1))
  let c := Real.exp Lambda - 1
  have Binary := PathMeasureFollowsTransition (Step PositiveLength) Initial
    (fun x y => Potential x - Potential y = 0 ∨ Potential x - Potential y = 1)
    (StepPotentialDecreaseBinary PositiveLength) j
  have CoordinateIntegrable (i : ℕ) : Integrable (fun Path => Potential (Path i)) μ :=
    FiniteStateCompositionIntegrable μ (fun Path => Potential (Path i))
      (Finset.univ.image (Potential (n := n))) id
      ((measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply i))
      (fun Path => Finset.mem_image.mpr ⟨Path i, Finset.mem_univ _, rfl⟩)
  have DIntegrable : Integrable D μ := (CoordinateIntegrable j).sub (CoordinateIntegrable (j + 1))
  have Affine : (fun Path => Real.exp (Lambda * D Path)) =ᵐ[μ]
      (fun Path => 1 + c * D Path) := by
    filter_upwards [Binary] with Path Drop
    change D Path = 0 ∨ D Path = 1 at Drop
    rcases Drop with Drop | Drop <;> simp [Drop, c]
  have Congruence := condExp_congr_ae (m := F j) Affine
  have Add := condExp_add (integrable_const (1 : ℝ)) (DIntegrable.const_mul c) (F j)
  have Scale := condExp_smul (μ := μ) c D (F j)
  have Mean := PathConditionalDecreaseMean PositiveLength Initial j
  filter_upwards [Congruence, Add, Scale, Mean] with Path Congruence Add Scale Mean
  rw [Congruence]
  change (μ[(fun _ => (1 : ℝ)) + (fun u => c * D u) | F j]) Path = _
  rw [Add]
  change (μ[fun _ => (1 : ℝ) | F j]) Path + (μ[c • D | F j]) Path = _
  rw [condExp_const (F.le j), Scale]
  exact congrArg (fun z : ℝ => 1 + c * z) Mean

/-- A genuine RLS call for any intermediate real target. The same bound applies
to first arrival even without using RLS's target absorption. -/
theorem FixedProgressExponentialLowerTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (a Lambda : ℝ) (NonnegativeLambda : 0 ≤ Lambda)
    (InitialAbove : a < (ZeroCount InitialState : ℝ)) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime (fun x : Bits n => Potential x ≤ a) Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((1 + (Real.exp Lambda - 1) *
        ((ZeroCount InitialState : ℝ) / (n : ℝ))) ^ t *
          Real.exp (-Lambda * ((ZeroCount InitialState : ℝ) - a))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X := fun j (Path : ℕ → Bits n) => Potential (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  let S := Finset.univ.image (Potential (n := n))
  let k : ℝ := ZeroCount InitialState
  let beta := 1 + (Real.exp Lambda - 1) * (k / (n : ℝ))
  have AdaptedX : Adapted F X := PathPotentialAdapted Potential
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have PositiveN : 0 < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have NonnegativeCoefficient : 0 ≤ Real.exp Lambda - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr NonnegativeLambda)
  have OneLeBeta : 1 ≤ beta := by
    have Nonnegative := mul_nonneg NonnegativeCoefficient
      (div_nonneg (show 0 ≤ k from Nat.cast_nonneg _) PositiveN.le)
    dsimp [beta]
    linarith
  have Initial : ∀ᵐ Path ∂μ, X 0 Path = k := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path Equal
    change Potential (Path 0) = k
    rw [Equal]
    rfl
  have Moment (j : ℕ) : ∀ᵐ Path ∂μ, a < X j Path →
      (μ[fun u => Real.exp (Lambda * (id (X j u) - id (X (j + 1) u))) | F j]) Path ≤ beta := by
    filter_upwards [PathConditionalExponentialDecreaseMoment PositiveLength (PMF.pure InitialState) j Lambda,
      PathPotentialLeInitial PositiveLength InitialState j] with Path Exact Reachable
    intro _Above
    simp only [id_eq]
    rw [Exact]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right Reachable PositiveN.le) NonnegativeCoefficient)
  have Bound := ExponentialDriftLowerTailProductOfFixedInitial μ X F AdaptedX S a k Lambda id
    (fun _ => beta) Values NonnegativeLambda (fun _ => OneLeBeta)
    (fun _ _ Below => Below) InitialAbove Initial Moment t
  have Event : {Path | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j Path) ≤ (t : WithTop ℕ)} =
      {Path | FirstHittingTime (fun x : Bits n => Potential x ≤ a) Path ≤ (t : WithTop ℕ)} := by
    ext Path
    change FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j Path) ≤ (t : WithTop ℕ) ↔
      FirstHittingTime (fun x : Bits n => Potential x ≤ a) Path ≤ (t : WithTop ℕ)
    rw [FirstHittingTimeLeIff, FirstHittingTimeLeIff]
  rw [Event] at Bound
  simpa only [id_eq, Finset.prod_const, Finset.card_range] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
