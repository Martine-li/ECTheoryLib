import ECTheoryLib.Analysis.OneMax.RLSWithShortcuts.Drift
import ECTheoryLib.Tools.Runtime.Geometric
import ECTheoryLib.Tools.Runtime.LocalDrift
import ECTheoryLib.Probability.Processes.InitialMixture

/-!
Two actual drift calls and an independent geometric success argument on one kernel.
Arbitrary initialization retains the optimum atom; termination is a conclusion.
-/
namespace ECTheoryLib.Analysis.RLSWithShortcuts
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
open scoped unitInterval Classical
noncomputable section

private theorem VariableRuntimeBound {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, VariableDriftPotential 1 (fun s => Delta n * s) (OneMax x : ℝ) ∂Initial.toMeasure) := by
  classical
  let μ := PathMeasure (Step PositiveLength) Initial
  let X : ℕ → (ℕ → Bits n) → ℝ := fun t Path => (OneMax (Path t) : ℝ)
  let S : Finset ℝ := insert 0 (Finset.univ.image (fun x : Bits n => (OneMax x : ℝ)))
  have Lower : ∀ s ∈ S, s = 0 ∨ 1 ≤ s := by
    intro s InS
    rcases Finset.mem_insert.mp InS with Zero | Image
    · exact Or.inl Zero
    · rcases Finset.mem_image.mp Image with ⟨x, _, rfl⟩
      by_cases Zero : OneMax x = 0
      · exact Or.inl (by simp [Zero])
      · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)
  have Values : ∀ t Path, X t Path ∈ S := by
    intro t Path
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨Path t, Finset.mem_univ _, rfl⟩)
  have AdaptedX : Adapted (Filtration.piLE (X := fun _ : ℕ => Bits n)) X :=
    CountablePathPotentialAdapted (fun x => (OneMax x : ℝ))
  have Absorbing : ZeroIsAbsorbing μ X :=
    PathMeasureZeroIsAbsorbing (Step PositiveLength) Initial (fun x => (OneMax x : ℝ))
      (fun _ => True) (fun _ => ae_of_all _ (fun _ => trivial))
      (fun x => (StepPreservesZero PositiveLength x).mono (fun _ Holds _ => Holds))
  have Drift : ∀ t s, s ∈ S → s ≠ 0 → 0 < μ (StateEvent X t s) →
      Delta n * s ≤ StateDrift μ X t s := by
    intro t s _ _ EventPositive
    exact le_of_eq (PathMeasureStateDrift (Step PositiveLength) Initial (fun x => (OneMax x : ℝ))
      (fun s => Delta n * s) (CountDrift PositiveLength) t s EventPositive).symm
  have Variable := VariableDriftUpperBound μ X S 1 (fun s => Delta n * s)
    (fun _ => AdaptedX.measurable) (Finset.mem_insert_self _ _) (by norm_num) Lower Values
    Absorbing (fun s H => mul_pos (DeltaPositive PositiveLength) (lt_of_lt_of_le (by norm_num) H))
    (fun _ _ _ _ H => mul_le_mul_of_nonneg_left H (DeltaPositive PositiveLength).le) Drift
  have Hitting := ExpectedHittingTimeEqExpectedZero (Step PositiveLength) Initial
    (fun x => (OneMax x : ℝ)) (fun x => (OneMax x : ℝ) = 0) (fun _ => Iff.rfl)
  change ExpectedRuntime PositiveLength Initial = ExpectedZeroHittingTime μ X at Hitting
  have VariableInitial := PathMeasureInitialIntegral (Step PositiveLength) Initial
    (fun x => VariableDriftPotential 1 (fun s => Delta n * s) (OneMax x : ℝ))
  change ExpectedValue μ (fun Path => VariableDriftPotential 1
    (fun s => Delta n * s) (X 0 Path)) = _ at VariableInitial
  rw [VariableInitial] at Variable
  rw [Hitting]
  exact Variable

theorem VariableRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal
      (∫ x, VariableDriftPotential 1 (fun s => Delta n * s) (OneMax x : ℝ) ∂Initial.toMeasure) :=
  VariableRuntimeBound PositiveLength Initial

theorem MultiplicativeRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal (∫ x, Bound x ∂Initial.toMeasure) := by
  have PreservesNatural : ∀ x, ∀ᵐ y ∂(Step PositiveLength x).toMeasure,
      True → OneMax x = 0 → OneMax y = 0 := by
    intro x
    filter_upwards [StepPreservesZero PositiveLength x] with y Preserves
    intro _ Zero
    exact Nat.cast_eq_zero.mp (Preserves (Nat.cast_eq_zero.mpr Zero))
  exact Tools.Runtime.MultiplicativeRuntimeUpperBound (Step PositiveLength) Initial OneMax
    (fun x => (OneMax x : ℝ) = 0) (fun _ => True) (fun _ => Nat.cast_eq_zero.symm)
    (ae_of_all _ (fun _ => trivial)) (fun _ => ae_of_all _ (fun _ _ => trivial))
    PreservesNatural (Delta n) (DeltaPositive PositiveLength)
    (fun x _ _ => (CountDrift PositiveLength x).symm.le)

theorem VariablePotentialEqBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    VariableDriftPotential 1 (fun s => Delta n * s) (OneMax x : ℝ) = Bound x := by
  apply LinearVariableDriftPotential 1 (Delta n) (OneMax x : ℝ) (by norm_num)
    (DeltaPositive PositiveLength)
  by_cases Zero : OneMax x = 0
  · exact Or.inl (by simp [Zero])
  · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Zero)

/-- Direct local success gives a geometric bound, independently of the drift upper bound. -/
theorem GeometricRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤ ENNReal.ofReal (n : ℝ) := by
  have Bound := Tools.Runtime.PathWaitingExpectedRuntime (Step PositiveLength) Initial
    (fun x => (OneMax x : ℝ) = 0) (fun _ => True)
    (Algorithms.RLSWithShortcuts.ShortcutProbability PositiveLength)
    (Algorithms.RLSWithShortcuts.ShortcutProbabilityPositive PositiveLength)
    (fun _ => ae_of_all _ (fun _ => trivial)) (StepPreservesZero PositiveLength)
    (fun x _ _ => SuccessProbabilityLower PositiveLength x)
  simpa only [ExpectedRuntime, Algorithms.RLSWithShortcuts.ShortcutProbability, one_div_one_div] using Bound

theorem RuntimeFinite {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≠ ⊤ :=
  (lt_of_le_of_lt (GeometricRuntimeUpper PositiveLength Initial) ENNReal.ofReal_lt_top).ne

theorem AtGoalRuntime {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) (Zero : (OneMax x : ℝ) = 0) :
    ExpectedRuntime PositiveLength (PMF.pure x) = 0 :=
  ExpectedHittingTimeOfPureTarget (Step PositiveLength) (fun x => (OneMax x : ℝ) = 0) x Zero

/-- Mixture of the fixed-state geometric bounds keeps any initially successful mass. -/
theorem InitialFailureRuntimeUpper {n : ℕ} (PositiveLength : 0 < n) (Initial : PMF (Bits n)) :
    ExpectedRuntime PositiveLength Initial ≤
      ENNReal.ofReal ((n : ℝ) * Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0}) := by
  let f : Bits n → ℝ := fun x => if (OneMax x : ℝ) = 0 then 0 else (n : ℝ)
  have Nonnegative : ∀ x, 0 ≤ f x := by
    intro x
    simp only [f]
    split_ifs <;> positivity
  have IntegralValue : (∫ x, f x ∂Initial.toMeasure) =
      (n : ℝ) * Initial.toMeasure.real {x | (OneMax x : ℝ) ≠ 0} := by
    have AsIndicator : f = {x : Bits n | (OneMax x : ℝ) ≠ 0}.indicator (fun _ => (n : ℝ)) := by
      funext x
      by_cases Zero : (OneMax x : ℝ) = 0 <;> simp [f, Set.indicator_apply]
    rw [AsIndicator, integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul]
    ring
  calc
    ExpectedRuntime PositiveLength Initial =
        ∫⁻ x, ExpectedRuntime PositiveLength (PMF.pure x) ∂Initial.toMeasure :=
      ExpectedHittingTimeInitialMixture (Step PositiveLength) (fun x => (OneMax x : ℝ) = 0) Initial
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂Initial.toMeasure := by
      apply lintegral_mono
      intro x
      by_cases Zero : (OneMax x : ℝ) = 0
      · simp [f, AtGoalRuntime PositiveLength x Zero]
      · simpa only [f, if_neg Zero] using GeometricRuntimeUpper PositiveLength (PMF.pure x)
    _ = ENNReal.ofReal (∫ x, f x ∂Initial.toMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ Nonnegative)).symm
    _ = _ := by rw [IntegralValue]

end
end ECTheoryLib.Analysis.RLSWithShortcuts

