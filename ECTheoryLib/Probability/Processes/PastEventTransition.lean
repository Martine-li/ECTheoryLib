import ECTheoryLib.Probability.Processes.Process
import Mathlib.Probability.Process.Adapted

/-!
# Transition bounds on arbitrary past events

The actual path law has the history/next-state joint law already established
in Process. Mathlib piLE identifies past events with inverse images of finite
histories. Integrating a kernel bound over such an event is the bridge needed
by history-sensitive runtime arguments; no independence from the past is assumed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Integrate a local kernel bound over an arbitrary event determined by the past. -/
theorem PathPastEventTransitionBound {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (A : Set (ℕ → State)) (PastA : MeasurableSet[Filtration.piLE t] A)
    (C : Set State) (q : ℝ) (Nonnegative : 0 ≤ q)
    (LocalBound : ∀ᵐ Path ∂PathMeasure Step Initial, Path ∈ A → (Step (Path t)).toMeasure.real C ≤ q) :
    (PathMeasure Step Initial).real (A ∩ {Path | Path (t+1) ∈ C}) ≤
      q*(PathMeasure Step Initial).real A := by
  let P := PathMeasure Step Initial
  let H := Preorder.frestrictLe (π := fun _ => State) t
  let μ := P.map H
  have MeasurableH : Measurable H := Preorder.measurable_frestrictLe t
  rw [Filtration.piLE_eq_comap_frestrictLe] at PastA
  obtain ⟨B, MeasurableB, Event⟩ := PastA
  change H ⁻¹' B = A at Event
  have MeasurableC : MeasurableSet C := (Set.to_countable C).measurableSet
  have HistoriesBound : ∀ᵐ h ∂μ, h ∈ B → (HistoryKernel Step t h) C ≤ ENNReal.ofReal q := by
    apply (ae_map_iff MeasurableH.aemeasurable (Set.to_countable _).measurableSet).mpr
    filter_upwards [LocalBound] with Path Bound
    intro InB
    have InA : Path ∈ A := by rw [← Event]; exact InB
    have BoundReal := Bound InA
    change (Step (Path t)).toMeasure C ≤ ENNReal.ofReal q
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal BoundReal
  have JointMeasurable : Measurable (fun Path : ℕ → State => (H Path, Path (t+1))) :=
    MeasurableH.prodMk (measurable_pi_apply (t+1))
  have JointEvent : (fun Path : ℕ → State => (H Path, Path (t+1))) ⁻¹' (B ×ˢ C) =
      A ∩ {Path | Path (t+1) ∈ C} := by
    rw [← Event]
    rfl
  have JointMass : P (A ∩ {Path | Path (t+1) ∈ C}) =
      (μ ⊗ₘ HistoryKernel Step t) (B ×ˢ C) := by
    rw [PathMeasureJointLaw Step Initial t, Measure.map_apply JointMeasurable (MeasurableB.prod MeasurableC)]
    rw [JointEvent]
  have Bound : P (A ∩ {Path | Path (t+1) ∈ C}) ≤ ENNReal.ofReal q * P A := by
    rw [JointMass, Measure.compProd_apply_prod MeasurableB MeasurableC]
    calc
      _ ≤ ∫⁻ _h in B, ENNReal.ofReal q ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae HistoriesBound, ae_restrict_mem MeasurableB] with h Bound InB
        exact Bound InB
      _ = ENNReal.ofReal q * P A := by
        rw [setLIntegral_const, Measure.map_apply MeasurableH MeasurableB, Event]
  have RealBound := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mpr Bound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal Nonnegative] at RealBound
  exact RealBound

/-- The canonical trajectory coordinates are adapted to Mathlib's natural past filtration. -/
theorem PathCoordinatesAdapted {State : Type*} [MeasurableSpace State] :
    Adapted (Filtration.piLE (X := fun _ : ℕ => State)) (fun t (Path : ℕ → State) => Path t) := by
  intro t
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have PrefixMeasurable := comap_measurable (m := inferInstance)
    (Preorder.frestrictLe (π := fun _ => State) t)
  exact (measurable_pi_apply (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t)).comp PrefixMeasurable

end
end ECTheoryLib.Probability
