import ECTheoryLib.Probability.Processes.Process

/-!
# Actual trajectory conditional expectations given the complete past

Finite histories have their actual joint law with the next state.
Mathlib conditional-expectation uniqueness transfers the kernel integral.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- One-step integration for a real function of the entire finite past and
the next state, using the actual joint trajectory/kernel law. -/
theorem PathMeasureHistoryTransitionIntegral (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : (Finset.Iic t → State) → State → ℝ) :
    (∫ Path, f (Preorder.frestrictLe t Path) (Path (t+1)) ∂PathMeasure Step Initial) =
      ∫ Path, (∫ y, f (Preorder.frestrictLe t Path) y ∂(Step (Path t)).toMeasure)
        ∂PathMeasure Step Initial := by
  let pair := fun Path : ℕ → State => (Preorder.frestrictLe t Path,Path (t+1))
  have PairMeasurable : Measurable pair :=
    (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t+1))
  let g := fun p : (Finset.Iic t → State)×State => f p.1 p.2
  calc
    _ = ∫ p, g p ∂(PathMeasure Step Initial).map pair := by
      rw [integral_map_of_stronglyMeasurable PairMeasurable (measurable_of_finite g).stronglyMeasurable]
    _ = ∫ p, g p ∂((PathMeasure Step Initial).map (Preorder.frestrictLe t) ⊗ₘ HistoryKernel Step t) := by
      rw [PathMeasureJointLaw Step Initial t]
    _ = ∫ h, (∫ y, f h y ∂(Step (HistoryLast t h)).toMeasure)
        ∂(PathMeasure Step Initial).map (Preorder.frestrictLe t) := by
      rw [Measure.integral_compProd Integrable.of_finite]
      rfl
    _ = _ := by
      rw [integral_map_of_stronglyMeasurable (Preorder.measurable_frestrictLe t)
        (measurable_of_finite _).stronglyMeasurable]
      rfl

/-- The actual next-state kernel gives the conditional expectation given
the complete past. It is not merely conditioning on the current potential. -/
theorem PathMeasureHistoryConditionalExpectation (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : (Finset.Iic t → State) → State → ℝ) :
    (PathMeasure Step Initial)[fun Path => f (Preorder.frestrictLe t Path) (Path (t+1)) |
      Filtration.piLE (X := fun _ : ℕ => State) t] =ᵐ[PathMeasure Step Initial]
      (fun Path => ∫ y, f (Preorder.frestrictLe t Path) y ∂(Step (Path t)).toMeasure) := by
  classical
  let μ := PathMeasure Step Initial
  let V := fun Path : ℕ → State => f (Preorder.frestrictLe t Path) (Path (t+1))
  let W := fun h : Finset.Iic t → State => ∫ y, f h y ∂(Step (HistoryLast t h)).toMeasure
  let g := fun Path : ℕ → State => W (Preorder.frestrictLe t Path)
  have PairMeasurable : Measurable (fun Path : ℕ → State => (Preorder.frestrictLe t Path,Path (t+1))) :=
    (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t+1))
  have IntegrableV : Integrable V μ :=
    (Integrable.of_finite (μ := μ.map (fun Path => (Preorder.frestrictLe t Path,Path (t+1))))
      (f := fun p => f p.1 p.2)).comp_measurable PairMeasurable
  have IntegrableG : Integrable g μ :=
    (Integrable.of_finite (μ := μ.map (Preorder.frestrictLe t)) (f := W)).comp_measurable
      (Preorder.measurable_frestrictLe t)
  have StronglyG : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => State) t] g := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact (measurable_of_finite W).stronglyMeasurable.comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)
  apply (ae_eq_condExp_of_forall_setIntegral_eq (Filtration.piLE.le t) IntegrableV
    (fun _ _ _ => IntegrableG.integrableOn) _ StronglyG.aestronglyMeasurable).symm
  intro s MeasurableS _FiniteS
  rw [Filtration.piLE_eq_comap_frestrictLe] at MeasurableS
  obtain ⟨A,MeasurableA,rfl⟩ := MeasurableS
  have EventMeasurable : MeasurableSet (Preorder.frestrictLe (π := fun _ : ℕ => State) t ⁻¹' A) :=
    MeasurableA.preimage (Preorder.measurable_frestrictLe t)
  have Identity := PathMeasureHistoryTransitionIntegral Step Initial t
    (fun h y => if h∈A then f h y else 0)
  have Inner (h : Finset.Iic t → State) :
      (∫ y, (if h∈A then f h y else 0) ∂(Step (HistoryLast t h)).toMeasure)=
        if h∈A then W h else 0 := by
    by_cases Member : h∈A
    · simp only [if_pos Member, W]
    · simp only [if_neg Member, integral_zero]
  change (∫ Path, (if Preorder.frestrictLe t Path∈A then V Path else 0) ∂μ) =
    ∫ Path, (∫ y, (if Preorder.frestrictLe t Path∈A then f (Preorder.frestrictLe t Path) y else 0)
      ∂(Step (HistoryLast t (Preorder.frestrictLe t Path))).toMeasure) ∂μ at Identity
  simp_rw [Inner] at Identity
  change (∫ Path, (Preorder.frestrictLe t ⁻¹' A).indicator V Path ∂μ) =
    ∫ Path, (Preorder.frestrictLe t ⁻¹' A).indicator g Path ∂μ at Identity
  rw [integral_indicator EventMeasurable, integral_indicator EventMeasurable] at Identity
  exact Identity.symm

/-- State-dependent increments are conditioned on the full trajectory history. -/
theorem PathMeasureStateConditionalExpectation (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : State → State → ℝ) :
    (PathMeasure Step Initial)[fun Path => f (Path t) (Path (t+1)) |
      Filtration.piLE (X := fun _ : ℕ => State) t] =ᵐ[PathMeasure Step Initial]
      (fun Path => ∫ y, f (Path t) y ∂(Step (Path t)).toMeasure) :=
  PathMeasureHistoryConditionalExpectation Step Initial t (fun h y => f (HistoryLast t h) y)

/-- Every finite-state potential is adapted to the complete coordinate history. -/
theorem PathPotentialAdapted (V : State → ℝ) :
    Adapted (Filtration.piLE (X := fun _ : ℕ => State)) (fun t Path => V (Path t)) := by
  intro t
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_finite (fun h : Finset.Iic t → State => V (HistoryLast t h))).comp
    (measurable_iff_comap_le.mpr le_rfl)

end
end ECTheoryLib.Probability
