import ECTheoryLib.Tools.Drift.NonabsorbingGeometricJump
import ECTheoryLib.Probability.Processes.HistoryConditional

/-!
# Nonabsorbing finite-state runtime bounds from the actual kernel

The trajectory history supplies the filtration. No target-preservation
premise is imposed on the algorithm.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Geometric-jump negative drift for an actual finite-state kernel without
target preservation. Full-history conditional bounds follow from the
trajectory law, so stopping does not require a Markov property of the potential. -/
theorem GeometricJumpRuntimeLowerTailNonabsorbing (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal : State → Prop) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r)
    (TargetIff : ∀ x, V x≤a ↔ Goal x)
    (InitiallyAbove : ∀ᵐ x ∂Initial.toMeasure, b≤V x)
    (JumpTail : ∀ x, a<V x → ∀ j : ℕ,
      (Step x).toMeasure {y | (j : ℝ)≤|V y-V x|} ≤ ENNReal.ofReal (r/(1+eta)^j))
    (Drift : ∀ x, a<V x → V x<b → (∫ y, V x-V y ∂(Step x).toMeasure) ≤ -Delta)
    (t : ℕ) :
    PathMeasure Step Initial {Path | FirstHittingTime Goal Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*GeometricJumpMomentBound eta r*
        Real.exp (-GeometricJumpDriftExponent eta Delta r*(b-a))) := by
  classical
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun j Path => V (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => State)
  let S : Finset ℝ := Finset.univ.image V
  have AdaptedX : Adapted F X := PathPotentialAdapted V
  have Values (j : ℕ) (Path : ℕ → State) : X j Path∈S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have InitialPaths : ∀ᵐ Path ∂μ, b≤X 0 Path := by
    have InitialMap : ∀ᵐ x ∂(PathMeasure Step Initial).map (fun Path : ℕ → State => Path 0), b≤V x := by
      rw [PathMeasureInitial]
      exact InitiallyAbove
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable InitialMap
  have HistoryTail (k j : ℕ) : ∀ᵐ Path ∂μ, a<X k Path →
      (μ[({u | (j : ℝ)≤|X (k+1) u-X k u|}).indicator (fun _ => (1 : ℝ)) | F k]) Path ≤
        r/(1+eta)^j := by
    have Identity := PathMeasureStateConditionalExpectation Step Initial k
      (fun x => ({y | (j : ℝ)≤|V y-V x|}).indicator (fun _ => (1 : ℝ)))
    filter_upwards [Identity] with Path Equal
    intro Above
    change (μ[fun u => ({y | (j : ℝ)≤|V y-V (u k)|}).indicator (fun _ => (1 : ℝ)) (u (k+1)) |
      F k]) Path ≤ r/(1+eta)^j
    rw [Equal, integral_indicator_const _ (Set.to_countable _).measurableSet, smul_eq_mul, mul_one]
    have Bound := JumpTail (Path k) Above j
    rw [← ofReal_measureReal (μ := (Step (Path k)).toMeasure)] at Bound
    exact (ENNReal.ofReal_le_ofReal_iff
      (div_nonneg PositiveR.le (pow_nonneg (by linarith) j))).mp Bound
  have HistoryDrift (k : ℕ) : ∀ᵐ Path ∂μ, a<X k Path ∧ X k Path<b →
      (μ[fun u => X k u-X (k+1) u | F k]) Path ≤ -Delta := by
    have Identity := PathMeasureStateConditionalExpectation Step Initial k (fun x y => V x-V y)
    filter_upwards [Identity] with Path Equal
    intro InRegion
    rw [Equal]
    exact Drift (Path k) InRegion.1 InRegion.2
  have Bound := GeometricJumpNegativeDriftTailNonabsorbing μ X F AdaptedX S a b eta Delta r
    Ordered PositiveEta PositiveDelta PositiveR Values InitialPaths HistoryTail HistoryDrift t
  have Events : {Path | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j Path) ≤ (t : WithTop ℕ)} =
      {Path | FirstHittingTime Goal Path ≤ (t : WithTop ℕ)} := by
    ext Path
    simp only [Set.mem_ofPred_eq, FirstHittingTimeLeIff, X, TargetIff]
  rw [Events] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
