import ECTheoryLib.Tools.Drift.GeometricJumpNegative
import ECTheoryLib.Probability.Processes.ConditionalTransition
import ECTheoryLib.Probability.Processes.PathInvariant

/-!
# Actual finite-state algorithm tails from local geometric-jump bounds

The initial law is any PMF supported above the interval. Local premises use
the actual kernel and are transferred to its trajectory law.
-/

namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section
variable {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Finite-state algorithm interface for geometric-jump negative drift.
The initial distribution can be arbitrary provided it is supported above b.
The local drift, jump tails and target preservation refer to the actual kernel. -/
theorem GeometricJumpRuntimeLowerTail (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (Goal : State → Prop) (a b eta Delta r : ℝ)
    (Ordered : a<b) (PositiveEta : 0<eta) (PositiveDelta : 0<Delta) (PositiveR : 0<r)
    (TargetIff : ∀ x, V x≤a ↔ Goal x)
    (InitiallyAbove : ∀ᵐ x ∂Initial.toMeasure, b≤V x)
    (Absorbing : ∀ x, ∀ᵐ y ∂(Step x).toMeasure, V x≤a → V y≤a)
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
  let S : Finset ℝ := Finset.univ.image V
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite V).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → State) : X j Path∈S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have InitialPaths : ∀ᵐ Path ∂μ, b≤X 0 Path := by
    have InitialMap : ∀ᵐ x ∂(PathMeasure Step Initial).map (fun Path : ℕ → State => Path 0), b≤V x := by
      rw [PathMeasureInitial]
      exact InitiallyAbove
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable InitialMap
  have Absorbs (j : ℕ) : ∀ᵐ Path ∂μ, X j Path≤a → X (j+1) Path≤a :=
    PathMeasureFollowsTransition Step Initial (fun x y => V x≤a → V y≤a) Absorbing j
  have LocalTail (j : ℕ) (s : ℝ) (_Member : s∈S) (Above : a<s)
      (Positive : 0<μ (StateEvent X j s)) (k : ℕ) :
      (cond μ (StateEvent X j s)) {Path | (k : ℝ)≤|X (j+1) Path-X j Path|} ≤
        ENNReal.ofReal (r/(1+eta)^k) := by
    exact PathMeasureConditionalTransitionProbabilityUpperBound Step Initial j {x | V x=s}
      (fun x y => (k : ℝ)≤|V y-V x|) (r/(1+eta)^k)
      (div_nonneg PositiveR.le (pow_nonneg (by linarith) k)) Positive (by
        intro x Equal
        change V x=s at Equal
        exact JumpTail x (by rwa [Equal]) k)
  have LocalDrift (j : ℕ) (s : ℝ) (_Member : s∈S) (Above : a<s) (Below : s<b)
      (Positive : 0<μ (StateEvent X j s)) : StateDrift μ X j s ≤ -Delta := by
    rw [StateDrift, EventConditionalExpectationEqCondIntegral]
    exact PathMeasureConditionalTransitionIntegralUpperBound Step Initial j {x | V x=s}
      (fun x y => V x-V y) (-Delta) Positive (by
        intro x Equal
        change V x=s at Equal
        exact Drift x (by rwa [Equal]) (by rwa [Equal]))
  have Bound := GeometricJumpNegativeDriftTail μ X S a b eta Delta r Ordered PositiveEta
    PositiveDelta PositiveR Coordinates Values InitialPaths Absorbs LocalTail LocalDrift t
  have Events : {Path | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j Path) ≤ (t : WithTop ℕ)} =
      {Path | FirstHittingTime Goal Path ≤ (t : WithTop ℕ)} := by
    ext Path
    simp only [Set.mem_ofPred_eq, FirstHittingTimeLeIff, X, TargetIff]
  rw [Events] at Bound
  exact Bound

end
end ECTheoryLib.Tools.Runtime
