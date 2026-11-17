import ECTheoryLib.Tools.Drift.ExponentialLowerTail
import ECTheoryLib.Analysis.OneMax.RLS.ExponentialTailBounds
import ECTheoryLib.Analysis.OneMax.RLS.UniformRuntimeBound
import ECTheoryLib.Probability.Processes.PathInvariant

/-!
# Exponential early-hit bounds for actual RLS on OneMax

The shared StochasticProgress path bound limits every reachable zero count
by the initial zero count k. Reusing the exact
conditional exponential moment gives beta = 1 + (exp(lambda)-1)*k/n >= 1.
The general zero-target theorem then bounds Pr[T <= t] by beta^t*exp(-lambda*k).
All path, conditional-state, and hitting-time premises are verified below.
Time counts mutation iterations after initialization; initial optimal states
are allowed. This API example does not claim a tight lower-tail estimate.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- An actual RLS early-hit bound, using the initial distance to bound all later success probabilities. -/
theorem FixedRuntimeExponentialLowerTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (Lambda : ℝ) (NonnegativeLambda : 0 ≤ Lambda) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | FirstHittingTime IsTarget Path ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((1+(Real.exp Lambda-1)*((ZeroCount InitialState : ℝ)/(n : ℝ)))^t*
        Real.exp (-Lambda*(ZeroCount InitialState : ℝ))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X : ℕ → (ℕ → Bits n) → ℝ := fun j Path => Potential (Path j)
  let S : Finset ℝ := Finset.univ.image (Potential (n := n))
  let k : ℝ := (ZeroCount InitialState : ℝ)
  let β := 1+(Real.exp Lambda-1)*(k/(n : ℝ))
  have Coordinates (j : ℕ) : Measurable (X j) :=
    (measurable_of_finite (Potential (n := n))).comp (measurable_pi_apply j)
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have Absorbing : ZeroIsAbsorbing μ X := by
    intro j
    have Nonincrease := PathMeasureFollowsTransition (Step PositiveLength) (PMF.pure InitialState)
      (fun x y => Potential y ≤ Potential x) (StepPotentialNonincreasing PositiveLength) j
    filter_upwards [Nonincrease] with Path Decreases
    intro Zero
    change X (j+1) Path ≤ X j Path at Decreases
    exact le_antisymm (by rw [Zero] at Decreases; exact Decreases) (PotentialNonnegative _)
  have PositiveN : (0 : ℝ) < n := Nat.cast_pos.mpr PositiveLength
  have ExpAtLeastOne : 1 ≤ Real.exp Lambda := Real.one_le_exp_iff.mpr NonnegativeLambda
  have OneLeBeta : 1 ≤ β := by
    have Nonnegative := mul_nonneg (sub_nonneg.mpr ExpAtLeastOne)
      (div_nonneg (show 0 ≤ k from Nat.cast_nonneg _) PositiveN.le)
    change 1 ≤ 1+(Real.exp Lambda-1)*(k/(n : ℝ))
    linarith
  have Moment (j : ℕ) (s : ℝ) (_InS : s ∈ S) (_Nonzero : s ≠ 0)
      (PositiveEvent : 0 < μ (StateEvent X j s)) :
      EventConditionalExpectation μ (fun Path => Real.exp (Lambda*(id (X j Path)-id (X (j+1) Path))))
        (StateEvent X j s) ≤ β := by
    let ν := cond μ (StateEvent X j s)
    have ConditionalProbability : IsProbabilityMeasure ν := cond_isProbabilityMeasure PositiveEvent.ne'
    have Current : ∀ᵐ Path ∂ν, X j Path=s := ae_cond_mem (StateEventMeasurable X j s (Coordinates j))
    have Reachable : ∀ᵐ Path ∂ν, X j Path ≤ k :=
      cond_absolutelyContinuous.ae_le (PathPotentialLeInitial PositiveLength InitialState j)
    have StateBound : s ≤ k := by
      obtain ⟨Path, Bound, Equal⟩ := (Reachable.and Current).exists
      rw [Equal] at Bound
      exact Bound
    have Exact := PathExponentialDecreaseMoment PositiveLength (PMF.pure InitialState) j s (-Lambda) PositiveEvent
    have Same : (fun Path : ℕ → Bits n => Real.exp (-Lambda*(Potential (Path (j+1))-Potential (Path j))))=
        (fun Path => Real.exp (Lambda*(id (X j Path)-id (X (j+1) Path)))) := by
      funext Path
      congr 1
      dsimp only [X, id_eq]
      ring
    rw [Same, neg_neg] at Exact
    rw [Exact]
    change 1+(Real.exp Lambda-1)*(s/(n : ℝ)) ≤ 1+(Real.exp Lambda-1)*(k/(n : ℝ))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right StateBound PositiveN.le) (sub_nonneg.mpr ExpAtLeastOne))
  have Initial : ∀ᵐ Path ∂μ, X 0 Path=k := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path AtInitial
    change Potential (Path 0)=k
    rw [AtInitial]
    rfl
  have Bound := ExponentialDriftLowerTailOfFixedInitial μ X S Lambda k id (fun _ => β)
    Coordinates Values Absorbing rfl (fun _ => OneLeBeta) Moment Initial t
  have Hitting (Path : ℕ → Bits n) : ZeroHittingTime X Path=FirstHittingTime IsTarget Path :=
    ZeroHittingTimeEqRuntime Path
  simp only [id_eq, Finset.prod_const, Finset.card_range] at Bound
  simp_rw [Hitting] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
