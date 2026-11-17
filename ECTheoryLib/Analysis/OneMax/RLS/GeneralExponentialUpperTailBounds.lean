import ECTheoryLib.Tools.Drift.GeneralExponentialUpperTail
import ECTheoryLib.Analysis.OneMax.RLS.GeneralExponentialLowerTailBounds

/-!
# Strict late-progress bounds for actual RLS on OneMax

Reuse the exact full-history exponential moment at a negative parameter.
Above an integer target a, at least a+1 zeros remain; this lower bound has
the required direction because exp(-lambda)-1 is negative. Time counts
mutation iterations after initialization.
-/

namespace ECTheoryLib.Analysis.RLSOnOneMax
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

/-- Strict general-exponential upper tail for a genuine intermediate target
under the actual fixed-start RLS trajectory measure. -/
theorem FixedProgressStrictExponentialUpperTail {n : ℕ} (PositiveLength : 0 < n)
    (InitialState : Bits n) (a : ℕ) (Lambda : ℝ) (PositiveLambda : 0 < Lambda)
    (InitialAbove : a < ZeroCount InitialState) (t : ℕ) :
    (PathMeasure (Step PositiveLength) (PMF.pure InitialState))
      {Path | (t : WithTop ℕ) < FirstHittingTime (fun x : Bits n => Potential x ≤ (a : ℝ)) Path} <
      ENNReal.ofReal ((1 + (Real.exp (-Lambda) - 1) * (((a + 1 : ℕ) : ℝ) / (n : ℝ))) ^ t *
        Real.exp (Lambda * ((ZeroCount InitialState : ℝ) - (a : ℝ)))) := by
  classical
  let μ := PathMeasure (Step PositiveLength) (PMF.pure InitialState)
  let X := fun j (Path : ℕ → Bits n) => Potential (Path j)
  let F := Filtration.piLE (X := fun _ : ℕ => Bits n)
  let S := Finset.univ.image (Potential (n := n))
  let k : ℝ := ZeroCount InitialState
  let beta := 1 + (Real.exp (-Lambda) - 1) * (((a + 1 : ℕ) : ℝ) / (n : ℝ))
  have AdaptedX : Adapted F X := PathPotentialAdapted Potential
  have Values (j : ℕ) (Path : ℕ → Bits n) : X j Path ∈ S :=
    Finset.mem_image.mpr ⟨Path j, Finset.mem_univ _, rfl⟩
  have PositiveN : 0 < (n : ℝ) := Nat.cast_pos.mpr PositiveLength
  have CountLeN : ZeroCount InitialState ≤ n := Nat.sub_le _ _
  have TargetLeN : a + 1 ≤ n := (Nat.succ_le_iff.mpr InitialAbove).trans CountLeN
  have RatioLeOne : (((a + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 :=
    (div_le_one PositiveN).mpr (by exact_mod_cast TargetLeN)
  have NonpositiveCoefficient : Real.exp (-Lambda) - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr PositiveLambda.le))
  have PositiveBeta : 0 < beta := by
    have Compare := mul_le_mul_of_nonpos_left RatioLeOne NonpositiveCoefficient
    have PositiveExp := Real.exp_pos (-Lambda)
    dsimp [beta]
    nlinarith
  have Initial : ∀ᵐ Path ∂μ, X 0 Path = k := by
    filter_upwards [PathMeasureInitialPure (Step PositiveLength) InitialState] with Path Equal
    change Potential (Path 0) = k
    rw [Equal]
    rfl
  have Sign (v w : ℝ) : (-Lambda) * (v - w) = Lambda * (w - v) := by ring
  have Moment (j : ℕ) : ∀ᵐ Path ∂μ, (a : ℝ) < X j Path →
      (μ[fun u => Real.exp (Lambda * (id (X (j + 1) u) - id (X j u))) | F j]) Path ≤ beta := by
    have Exact := PathConditionalExponentialDecreaseMoment PositiveLength (PMF.pure InitialState) j (-Lambda)
    simp only [Sign] at Exact
    filter_upwards [Exact] with Path Exact
    intro Above
    have Count : a + 1 ≤ ZeroCount (Path j) := by
      apply Nat.succ_le_iff.mpr
      change (a : ℝ) < (ZeroCount (Path j) : ℝ) at Above
      exact_mod_cast Above
    have Lower : (((a + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ Potential (Path j) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by
        change ((a + 1 : ℕ) : ℝ) ≤ (ZeroCount (Path j) : ℝ)
        exact_mod_cast Count) PositiveN.le
    simp only [id_eq]
    rw [Exact]
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_left Lower NonpositiveCoefficient)
  have Bound := StrictGeneralExponentialDriftUpperTailOfFixedInitial μ X F AdaptedX S (a : ℝ) k Lambda id
    (fun _ => beta) Values PositiveLambda (fun _ => PositiveBeta)
    (fun _ _ Above => Above)
    (by change (a : ℝ) < (ZeroCount InitialState : ℝ); exact_mod_cast InitialAbove) Initial Moment t
  have Event : {Path | (t : WithTop ℕ) < FirstHittingTime (fun s : ℝ => s ≤ (a : ℝ)) (fun j => X j Path)} =
      {Path | (t : WithTop ℕ) < FirstHittingTime (fun x : Bits n => Potential x ≤ (a : ℝ)) Path} := by
    ext Path
    change (t : WithTop ℕ) < FirstHittingTime _ _ ↔ (t : WithTop ℕ) < FirstHittingTime _ _
    simp only [← not_le, FirstHittingTimeLeIff, X]
  rw [Event] at Bound
  simpa only [id_eq, Finset.prod_const, Finset.card_range] using Bound

end
end ECTheoryLib.Analysis.RLSOnOneMax
