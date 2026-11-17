import ECTheoryLib.Analysis.LeadingOnes.RLS.Model
import ECTheoryLib.Problems.LOTZGeometry
import ECTheoryLib.Probability.PMF.FiniteProgress

/-!
# Actual one-step progress of RLS on LeadingOnes

The first zero is selected with probability 1/n. Its flip extends the prefix
by at least one, and every other accepted update has nonnegative progress.
This proves the lower drift bound from Example 2.3.2, pp. 97-98. It holds for
every fixed state, without assuming a uniformly distributed unseen suffix.
The existing FirstZeroBit property is reused from LOTZGeometry; its proof
depends only on the longest-prefix definition.
-/

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Weak elitism makes the prefix deficit nonincreasing, including neutral moves. -/
theorem SelectedPotentialLe {n : ℕ} (x y : Bits n) :
    Potential (ElitistSelect (Problems.MaxNotWorse LeadingOnes) x y) ≤ Potential x := by
  unfold ElitistSelect
  by_cases Accept : Problems.MaxNotWorse LeadingOnes y x
  · rw [if_pos Accept]
    change LeadingOnes x ≤ LeadingOnes y at Accept
    exact Nat.cast_le.mpr (Nat.sub_le_sub_left Accept n)
  · rw [if_neg Accept]

/-- Flipping the first missing prefix bit extends the prefix by at least one. -/
theorem FirstZeroFlipProgress {n : ℕ} (x : Bits n) (Outside : LeadingOnes x < n) :
    LeadingOnes x + 1 ≤ LeadingOnes (OnebitMutation x ⟨LeadingOnes x, Outside⟩) := by
  let i : Fin n := ⟨LeadingOnes x, Outside⟩
  have ZeroBit : x i = false := Problems.LOTZ.FirstZeroBit x Outside
  apply Problems.LeadingOnes.PrefixLeLeadingOnes _ Outside
  intro j InPrefix
  by_cases Equal : j = i
  · rw [Equal, OnebitMutationAt, ZeroBit]
    rfl
  · rw [OnebitMutationAway x i j Equal]
    apply Problems.LeadingOnes.HasLeadingOnesPrefix
    have Different : j.val ≠ LeadingOnes x := fun Eq => Equal (Fin.ext Eq)
    omega

/-- Selection accepts this strict improvement; free riders may decrease deficit further. -/
theorem FirstZeroUpdateProgress {n : ℕ} (x : Bits n) (Outside : LeadingOnes x < n) :
    1 ≤ Potential x - Potential (Update x ⟨LeadingOnes x, Outside⟩) := by
  have Progress := FirstZeroFlipProgress x Outside
  have Accepted : Update x ⟨LeadingOnes x, Outside⟩ = OnebitMutation x ⟨LeadingOnes x, Outside⟩ := by
    apply ElitistSelectAccept
    change LeadingOnes x ≤ LeadingOnes (OnebitMutation x ⟨LeadingOnes x, Outside⟩)
    omega
  rw [Accepted]
  have Bound := Problems.LeadingOnes.LeadingOnesLeN (OnebitMutation x ⟨LeadingOnes x, Outside⟩)
  have NatProgress : Deficit (OnebitMutation x ⟨LeadingOnes x, Outside⟩) + 1 ≤ Deficit x := by
    unfold Deficit
    omega
  have RealProgress : Potential (OnebitMutation x ⟨LeadingOnes x, Outside⟩) + 1 ≤ Potential x := by
    unfold Potential
    exact_mod_cast NatProgress
  linarith

/-- The uniformly selected first zero gives a drift floor of 1/n at every nonoptimum. -/
theorem OneStepDriftLowerBound {n : ℕ} (PositiveLength : 0 < n) (x : Bits n)
    (Nonzero : Potential x ≠ 0) :
    1 / (n : ℝ) ≤ ∫ y, Potential x - Potential y ∂(Step PositiveLength x).toMeasure := by
  have Outside : LeadingOnes x < n := by
    have Upper := Problems.LeadingOnes.LeadingOnesLeN x
    by_contra NotOutside
    have Equal : LeadingOnes x = n := by omega
    apply Nonzero
    simp only [Potential, Deficit, Equal, Nat.sub_self, Nat.cast_zero]
  let i : Fin n := ⟨LeadingOnes x, Outside⟩
  let Progress : Fin n → ℝ := fun j => Potential x - Potential (Update x j)
  have Nonnegative (j : Fin n) : 0 ≤ Progress j :=
    sub_nonneg.mpr (SelectedPotentialLe x (OnebitMutation x j))
  have Bound := PMFIntegralLowerOfPoint (UniformBitIndex n PositiveLength) Progress Nonnegative i
  have Weight : (UniformBitIndex n PositiveLength i).toReal = 1 / (n : ℝ) := by
    rw [UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [Weight] at Bound
  have Useful : 1 ≤ Progress i := FirstZeroUpdateProgress x Outside
  rw [Step, RLSStepEqUniformUpdate, PMFIntegralMap]
  have Contribution : 1 / (n : ℝ) ≤ (1 / (n : ℝ)) * Progress i := by
    have Scaled := mul_le_mul_of_nonneg_left Useful (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    rw [mul_one] at Scaled
    exact Scaled
  exact Contribution.trans Bound

theorem StepPotentialNonincreasing {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    ∀ᵐ y ∂(Step PositiveLength x).toMeasure, Potential y ≤ Potential x := by
  rw [Step, RLSStep]
  apply PMFAEOfSupport
  intro y Supported
  obtain ⟨Candidate, _Possible, Equal⟩ := (PMF.mem_support_map_iff _ _ _).mp Supported
  rw [← Equal]
  exact SelectedPotentialLe x Candidate


end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
