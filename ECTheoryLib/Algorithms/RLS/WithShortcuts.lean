import ECTheoryLib.Algorithms.RLS
import ECTheoryLib.Probability.PMF.FinitePMF
import Mathlib.Probability.Distributions.Bernoulli

/-!
An actual shortcut branch followed otherwise by the complete existing RLS step.
The target is prescribed by this algorithm; each branch counts one update round.
No optimum property or termination assumption is part of the generic definition.
-/
namespace ECTheoryLib.Algorithms.RLSWithShortcuts
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval Classical
noncomputable section

def ShortcutProbability {n : ℕ} (PositiveLength : 0 < n) : I :=
  ⟨1 / (n : ℝ), by
    constructor
    · positivity
    · exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by exact_mod_cast Nat.succ_le_of_lt PositiveLength : (1 : ℝ) ≤ n)).trans (by norm_num)⟩

theorem ShortcutProbabilityPositive {n : ℕ} (PositiveLength : 0 < n) :
    0 < (ShortcutProbability PositiveLength : ℝ) :=
  one_div_pos.mpr (Nat.cast_pos.mpr PositiveLength)

def Step {n : ℕ} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Target x : Bits n) : PMF (Bits n) :=
  (bernoulliMeasure true false (ShortcutProbability PositiveLength)).toPMF.bind
    (fun Shortcut => if Shortcut then PMF.pure Target else RLSStep PositiveLength NotWorse x)

private theorem CoinReal {n : ℕ} (PositiveLength : 0 < n) (b : Bool) :
    ((bernoulliMeasure true false (ShortcutProbability PositiveLength)).toPMF b).toReal =
      if b then (1 / (n : ℝ)) else 1 - 1 / (n : ℝ) := by
  change (bernoulliMeasure true false (ShortcutProbability PositiveLength)).real {b} = _
  rw [bernoulliMeasure_real_apply _ (measurableSet_singleton b)]
  cases b <;> simp [ShortcutProbability]

/-- Signed expectation on the actual two branches; the ordinary branch keeps all coordinates. -/
theorem StepIntegral {n : ℕ} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Target x : Bits n) (f : Bits n → ℝ) :
    (∫ y, f y ∂(Step PositiveLength NotWorse Target x).toMeasure) =
      (1 / (n : ℝ)) * f Target + (1 - 1 / (n : ℝ)) *
        (∫ y, f y ∂(RLSStep PositiveLength NotWorse x).toMeasure) := by
  rw [Step, PMFIntegralBind, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.toMeasure_pure, integral_dirac, CoinReal]

/-- The same mixture law for every measurable event, including the target event. -/
theorem StepEventProbability {n : ℕ} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Target x : Bits n) (A : Set (Bits n)) :
    (Step PositiveLength NotWorse Target x).toMeasure.real A =
      (1 / (n : ℝ)) * (if Target ∈ A then 1 else 0) + (1 - 1 / (n : ℝ)) *
        (RLSStep PositiveLength NotWorse x).toMeasure.real A := by
  classical
  have Formula := StepIntegral PositiveLength NotWorse Target x (A.indicator (fun _ => 1))
  have EventIntegral (p : PMF (Bits n)) :
      (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂p.toMeasure) = p.toMeasure.real A :=
    integral_indicator_one (Set.to_countable A).measurableSet
  rw [EventIntegral, EventIntegral] at Formula
  simpa only [Set.indicator_apply] using Formula

/-- Explicit probability of each successor; all mass from rejected ordinary proposals remains. -/
theorem StepProbabilityReal {n : ℕ} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Target x y : Bits n) :
    (Step PositiveLength NotWorse Target x y).toReal =
      (if Target = y then (1 / (n : ℝ)) else 0) + (1 - 1 / (n : ℝ)) *
        (RLSStep PositiveLength NotWorse x y).toReal := by
  classical
  have Formula := StepEventProbability PositiveLength NotWorse Target x {y}
  simpa only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y),
    Set.mem_singleton_iff, mul_ite, mul_one, mul_zero] using Formula

theorem StepTargetProbabilityLower {n : ℕ} (PositiveLength : 0 < n)
    (NotWorse : Bits n → Bits n → Prop) [DecidableRel NotWorse]
    (Target x : Bits n) :
    (1 / (n : ℝ)) ≤ (Step PositiveLength NotWorse Target x).toMeasure.real {Target} := by
  rw [StepEventProbability]
  simp only [Set.mem_singleton_iff, if_true, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (ShortcutProbability PositiveLength).2.2)
    ENNReal.toReal_nonneg)

end
end ECTheoryLib.Algorithms.RLSWithShortcuts

