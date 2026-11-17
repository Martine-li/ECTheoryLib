import ECTheoryLib.Probability.Processes.Process
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A genuinely unbounded upward-biased random walk

The state is any natural number. Zero absorbs; each positive state moves up
with probability 3/4 and down with probability 1/4. Every higher level is
reachable under the actual iterated kernel, with no upper boundary.
-/

namespace ECTheoryLib.Probability.UnboundedBiasedWalk
open MeasureTheory ProbabilityTheory
open scoped unitInterval
noncomputable section

/-- An upward-biased walk on all natural numbers, absorbed only at zero.
There is no upper boundary or reflecting cap. -/
def Step (x : ℕ) : PMF ℕ :=
  if x=0 then PMF.pure 0 else
    (bernoulliMeasure (x+1) (x-1) (⟨3/4,by norm_num⟩ : I)).toPMF

def Potential (x : ℕ) : ℝ := (x : ℝ)

theorem StepZeroAbsorbing (x : ℕ) :
    ∀ᵐ y ∂(Step x).toMeasure, Potential x≤0 → Potential y≤0 := by
  by_cases Zero : x=0
  · rw [Step,if_pos Zero,PMF.toMeasure_pure]
    filter_upwards [ae_eq_dirac (fun y : ℕ => y)] with y Equal
    intro _
    change y=0 at Equal
    simp only [Equal,Potential,Nat.cast_zero,le_refl]
  · exact ae_of_all _ (fun _ Below => by
      have ZeroReal : (x : ℝ)=0 := le_antisymm Below (Nat.cast_nonneg x)
      exact (Zero (Nat.cast_eq_zero.mp ZeroReal)).elim)

theorem StepAbsoluteJumpBound (x : ℕ) :
    ∀ᵐ y ∂(Step x).toMeasure, |Potential y-Potential x|≤1 := by
  by_cases Zero : x=0
  · rw [Step,if_pos Zero,PMF.toMeasure_pure]
    filter_upwards [ae_eq_dirac (fun y : ℕ => y)] with y Equal
    change y=0 at Equal
    simp only [Zero,Equal,Potential,Nat.cast_zero,sub_self,abs_zero,zero_le_one]
  · rw [Step,if_neg Zero,Measure.toPMF_toMeasure]
    have Supported : ∀ᵐ y ∂bernoulliMeasure (x+1) (x-1) (⟨3/4,by norm_num⟩ : I), y=x+1 ∨ y=x-1 := by
      rw [bernoulliMeasure_def]
      apply ae_add_measure_iff.mpr
      constructor
      · exact Measure.ae_smul_measure ((ae_eq_dirac (fun y : ℕ => y)).mono (fun _ Equal => Or.inl Equal)) _
      · exact Measure.ae_smul_measure ((ae_eq_dirac (fun y : ℕ => y)).mono (fun _ Equal => Or.inr Equal)) _
    filter_upwards [Supported] with y InSupport
    have AtLeastOne : 1≤x := Nat.one_le_iff_ne_zero.mpr Zero
    rcases InSupport with Up | Down
    · rw [Up]
      simp only [Potential,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,abs_one,le_refl]
    · rw [Down]
      simp only [Potential,Nat.cast_sub AtLeastOne,Nat.cast_one,sub_sub_cancel_left,abs_neg,abs_one,le_refl]

theorem OneStepIncrement (x : ℕ) :
    (∫ y, Potential y-Potential x ∂(Step x).toMeasure) = if x=0 then 0 else (1/2 : ℝ) := by
  by_cases Zero : x=0
  · rw [Step,if_pos Zero,PMF.toMeasure_pure,integral_dirac,Zero,sub_self]
    simp
  · rw [Step,if_neg Zero,Measure.toPMF_toMeasure,integral_bernoulliMeasure]
    have AtLeastOne : 1≤x := Nat.one_le_iff_ne_zero.mpr Zero
    simp only [Potential,Nat.cast_add,Nat.cast_one,Nat.cast_sub AtLeastOne,smul_eq_mul,if_neg Zero]
    ring

theorem OneStepAbsoluteExponentialMoment (x : ℕ) (q : ℝ) :
    (∫ y, Real.exp (q*|Potential y-Potential x|) ∂(Step x).toMeasure) =
      if x=0 then 1 else Real.exp q := by
  by_cases Zero : x=0
  · rw [Step,if_pos Zero,PMF.toMeasure_pure,integral_dirac,Zero,sub_self,abs_zero,mul_zero,Real.exp_zero]
    simp
  · rw [Step,if_neg Zero,Measure.toPMF_toMeasure,integral_bernoulliMeasure]
    have AtLeastOne : 1≤x := Nat.one_le_iff_ne_zero.mpr Zero
    simp only [Potential,Nat.cast_add,Nat.cast_one,Nat.cast_sub AtLeastOne,smul_eq_mul,
      add_sub_cancel_left,sub_sub_cancel_left,abs_one,abs_neg,mul_one,if_neg Zero]
    ring

theorem OneStepLogTwoMoment (x : ℕ) (Positive : 0<x) :
    (∫ y, Real.exp (-Real.log 2*(Potential y-Potential x)) ∂(Step x).toMeasure) = (7/8 : ℝ) := by
  rw [Step,if_neg (Nat.ne_of_gt Positive),Measure.toPMF_toMeasure,integral_bernoulliMeasure]
  have AtLeastOne : 1≤x := Positive
  simp only [Potential,Nat.cast_add,Nat.cast_one,Nat.cast_sub AtLeastOne,smul_eq_mul,
    add_sub_cancel_left,sub_sub_cancel_left,mul_one,mul_neg_one,neg_neg]
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  norm_num

/-- The potential domain itself has no finite range. The new analysis does
not certify unboundedness merely by choosing an infinite ambient state type. -/
theorem PotentialHasNoFiniteRange : ¬∃ S : Finset ℝ, ∀ x, Potential x∈S := by
  rintro ⟨S,Values⟩
  have FiniteRange : (Set.range Potential).Finite := S.finite_toSet.subset (by
    rintro _ ⟨x,rfl⟩
    exact Values x)
  have Injective : Function.Injective Potential := by
    intro x y Equal
    exact Nat.cast_injective Equal
  exact (Set.infinite_range_of_injective Injective).not_finite FiniteRange

theorem UpwardStepPossible (x : ℕ) (Positive : 0<x) : x+1∈(Step x).support := by
  rw [PMF.mem_support_iff,Step,if_neg (Nat.ne_of_gt Positive),Measure.toPMF_apply,
    bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      (by simp) (by simp only [Set.mem_singleton_iff]; omega)]
  apply ENNReal.coe_ne_zero.mpr
  intro Zero
  have Coe := congrArg (fun r : NNReal => (r : ℝ)) Zero
  change (3/4 : ℝ)=0 at Coe
  norm_num at Coe

/-- Every higher level has positive mass after sufficiently many actual
transitions, so the walk cannot be confined to a common finite range. -/
theorem HigherLevelReachable (x : ℕ) (Positive : 0<x) (t : ℕ) :
    x+t∈(Evolve Step (PMF.pure x) t).support := by
  induction t with
  | zero => simp [Evolve]
  | succ t Previous =>
    rw [Evolve,PMF.mem_support_bind_iff]
    refine ⟨x+t,Previous,?_⟩
    simpa only [Nat.add_assoc] using UpwardStepPossible (x+t) (by omega)

end
end ECTheoryLib.Probability.UnboundedBiasedWalk
