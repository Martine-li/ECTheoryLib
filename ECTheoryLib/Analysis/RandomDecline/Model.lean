import ECTheoryLib.Probability.PMF.FinitePMF
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Intervals

/-! The actual finite Random Decline kernel. The cutoff, including clipping at N,
is part of the law. Time is counted in transitions after initialization. -/
namespace ECTheoryLib.Analysis.RandomDecline
open MeasureTheory ECTheoryLib.Probability
noncomputable section

def Cutoff {N : ℕ} (a : ℝ) (s : Fin (N + 1)) : ℕ :=
  min ⌊a * (s.val : ℝ)⌋₊ N

theorem CutoffLe {N : ℕ} (a : ℝ) (s : Fin (N + 1)) : Cutoff a s ≤ N :=
  min_le_right _ _

theorem CutoffRealLe {N : ℕ} {a : ℝ} (Nonnegative : 0 ≤ a) (s : Fin (N + 1)) :
    (Cutoff a s : ℝ) ≤ a * (s.val : ℝ) :=
  (Nat.cast_le.mpr (min_le_left _ _)).trans
    (Nat.floor_le (mul_nonneg Nonnegative (Nat.cast_nonneg _)))

@[simp] theorem CutoffZero (N : ℕ) (a : ℝ) : Cutoff a (0 : Fin (N + 1)) = 0 := by
  simp [Cutoff]

def Step {N : ℕ} (a : ℝ) (s : Fin (N + 1)) : PMF (Fin (N + 1)) :=
  (PMF.uniformOfFintype (Fin (Cutoff a s + 1))).map
    (Fin.castLE (Nat.succ_le_succ (CutoffLe a s)))

theorem StepProbability {N : ℕ} (a : ℝ) (s y : Fin (N + 1)) :
    Step a s y = if y.val ≤ Cutoff a s then ((Cutoff a s + 1 : ℕ) : ENNReal)⁻¹ else 0 := by
  classical
  rw [Step, PMF.map_apply, tsum_fintype]
  by_cases Small : y.val ≤ Cutoff a s
  · let k : Fin (Cutoff a s + 1) := ⟨y.val, by omega⟩
    have Compare (j : Fin (Cutoff a s + 1)) :
        y = Fin.castLE (Nat.succ_le_succ (CutoffLe a s)) j ↔ j = k := by
      constructor
      · intro Equal
        apply Fin.ext
        exact (congrArg Fin.val Equal).symm
      · intro Equal
        subst j
        apply Fin.ext
        rfl
    simp_rw [Compare, PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp [Small]
  · have Impossible (j : Fin (Cutoff a s + 1)) :
        y ≠ Fin.castLE (Nat.succ_le_succ (CutoffLe a s)) j := by
      intro Equal
      have Same := congrArg Fin.val Equal
      have Bound := j.isLt
      simp only [Fin.val_castLE] at Same
      omega
    simp [Impossible, Small]

theorem StepProbabilityReal {N : ℕ} (a : ℝ) (s y : Fin (N + 1)) :
    (Step a s y).toReal = if y.val ≤ Cutoff a s then 1 / ((Cutoff a s : ℝ) + 1) else 0 := by
  rw [StepProbability]
  split_ifs
  · simp [ENNReal.toReal_add]
  · rfl

/-- Signed expectation, with precisely one equally weighted term per successor. -/
theorem StepIntegral {N : ℕ} (a : ℝ) (s : Fin (N + 1)) (f : Fin (N + 1) → ℝ) :
    (∫ y, f y ∂(Step a s).toMeasure) =
      (1 / ((Cutoff a s : ℝ) + 1)) * ∑ k : Fin (Cutoff a s + 1),
        f (Fin.castLE (Nat.succ_le_succ (CutoffLe a s)) k) := by
  rw [Step, PMFIntegralMap, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, smul_eq_mul, ENNReal.toReal_add,
    ← Finset.mul_sum, one_div]

theorem StepNatIntegral {N : ℕ} (a : ℝ) (s : Fin (N + 1)) (f : ℕ → ℝ) :
    (∫ y, f y.val ∂(Step a s).toMeasure) =
      (1 / ((Cutoff a s : ℝ) + 1)) * ∑ k ∈ Finset.range (Cutoff a s + 1), f k := by
  rw [StepIntegral]
  congr 1
  exact Fin.sum_univ_eq_sum_range f (Cutoff a s + 1)

theorem StepMean {N : ℕ} (a : ℝ) (s : Fin (N + 1)) :
    (∫ y, (y.val : ℝ) ∂(Step a s).toMeasure) = (Cutoff a s : ℝ) / 2 := by
  rw [StepNatIntegral]
  have SumNat := Finset.sum_range_id_mul_two (Cutoff a s + 1)
  simp only [Nat.add_sub_cancel] at SumNat
  have SumReal : (∑ k ∈ Finset.range (Cutoff a s + 1), (k : ℝ)) * 2 =
      ((Cutoff a s : ℝ) + 1) * (Cutoff a s : ℝ) := by
    have Cast := congrArg (fun n : ℕ => (n : ℝ)) SumNat
    push_cast at Cast
    exact Cast
  have Positive : 0 < (Cutoff a s : ℝ) + 1 := by positivity
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
  field_simp
  nlinarith

theorem SuccessProbability {N : ℕ} (a : ℝ) (s : Fin (N + 1)) :
    (Step a s).toMeasure.real {y | y.val = 0} = 1 / ((Cutoff a s : ℝ) + 1) := by
  have Event : {y : Fin (N + 1) | y.val = 0} = {0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun Zero => Fin.ext Zero, fun Zero => congrArg Fin.val Zero⟩
  rw [Event]
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0)]
  simp [StepProbabilityReal]

theorem StepZero (N : ℕ) (a : ℝ) : Step a (0 : Fin (N + 1)) = PMF.pure 0 := by
  classical
  apply PMF.ext
  intro y
  rw [StepProbability, CutoffZero]
  by_cases Zero : y = 0
  · subst y
    simp
  · have Positive : ¬y.val ≤ 0 := by
      intro Bound
      apply Zero
      apply Fin.ext
      change y.val = 0
      omega
    simp [Positive, PMF.pure_apply, Zero]

theorem StepPreservesZero {N : ℕ} (a : ℝ) (s : Fin (N + 1)) :
    ∀ᵐ y ∂(Step a s).toMeasure, s.val = 0 → y.val = 0 := by
  apply PMFAEOfSupport (Step a s)
  intro y Possible Zero
  have StateZero : s = 0 := Fin.ext Zero
  subst s
  have Target : y = 0 := by simpa [StepZero] using Possible
  exact congrArg Fin.val Target

end
end ECTheoryLib.Analysis.RandomDecline

