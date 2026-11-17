import ECTheoryLib.Analysis.LeadingOnes.RLS.ConditionalLevelLaw
import ECTheoryLib.Analysis.LeadingOnes.RLS.UniformInitialization
import ECTheoryLib.Operators.Mutation.BitFlipTuple
import ECTheoryLib.Probability.Processes.ConditionalTransition

/-!
# Exact translated drift of uniform-start RLS on LeadingOnes

For Example 2.3.2, set Y=0 at the optimum and Y=n-LO+1 elsewhere. Only the
first-zero mutation changes Y. Recursion by the head bit shows that its gain,
averaged uniformly over each nonoptimal level, is exactly two. Uniform coordinate
choice divides this by n. The previously proved conditional level law transfers
this calculation to every positive current-fitness event of the actual process.

The translated value determines fitness, so the same equality holds on the
nonzero potential-level events required by additive drift. No individual-state
constant drift, full-history suffix uniformity, or projected Markov premise
is assumed. Null events are excluded from the drift's probabilistic statement.
-/


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes
noncomputable section

theorem TranslatedPotentialByValue {n : ℕ} (x : Bits n) :
    TranslatedPotential x = if LeadingOnes x = n then 0 else (n : ℝ) - LeadingOnes x + 1 := by
  have SameTarget := LeadingOnesEqNIffEqAllOnes x
  have Difference : Potential x = (n : ℝ) - LeadingOnes x := Nat.cast_sub (LeadingOnesLeN x)
  simp only [TranslatedPotential, SameTarget, Difference]

theorem TranslatedPotentialConsTrue {n : ℕ} (x : Bits n) :
    TranslatedPotential (Fin.cons true x) = TranslatedPotential x := by
  rw [TranslatedPotentialByValue, TranslatedPotentialByValue, LeadingOnesConsTrue]
  have Same : 1 + LeadingOnes x = n+1 ↔ LeadingOnes x = n := by omega
  simp only [Same, Nat.cast_add, Nat.cast_one]
  split
  · rfl
  · ring

theorem TranslatedPotentialConsFalse {n : ℕ} (x : Bits n) :
    TranslatedPotential (Fin.cons false x) = (n : ℝ) + 2 := by
  rw [TranslatedPotentialByValue, LeadingOnesConsFalse, if_neg (by omega)]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  ring

theorem TranslatedPotentialTotal (n : ℕ) :
    (∑ x : Bits n, TranslatedPotential x) = (n : ℝ) * (2 : ℝ)^n := by
  have Mean := UniformTranslatedPotentialExpectation n
  rw [PMF.integral_eq_sum] at Mean
  simp only [RLSInitProbability, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, smul_eq_mul, ← Finset.mul_sum] at Mean
  have Nonzero : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have Scaled := congrArg (fun z : ℝ => (2 : ℝ)^n * z) Mean
  rw [← mul_assoc, mul_inv_cancel₀ Nonzero, one_mul] at Scaled
  rw [Scaled, mul_comm]

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes
noncomputable section

/-- The translated-potential gain if the first zero is chosen; zero at the optimum. -/
def FirstZeroGain {n : ℕ} (x : Bits n) : ℝ :=
  if Within : LeadingOnes x < n then
    TranslatedPotential x - TranslatedPotential (OnebitMutation x ⟨LeadingOnes x, Within⟩)
  else 0

theorem FirstZeroGainConsFalse {n : ℕ} (x : Bits n) :
    FirstZeroGain (Fin.cons false x) = (n : ℝ) + 2 - TranslatedPotential x := by
  have Within : LeadingOnes (Fin.cons false x) < n+1 := by rw [LeadingOnesConsFalse]; omega
  have Position : (⟨LeadingOnes (Fin.cons false x), Within⟩ : Fin (n+1)) = 0 := by
    apply Fin.ext
    exact LeadingOnesConsFalse x
  rw [FirstZeroGain, dif_pos Within, Position, OnebitMutationConsZero]
  change TranslatedPotential (Fin.cons false x) - TranslatedPotential (Fin.cons true x) = _
  rw [TranslatedPotentialConsFalse, TranslatedPotentialConsTrue]

theorem FirstZeroGainConsTrue {n : ℕ} (x : Bits n) :
    FirstZeroGain (Fin.cons true x) = FirstZeroGain x := by
  by_cases Within : LeadingOnes x < n
  · have ExtendedWithin : LeadingOnes (Fin.cons true x) < n+1 := by rw [LeadingOnesConsTrue]; omega
    have Position : (⟨LeadingOnes (Fin.cons true x), ExtendedWithin⟩ : Fin (n+1)) =
        (⟨LeadingOnes x, Within⟩ : Fin n).succ := by
      apply Fin.ext
      change LeadingOnes (Fin.cons true x) = LeadingOnes x + 1
      rw [LeadingOnesConsTrue]
      omega
    unfold FirstZeroGain
    rw [dif_pos ExtendedWithin, dif_pos Within, Position, OnebitMutationConsSucc,
      TranslatedPotentialConsTrue, TranslatedPotentialConsTrue]
  · have ExtendedOutside : ¬ LeadingOnes (Fin.cons true x) < n+1 := by rw [LeadingOnesConsTrue]; omega
    unfold FirstZeroGain
    rw [dif_neg ExtendedOutside, dif_neg Within]

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes
noncomputable section

/-- Averaging over a whole nonoptimal level gives gain exactly two when its
first zero is selected. Individual strings can have larger or smaller gains. -/
theorem FirstZeroGainLevelSum (n k : ℕ) (Within : k < n) :
    (∑ x : Bits n, if LeadingOnes x = k then FirstZeroGain x else 0) =
      2 * ∑ x : Bits n, if LeadingOnes x = k then (1 : ℝ) else 0 := by
  classical
  have Split {m : ℕ} (f : Bits (m+1) → ℝ) :
      (∑ x, f x) = (∑ x : Bits m, f (Fin.cons true x)) + ∑ x : Bits m, f (Fin.cons false x) := by
    have Reindex : (∑ x, f x) = ∑ p : Bool × Bits m, f (Fin.cons p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool)) _ _ (fun _ => rfl)).symm
    rw [Reindex, Fintype.sum_prod_type, Fintype.sum_bool]
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      rw [Split, Split]
      have NotZero (x : Bits n) : 1 + LeadingOnes x ≠ 0 := by omega
      simp only [LeadingOnesConsTrue, NotZero, if_false, LeadingOnesConsFalse,
        if_true, Finset.sum_const_zero, zero_add, FirstZeroGainConsFalse]
      rw [Finset.sum_sub_distrib, TranslatedPotentialTotal]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have Card : Fintype.card (Bits n) = 2^n := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [Card, Nat.cast_pow, Nat.cast_ofNat]
      ring
  | succ k Before =>
    cases n with
    | zero => omega
    | succ n =>
      rw [Split, Split]
      have TrueLevel (x : Bits n) : LeadingOnes (Fin.cons true x) = k+1 ↔ LeadingOnes x = k := by
        rw [LeadingOnesConsTrue]
        omega
      have FalseLevel : ¬ (0 : ℕ) = k+1 := by omega
      simp only [TrueLevel, LeadingOnesConsFalse, if_neg FalseLevel, Finset.sum_const_zero,
        add_zero, FirstZeroGainConsTrue]
      exact Before n (by omega)

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ECTheoryLib.Problems.LeadingOnes ECTheoryLib.Probability
noncomputable section

theorem TranslatedPotentialEqOfLevel {n : ℕ} (x y : Bits n)
    (Same : LeadingOnes x = LeadingOnes y) : TranslatedPotential x = TranslatedPotential y := by
  rw [TranslatedPotentialByValue, TranslatedPotentialByValue, Same]

/-- Only choosing the first zero changes the translated potential. -/
theorem TranslatedSelectedGain {n : ℕ} (x : Bits n) (i : Fin n) :
    TranslatedPotential x - TranslatedPotential (Update x i) =
      if i.val = LeadingOnes x then FirstZeroGain x else 0 := by
  rw [UpdateByPosition]
  by_cases Before : i.val < LeadingOnes x
  · rw [if_pos Before, if_neg (by omega), sub_self]
  · rw [if_neg Before]
    by_cases AtZero : i.val = LeadingOnes x
    · have Within : LeadingOnes x < n := by rw [← AtZero]; exact i.isLt
      have Position : i = ⟨LeadingOnes x, Within⟩ := Fin.ext AtZero
      rw [if_pos AtZero, FirstZeroGain, dif_pos Within, Position]
    · rw [if_neg AtZero]
      have SameValue := SuffixFlipValue x i (by omega)
      rw [TranslatedPotentialEqOfLevel _ _ SameValue, sub_self]

/-- Exact per-string drift; free riders are retained in FirstZeroGain. -/
theorem TranslatedOneStepDrift {n : ℕ} (PositiveLength : 0 < n) (x : Bits n) :
    (∫ y, TranslatedPotential x - TranslatedPotential y ∂(Step PositiveLength x).toMeasure) =
      (n : ℝ)⁻¹ * FirstZeroGain x := by
  classical
  rw [Step, RLSStepEqUniformUpdate, PMFIntegralMap, PMF.integral_eq_sum]
  simp only [smul_eq_mul, UniformBitIndexProbability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [TranslatedSelectedGain]
  by_cases Within : LeadingOnes x < n
  · let j : Fin n := ⟨LeadingOnes x, Within⟩
    have SameIndex (i : Fin n) : i.val = LeadingOnes x ↔ i = j := by
      constructor
      · intro Same
        exact Fin.ext Same
      · intro Same
        exact congrArg Fin.val Same
    simp only [SameIndex, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have NoIndex (i : Fin n) : i.val ≠ LeadingOnes x := by
      have Bound := i.isLt
      omega
    simp only [NoIndex, if_false, Finset.sum_const_zero, FirstZeroGain, dif_neg Within]

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Problems.LeadingOnes ECTheoryLib.Probability
noncomputable section

/-- Uniform initialization puts positive mass on every feasible fitness level. -/
theorem UniformLevelPositive {n : ℕ} (k : ℕ) (Within : k ≤ n) :
    0 < (RLSInit n).toMeasure {x | LeadingOnes x = k} := by
  have Atom : 0 < (RLSInit n).toMeasure {PrefixOnes n k} := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]
    exact ENNReal.inv_pos.mpr (by finiteness)
  apply Atom.trans_le
  apply measure_mono
  intro x InSingleton
  rw [Set.mem_singleton_iff] at InSingleton
  change LeadingOnes x = k
  rw [InSingleton, LeadingOnesPrefixOnes Within]

/-- The unnormalized level integral retains the level's probability mass. -/
theorem UniformLevelGainIntegral (n k : ℕ) (Within : k < n) :
    (∫ x in {x | LeadingOnes x = k}, FirstZeroGain x ∂(RLSInit n).toMeasure) =
      2 * (RLSInit n).toMeasure.real {x | LeadingOnes x = k} := by
  classical
  let A : Set (Bits n) := {x | LeadingOnes x = k}
  have AMeasurable : MeasurableSet A := (Set.to_countable _).measurableSet
  have MassFormula : (RLSInit n).toMeasure.real A =
      ((2 : ℝ)^n)⁻¹ * ∑ x : Bits n, if LeadingOnes x = k then (1 : ℝ) else 0 := by
    calc
      _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂(RLSInit n).toMeasure := by
        rw [integral_indicator_const _ AMeasurable, smul_eq_mul, mul_one]
      _ = _ := by
        rw [PMF.integral_eq_sum]
        simp only [RLSInitProbability, ENNReal.toReal_inv, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, smul_eq_mul, Set.indicator_apply, A, Set.mem_ofPred_eq]
        rw [← Finset.mul_sum]
  change (∫ x in A, FirstZeroGain x ∂(RLSInit n).toMeasure) = 2 * (RLSInit n).toMeasure.real A
  rw [← integral_indicator AMeasurable, PMF.integral_eq_sum, MassFormula]
  simp only [RLSInitProbability, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, smul_eq_mul, Set.indicator_apply, A, Set.mem_ofPred_eq]
  rw [← Finset.mul_sum, FirstZeroGainLevelSum n k Within]
  ring

/-- The genuine transition averaged over a uniform nonoptimal level has drift 2/n. -/
theorem UniformLevelTranslatedDrift {n : ℕ} (PositiveLength : 0 < n) (k : ℕ) (Within : k < n) :
    (∫ x, (∫ y, TranslatedPotential x - TranslatedPotential y ∂(Step PositiveLength x).toMeasure)
      ∂cond (RLSInit n).toMeasure {x | LeadingOnes x = k}) = 2 / (n : ℝ) := by
  simp_rw [TranslatedOneStepDrift]
  rw [integral_const_mul, ProbabilityTheory.cond, integral_smul_measure,
    UniformLevelGainIntegral n k Within]
  have Nonzero : (RLSInit n).toMeasure.real {x | LeadingOnes x = k} ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.toReal_pos (UniformLevelPositive k Within.le).ne' (measure_ne_top _ _)
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  change (n : ℝ)⁻¹ * (((RLSInit n).toMeasure.real {x | LeadingOnes x = k})⁻¹ *
    (2 * (RLSInit n).toMeasure.real {x | LeadingOnes x = k})) = _
  field_simp

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Current-fitness conditioning uses the true next-step kernel and the proved
conditional state law; no projected Markov assumption is introduced. -/
theorem UniformPathLevelTransitionIntegral {n : ℕ} (PositiveLength : 0 < n)
    (t k : ℕ) (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | LeadingOnes (Path t) = k} ≠ 0) (f : Bits n → Bits n → ℝ) :
    (∫ Path, f (Path t) (Path (t+1))
      ∂cond (PathMeasure (Step PositiveLength) (RLSInit n)) {Path | LeadingOnes (Path t) = k}) =
      ∫ x, (∫ y, f x y ∂(Step PositiveLength x).toMeasure)
        ∂cond (RLSInit n).toMeasure {x | LeadingOnes x = k} := by
  have FinitePositive : (Evolve (Step PositiveLength) (RLSInit n) t).toMeasure
      {x | LeadingOnes x = k} ≠ 0 := by
    have Event := PathMeasureCoordinateEvent (Step PositiveLength) (RLSInit n) t
      {x | LeadingOnes x = k}
    exact Event.symm ▸ Positive
  have Bridge := PathMeasureConditionalTransitionIntegral (Step PositiveLength) (RLSInit n) t
    {x | LeadingOnes x = k} f
  simp only [Set.mem_ofPred_eq] at Bridge
  rw [Bridge]
  rw [ConditionalLevelLawOfSymmetry _ (UniformRunSuffixSymmetric PositiveLength t) k FinitePositive]

/-- The book's translated potential has exact drift 2/n on every positive
nonoptimal current-fitness event of the actual uniform-start trajectory. -/
theorem UniformPathLevelTranslatedDrift {n : ℕ} (PositiveLength : 0 < n)
    (t k : ℕ) (Within : k < n) (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | LeadingOnes (Path t) = k} ≠ 0) :
    (∫ Path, TranslatedPotential (Path t) - TranslatedPotential (Path (t+1))
      ∂cond (PathMeasure (Step PositiveLength) (RLSInit n)) {Path | LeadingOnes (Path t) = k}) =
      2 / (n : ℝ) := by
  rw [UniformPathLevelTransitionIntegral PositiveLength t k Positive
    (fun x y => TranslatedPotential x - TranslatedPotential y)]
  exact UniformLevelTranslatedDrift PositiveLength k Within

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes

namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Problems.LeadingOnes ECTheoryLib.Probability
noncomputable section

theorem TranslatedPotentialNonnegative {n : ℕ} (x : Bits n) : 0 ≤ TranslatedPotential x := by
  unfold TranslatedPotential
  split
  · exact le_rfl
  · have Nonnegative := PotentialNonnegative x
    linarith

theorem TranslatedPotentialZeroIffTarget {n : ℕ} (x : Bits n) :
    TranslatedPotential x = 0 ↔ x = AllOnes n := by
  by_cases Target : x = AllOnes n
  · constructor
    · intro _Zero
      exact Target
    · intro _Target
      rw [TranslatedPotential, if_pos Target]
  · have Nonnegative := PotentialNonnegative x
    rw [TranslatedPotential, if_neg Target]
    constructor
    · intro Zero
      linarith
    · intro Contradiction
      exact False.elim (Target Contradiction)

theorem TranslatedPotentialEqualIffLevel {n : ℕ} (x y : Bits n) :
    TranslatedPotential x = TranslatedPotential y ↔ LeadingOnes x = LeadingOnes y := by
  constructor
  · intro Same
    by_cases XTarget : x = AllOnes n
    · have XZero := (TranslatedPotentialZeroIffTarget x).mpr XTarget
      have YTarget := (TranslatedPotentialZeroIffTarget y).mp (Same.symm.trans XZero)
      rw [XTarget, YTarget]
    · by_cases YTarget : y = AllOnes n
      · have YZero := (TranslatedPotentialZeroIffTarget y).mpr YTarget
        exact False.elim (XTarget ((TranslatedPotentialZeroIffTarget x).mp (Same.trans YZero)))
      · have XNotFull : LeadingOnes x ≠ n := fun Equal => XTarget ((LeadingOnesEqNIffEqAllOnes x).mp Equal)
        have YNotFull : LeadingOnes y ≠ n := fun Equal => YTarget ((LeadingOnesEqNIffEqAllOnes y).mp Equal)
        rw [TranslatedPotentialByValue, if_neg XNotFull,
          TranslatedPotentialByValue, if_neg YNotFull] at Same
        have RealEqual : (LeadingOnes x : ℝ) = LeadingOnes y := by linarith
        exact_mod_cast RealEqual
  · intro Same
    exact TranslatedPotentialEqOfLevel x y Same

/-- The state-event drift interface required by both additive drift theorems. -/
theorem UniformTranslatedStateDrift {n : ℕ} (PositiveLength : 0 < n) (t : ℕ) (s : ℝ)
    (Nonzero : s ≠ 0)
    (Positive : 0 < (PathMeasure (Step PositiveLength) (RLSInit n))
      (StateEvent (fun t Path => TranslatedPotential (Path t)) t s)) :
    StateDrift (PathMeasure (Step PositiveLength) (RLSInit n))
      (fun t Path => TranslatedPotential (Path t)) t s = 2 / (n : ℝ) := by
  obtain ⟨Witness, WitnessValue⟩ := nonempty_of_measure_ne_zero Positive.ne'
  change TranslatedPotential (Witness t) = s at WitnessValue
  let k := LeadingOnes (Witness t)
  have Within : k < n := by
    have Bound := LeadingOnesLeN (Witness t)
    have NotFull : LeadingOnes (Witness t) ≠ n := by
      intro Full
      have Target := (LeadingOnesEqNIffEqAllOnes (Witness t)).mp Full
      have Zero := (TranslatedPotentialZeroIffTarget (Witness t)).mpr Target
      exact Nonzero (WitnessValue.symm.trans Zero)
    exact lt_of_le_of_ne Bound NotFull
  have EventEqual : StateEvent (fun t (Path : ℕ → Bits n) => TranslatedPotential (Path t)) t s =
      {Path | LeadingOnes (Path t) = k} := by
    ext Path
    change TranslatedPotential (Path t) = s ↔ LeadingOnes (Path t) = k
    rw [← WitnessValue]
    exact TranslatedPotentialEqualIffLevel _ _
  rw [StateDrift, EventConditionalExpectationEqCondIntegral, EventEqual]
  apply UniformPathLevelTranslatedDrift PositiveLength t k Within
  rw [← EventEqual]
  exact Positive.ne'

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
