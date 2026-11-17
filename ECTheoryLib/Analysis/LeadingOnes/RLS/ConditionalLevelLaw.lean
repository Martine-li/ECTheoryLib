import ECTheoryLib.Analysis.LeadingOnes.RLS.SuffixSymmetry
import ECTheoryLib.Probability.StochasticOrder.StochasticConditioning

/-!
# Conditional current-state laws for uniform-start RLS on LeadingOnes

Preserved suffix-flip symmetry makes all states at a given fitness level equally
likely. On a positive-probability level event, the conditional full state law
therefore equals uniform initialization conditioned on the same level.

The trajectory statement conditions only on current fitness, as required by
Example 2.3.2 and its footnote 9. Conditioning on the complete observed state
or its full history does not preserve this conclusion. Null level events are
excluded from the probability-law statement. No exact runtime is claimed here.
-/


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open ECTheoryLib.Problems.LeadingOnes

/-- Unseen-bit symmetry makes all strings on the same fitness level equiprobable. -/
theorem SuffixSymmetricEqualOnLevel {n : ℕ} (p : PMF (Bits n)) (Symmetric : SuffixSymmetricLaw p)
    (x y : Bits n) (SameLevel : LeadingOnes x = LeadingOnes y) : p x = p y := by
  by_cases Optimal : LeadingOnes x = n
  · have XTarget := (LeadingOnesEqNIffEqAllOnes x).mp Optimal
    have YTarget := (LeadingOnesEqNIffEqAllOnes y).mp (SameLevel.symm.trans Optimal)
    rw [XTarget, YTarget]
  · have Outside : LeadingOnes x < n := lt_of_le_of_ne (LeadingOnesLeN x) Optimal
    let k := LeadingOnes x
    let First : Fin n := ⟨k, Outside⟩
    have ZeroX : x First = false := Problems.LOTZ.FirstZeroBit x Outside
    have ZeroY : y First = false := by
      have YOutside : LeadingOnes y < n := by rw [← SameLevel]; exact Outside
      have Index : First = ⟨LeadingOnes y, YOutside⟩ := Fin.ext SameLevel
      rw [Index]
      exact Problems.LOTZ.FirstZeroBit y YOutside
    have BelowEqual (i : Fin n) (Before : i.val ≤ k) : x i = y i := by
      by_cases Strict : i.val < k
      · rw [HasLeadingOnesPrefix x i Strict, HasLeadingOnesPrefix y i (by rw [← SameLevel]; exact Strict)]
      · have EqualIndex : i = First := Fin.ext (by change i.val = k; omega)
        rw [EqualIndex, ZeroX, ZeroY]
    let Patch (m : ℕ) : Bits n := fun i => if i.val < m then y i else x i
    have PatchMatches (m : ℕ) (i : Fin n) (Before : i.val ≤ k) : Patch m i = x i := by
      dsimp only [Patch]
      by_cases Patched : i.val < m
      · rw [if_pos Patched]
        exact (BelowEqual i Before).symm
      · rw [if_neg Patched]
    have PatchValue (m : ℕ) : LeadingOnes (Patch m) = k := by
      apply LeadingOnesEqOfPrefixAndZero _ First
      · intro i Before
        rw [PatchMatches m i Before.le]
        exact HasLeadingOnesPrefix x i Before
      · rw [PatchMatches m First le_rfl, ZeroX]
    have InitialPatch : Patch 0 = x := by
      funext i
      exact if_neg (Nat.not_lt_zero _)
    have FinalPatch : Patch n = y := by
      funext i
      exact if_pos i.isLt
    have Constant (m : ℕ) : m ≤ n → p (Patch m) = p x := by
      induction m with
      | zero => intro _Bound; rw [InitialPatch]
      | succ m Before =>
        intro Bound
        have Within : m < n := by omega
        let i : Fin n := ⟨m, Within⟩
        have AtIndex : Patch m i = x i := if_neg (Nat.lt_irrefl m)
        have PatchStep : Patch (m+1) = Function.update (Patch m) i (y i) := by
          funext j
          by_cases Equal : j = i
          · subst j
            rw [Function.update_self]
            exact if_pos (Nat.lt_succ_self m)
          · rw [Function.update_of_ne Equal]
            have Different : j.val ≠ m := fun Position => Equal (Fin.ext Position)
            have Compare : (j.val < m+1) ↔ j.val < m := by omega
            dsimp only [Patch]
            simp only [Compare]
        by_cases SameBit : x i = y i
        · have PatchSame : Patch (m+1) = Patch m := by
            rw [PatchStep, ← SameBit, ← AtIndex, Function.update_eq_self]
          rw [PatchSame]
          exact Before (by omega)
        · have After : k < i.val := by
            by_contra NotAfter
            exact SameBit (BelowEqual i (by omega))
          have Complement : y i = !(x i) := by
            cases XBit : x i with
            | false =>
              cases YBit : y i with
              | false => exact False.elim (SameBit (XBit.trans YBit.symm))
              | true => rfl
            | true =>
              cases YBit : y i with
              | false => rfl
              | true => exact False.elim (SameBit (XBit.trans YBit.symm))
          have PatchFlip : Patch (m+1) = OnebitMutation (Patch m) i := by
            rw [PatchStep]
            funext j
            by_cases Equal : j = i
            · subst j
              rw [Function.update_self, OnebitMutationAt, AtIndex, Complement]
            · rw [Function.update_of_ne Equal, OnebitMutationAway (Patch m) i j Equal]
          rw [PatchFlip, Symmetric i (Patch m) (by rw [PatchValue]; exact After)]
          exact Before (by omega)
    have Result := Constant n le_rfl
    rw [FinalPatch] at Result
    exact Result.symm

end ECTheoryLib.Analysis.RLSOnLeadingOnes


namespace ECTheoryLib.Analysis.RLSOnLeadingOnes
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
noncomputable section

/-- Under suffix symmetry, a level's mass is its cardinality times any atom there. -/
theorem SymmetricLevelMass {n : ℕ} (p : PMF (Bits n)) (Symmetric : SuffixSymmetricLaw p)
    (k : ℕ) (x : Bits n) (AtLevel : LeadingOnes x = k) :
    p.toMeasure.real {y | LeadingOnes y = k} =
      ((Finset.univ.filter (fun y : Bits n => LeadingOnes y = k)).card : ℝ) * (p x).toReal := by
  classical
  let S := Finset.univ.filter (fun y : Bits n => LeadingOnes y = k)
  have Event : {y : Bits n | LeadingOnes y = k} = (S : Set (Bits n)) := by
    ext y
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [measureReal_def, Event, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum (fun y _InS => p.apply_ne_top y)]
  have EqualTerms : (∑ y ∈ S, (p y).toReal) = ∑ _y ∈ S, (p x).toReal := by
    apply Finset.sum_congr rfl
    intro y InS
    have YLevel : LeadingOnes y = k := (Finset.mem_filter.mp InS).2
    rw [SuffixSymmetricEqualOnLevel p Symmetric y x (YLevel.trans AtLevel.symm)]
  rw [EqualTerms, Finset.sum_const, nsmul_eq_mul]

/-- Conditioning a symmetric law on a positive fitness level gives the same
complete state law as conditioning the original uniform initialization. -/
theorem ConditionalLevelLawOfSymmetry {n : ℕ} (p : PMF (Bits n)) (Symmetric : SuffixSymmetricLaw p)
    (k : ℕ) (Positive : p.toMeasure {x | LeadingOnes x = k} ≠ 0) :
    cond p.toMeasure {x | LeadingOnes x = k} =
      cond (RLSInit n).toMeasure {x | LeadingOnes x = k} := by
  classical
  let A : Set (Bits n) := {x | LeadingOnes x = k}
  have UniformSymmetric : SuffixSymmetricLaw (RLSInit n) := by
    intro j x _After
    rw [RLSInitProbability, RLSInitProbability]
  obtain ⟨z, InLevel⟩ := nonempty_of_measure_ne_zero Positive
  have UniformPositive : (RLSInit n).toMeasure A ≠ 0 := by
    have PointPositive : 0 < (RLSInit n).toMeasure {z} := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RLSInitProbability]
      exact ENNReal.inv_pos.mpr (by finiteness)
    exact (PointPositive.trans_le (measure_mono (Set.singleton_subset_iff.mpr InLevel))).ne'
  have FirstProbability : IsProbabilityMeasure (cond p.toMeasure A) := cond_isProbabilityMeasure Positive
  have SecondProbability : IsProbabilityMeasure (cond (RLSInit n).toMeasure A) := cond_isProbabilityMeasure UniformPositive
  change cond p.toMeasure A = cond (RLSInit n).toMeasure A
  apply Measure.ext_of_measureReal_singleton
  intro x
  rw [ConditionalSingletonReal, ConditionalSingletonReal]
  by_cases Member : x ∈ A
  · rw [if_pos Member, if_pos Member]
    have CurrentMass := SymmetricLevelMass p Symmetric k x Member
    have UniformMass := SymmetricLevelMass (RLSInit n) UniformSymmetric k x Member
    change p.toMeasure.real A = _ at CurrentMass
    change (RLSInit n).toMeasure.real A = _ at UniformMass
    have MassPositive : 0 < p.toMeasure.real A :=
      ENNReal.toReal_pos Positive (measure_ne_top _ _)
    have AtomNonzero : (p x).toReal ≠ 0 := by
      intro Zero
      rw [CurrentMass, Zero, mul_zero] at MassPositive
      exact lt_irrefl 0 MassPositive
    have UniformAtomNonzero : (RLSInit n x).toReal ≠ 0 := by
      rw [RLSInitProbability, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
      positivity
    rw [CurrentMass, UniformMass]
    simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [mul_comm _ (p x).toReal, mul_comm _ (RLSInit n x).toReal,
      div_mul_cancel_left₀ AtomNonzero, div_mul_cancel_left₀ UniformAtomNonzero]
  · rw [if_neg Member, if_neg Member, zero_div, zero_div]

/-- Conditional current-state law on actual paths. Conditioning is only on the
current fitness value, not on the complete history or on a fixed full string. -/
theorem UniformPathConditionalLevelLaw {n : ℕ} (PositiveLength : 0 < n) (t k : ℕ)
    (Positive : (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | LeadingOnes (Path t) = k} ≠ 0) :
    (cond (PathMeasure (Step PositiveLength) (RLSInit n))
      {Path | LeadingOnes (Path t) = k}).map (fun Path => Path t) =
        cond (RLSInit n).toMeasure {x | LeadingOnes x = k} := by
  have Commutes := ConditionalMap (PathMeasure (Step PositiveLength) (RLSInit n))
    (fun Path => Path t) (measurable_pi_apply t) {x | LeadingOnes x = k}
    (Set.to_countable _).measurableSet
  rw [PathMeasureMarginal] at Commutes
  change (cond (PathMeasure (Step PositiveLength) (RLSInit n))
    {Path | LeadingOnes (Path t) = k}).map (fun Path => Path t) = _ at Commutes
  rw [Commutes]
  apply ConditionalLevelLawOfSymmetry _ (UniformRunSuffixSymmetric PositiveLength t) k
  have Event := PathMeasureCoordinateEvent (Step PositiveLength) (RLSInit n) t
    {x | LeadingOnes x = k}
  rw [← Event]
  exact Positive

end
end ECTheoryLib.Analysis.RLSOnLeadingOnes
