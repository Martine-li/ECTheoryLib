import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicative
import ECTheoryLib.Tools.Drift.NonabsorbingMultiplicativeTail
import ECTheoryLib.Tools.Drift.Additive
import ECTheoryLib.Probability.HittingTimes.StoppedHitting
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-! A three-path process separating raw-level, stopped, and surviving-level drift conditions. See docs/SOURCE_NOTES.md or docs/COVERAGE.md for source relations. -/




namespace AbsorptionConditioningAudit
open MeasureTheory ECTheoryLib.Probability
noncomputable section

def P : Measure (Fin 3) := (PMF.uniformOfFintype (Fin 3)).toMeasure
instance : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype (Fin 3)).toMeasure)

/-- All branches start at one. Branch zero stays there forever; the other
two alternate between zero and one with opposite phases. -/
def X (t : ℕ) (ω : Fin 3) : ℝ :=
  if t=0 then 1 else if ω=0 then 1 else if ω=1 then (t%2 : ℕ) else 1-(t%2 : ℕ)

theorem Values (t : ℕ) (ω : Fin 3) : X t ω∈({0,1} : Finset ℝ) := by
  have Cases : t%2=0 ∨ t%2=1 := by omega
  rcases Cases with Parity | Parity <;> fin_cases ω <;>
    by_cases Zero : t=0 <;> norm_num [X,Zero,Parity]

theorem Initial (ω : Fin 3) : X 0 ω=1 := by simp [X]

theorem LevelOneDrift (t : ℕ) : StateDrift P X t 1=if t=0 then (1/3 : ℝ) else 1/2 := by
  classical
  unfold StateDrift EventConditionalExpectation
  rw [← integral_indicator (StateEventMeasurable X t 1 (measurable_of_countable _))]
  unfold P
  rw [PMF.integral_eq_sum,PMF.toMeasure_apply_fintype]
  have TwoZero : (2 : Fin 3)≠0 := by decide
  have TwoOne : (2 : Fin 3)≠1 := by decide
  have Cases : t%2=0 ∨ t%2=1 := by omega
  by_cases Zero : t=0
  · norm_num [Zero,Fin.sum_univ_three,Set.indicator_apply,StateEvent,X,PMF.uniformOfFintype_apply,TwoZero,TwoOne]
  · rcases Cases with Parity | Parity
    · have Next : (t+1)%2=1 := by omega
      norm_num [Fin.sum_univ_three,Set.indicator_apply,StateEvent,X,Zero,Nat.add_one_ne_zero,Parity,Next,
        PMF.uniformOfFintype_apply,TwoZero,TwoOne]
      norm_num [ENNReal.toReal_add]
    · have Next : (t+1)%2=0 := by omega
      norm_num [Fin.sum_univ_three,Set.indicator_apply,StateEvent,X,Zero,Nat.add_one_ne_zero,Parity,Next,
        PMF.uniformOfFintype_apply,TwoZero,TwoOne]
      norm_num [ENNReal.toReal_add]

theorem Trapped : ZeroHittingTime X 0=⊤ := by
  rw [ZeroHittingTime,FirstHittingTimeEqTopIff]
  intro t
  simp [X]

theorem ExpectedTimeInfinite : ExpectedZeroHittingTime P X=⊤ := by
  rw [ExpectedZeroHittingTime,lintegral_fintype]
  apply top_le_iff.mp
  calc
    ⊤ = ENat.toENNReal (ZeroHittingTime X 0)*P {0} := by
      rw [Trapped]
      change (⊤ : ENNReal)=⊤*P {0}
      norm_num [P,PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply]
    _ ≤ ∑ ω : Fin 3, ENat.toENNReal (ZeroHittingTime X ω)*P {ω} :=
      Finset.single_le_sum (f := fun ω : Fin 3 => ENat.toENNReal (ZeroHittingTime X ω)*P {ω})
        (fun _ _ => bot_le) (Finset.mem_univ 0)

theorem StateDriftPositive (t : ℕ) (s : ℝ) (InS : s∈({0,1} : Finset ℝ)) (Nonzero : s≠0) :
    (1/3 : ℝ)≤StateDrift P X t s := by
  have One : s=1 := by simpa only [Finset.mem_insert,Finset.mem_singleton,Nonzero,false_or] using InS
  rw [One,LevelOneDrift]
  split <;> norm_num

theorem InitialMean : ExpectedValue P (X 0)=1 := by
  change (∫ ω, X 0 ω ∂P)=1
  simp only [Initial,integral_const,probReal_univ,one_smul]

/-- Every explicit raw-level premise of the unabsorbed upper-bound reading
is satisfied, but the alleged finite expected hitting-time bound is false. -/
theorem RawAdditiveConclusionFails :
    ¬ExpectedZeroHittingTime P X≤ENNReal.ofReal (ExpectedValue P (X 0)/(1/3)) := by
  rw [ExpectedTimeInfinite]
  exact not_le_of_gt ENNReal.ofReal_lt_top

def Stopped := StopAtFirstHit (fun s : ℝ => s≤0) X

theorem StoppedAfterTwo (t : ℕ) (After : 2≤t) (ω : Fin 3) :
    Stopped t ω=if ω=0 then 1 else 0 := by
  by_cases Trap : ω=0
  · simp [Stopped,StopAtFirstHit,stoppedProcess,X,Trap]
  · rw [if_neg Trap]
    have Nonnegative : ∀ j u, 0≤X j u := by
      intro j u
      have In := Values j u
      simp only [Finset.mem_insert,Finset.mem_singleton] at In
      rcases In with Zero | One
      · rw [Zero]
      · rw [One]; norm_num
    have Above : 0≤Stopped t ω := StopAtFirstHitValues _ X (Set.Ici 0) Nonnegative t ω
    apply le_antisymm _ Above
    apply (StopAtFirstHitGoalIff (fun s : ℝ => s≤0) X t ω).mpr
    apply (FirstHittingTimeLeIff (fun s : ℝ => s≤0) (fun j => X j ω) t).mpr
    by_cases One : ω=1
    · exact ⟨2,After,by norm_num [X,One]⟩
    · exact ⟨1,by omega,by norm_num [X,Trap,One]⟩

/-- Stopping changes which hidden branches remain in the current-level
event: the stopped positive level eventually consists only of the trapped branch. -/
theorem StoppedDriftVanishes : StateDrift P Stopped 2 1=0 := by
  have Difference : (fun ω => Stopped 2 ω-Stopped (2+1) ω)=(fun _ => (0 : ℝ)) := by
    funext ω
    rw [StoppedAfterTwo 2 (by omega),StoppedAfterTwo 3 (by omega),sub_self]
  unfold StateDrift EventConditionalExpectation
  rw [Difference]
  simp

theorem RawAndStoppedDriftDiffer : StateDrift P X 2 1≠StateDrift P Stopped 2 1 := by
  rw [LevelOneDrift,StoppedDriftVanishes]
  norm_num

/-- Explicitly collect the model assumptions and the failed conclusion,
so that the regression cannot be mistaken for merely an informal example. -/
theorem Counterexample :
    (∀ t, Measurable (X t)) ∧ (∀ t ω, X t ω∈({0,1} : Finset ℝ)) ∧
    (∀ ω, X 0 ω=1) ∧
    (∀ t s, s∈({0,1} : Finset ℝ) → s≠0 → 0<P (StateEvent X t s) →
      (1/3 : ℝ)≤StateDrift P X t s) ∧
    ¬ExpectedZeroHittingTime P X≤ENNReal.ofReal (ExpectedValue P (X 0)/(1/3)) :=
  ⟨fun _ => measurable_of_countable _,Values,Initial,
    fun t s InS Nonzero _ => StateDriftPositive t s InS Nonzero,RawAdditiveConclusionFails⟩

end
end AbsorptionConditioningAudit


namespace AbsorptionConditioningAudit
open MeasureTheory ECTheoryLib.Probability
noncomputable section

theorem NontrappedHitByTwo (ω : Fin 3) (NotTrapped : ω≠0) :
    ZeroHittingTime X ω≤((2 : ℕ) : WithTop ℕ) := by
  apply (FirstHittingTimeLeIff (fun s : ℝ => s=0) (fun j => X j ω) 2).mpr
  by_cases One : ω=1
  · exact ⟨2,le_rfl,by norm_num [X,One]⟩
  · exact ⟨1,by omega,by norm_num [X,NotTrapped,One]⟩

theorem TailAtSix : P {ω | ((6 : ℕ) : WithTop ℕ)<ZeroHittingTime X ω}=(1/3 : ENNReal) := by
  have Event : {ω | ((6 : ℕ) : WithTop ℕ)<ZeroHittingTime X ω}=({0} : Set (Fin 3)) := by
    ext ω
    by_cases Trap : ω=0
    · simp only [Trap,Trapped,Set.mem_ofPred_eq,Set.mem_singleton_iff,iff_true]
      exact WithTop.coe_lt_top 6
    · have Hit := (NontrappedHitByTwo ω Trap).trans (show ((2 : ℕ) : WithTop ℕ)≤((6 : ℕ) : WithTop ℕ) by norm_num)
      simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff,Trap,iff_false]
      exact not_lt_of_ge Hit
  rw [Event]
  norm_num [P,PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply]

theorem RawMultiplicativeDrift (t : ℕ) (s : ℝ) (InS : s∈({0,1} : Finset ℝ)) (Nonzero : s≠0) :
    (1/3 : ℝ)*s≤StateDrift P X t s := by
  have One : s=1 := by simpa only [Finset.mem_insert,Finset.mem_singleton,Nonzero,false_or] using InS
  simpa only [One,mul_one] using StateDriftPositive t s InS Nonzero

/-- At r=2, delta=1/3 and s0=smin=1 the raw, nonabsorbing reading
of the multiplicative upper tail predicts exp(-2), but the tail is 1/3. -/
theorem RawMultiplicativeTailFails :
    ¬P {ω | (⌈((2 : ℝ)+Real.log (1/1))/(1/3)⌉₊ : WithTop ℕ)<ZeroHittingTime X ω}≤
      ENNReal.ofReal (Real.exp (-2)) := by
  have Time : ⌈((2 : ℝ)+Real.log (1/1))/(1/3)⌉₊=6 := by norm_num
  rw [Time,TailAtSix]
  have Exponential : (3 : ℝ)<Real.exp 2 := by
    have Bound := Real.add_one_lt_exp (by norm_num : (2 : ℝ)≠0)
    linarith
  have Small : Real.exp (-2)<(1/3 : ℝ) := by
    rw [Real.exp_neg,← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) Exponential
  have Lift := ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ)<1/3) |>.mpr Small
  have Rational : ENNReal.ofReal (1/3 : ℝ)=(1/3 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [Rational] at Lift
  exact not_le_of_gt Lift

end
end AbsorptionConditioningAudit


namespace AbsorptionConditioningAudit
open MeasureTheory ECTheoryLib.Probability ECTheoryLib.Tools.Drift
noncomputable section

-- The same counterexample uses a strictly increasing positive drift function,
-- so it does not rely on an ambiguous reading of the word "increasing".
theorem LinearDriftStrictlyIncreasing : StrictMono (fun s : ℝ => (1/3)*s) := by
  intro a b Before
  exact mul_lt_mul_of_pos_left Before (by norm_num)

theorem LinearDriftPositive (s : ℝ) (Positive : 0<s) : 0<(1/3 : ℝ)*s :=
  mul_pos (by norm_num) Positive

theorem RawVariableConclusionFails :
    ¬ExpectedZeroHittingTime P X≤ENNReal.ofReal
      (1/((1/3 : ℝ)*1)+ExpectedValue P (fun ω => ∫ s in (1 : ℝ)..X 0 ω, 1/((1/3)*s))) := by
  simp only [ExpectedTimeInfinite,Initial,intervalIntegral.integral_same,ExpectedValue,integral_zero,add_zero]
  exact not_le.mpr ENNReal.ofReal_lt_top

theorem RawMultiplicativeExpectationFails :
    ¬ExpectedZeroHittingTime P X≤ENNReal.ofReal
      ((1+ExpectedValue P (fun ω => Real.log (X 0 ω/1)))/(1/3)) := by
  simp only [ExpectedTimeInfinite,Initial,div_one,Real.log_one,ExpectedValue,integral_zero,add_zero]
  exact not_le.mpr ENNReal.ofReal_lt_top

end
end AbsorptionConditioningAudit


/-! The old raw-level counterexample fails the positive-mass surviving-level premise. -/

namespace AbsorptionConditioningAudit
open MeasureTheory ECTheoryLib.Probability
noncomputable section

theorem SurvivingLevelEventAtTwo :
    {ω : Fin 3 | ((2 : ℕ) : WithTop ℕ) < ZeroHittingTime X ω ∧ X 2 ω = 1} =
      ({0} : Set (Fin 3)) := by
  ext ω
  change (((2 : ℕ) : WithTop ℕ) < ZeroHittingTime X ω ∧ X 2 ω = 1) ↔ ω = 0
  constructor
  · intro Alive
    by_contra NotTrapped
    exact (not_lt_of_ge (NontrappedHitByTwo ω NotTrapped)) Alive.1
  · rintro rfl
    constructor
    · rw [Trapped]
      exact WithTop.coe_lt_top 2
    · norm_num [X]

theorem SurvivingLevelMassAtTwo :
    P {ω | ((2 : ℕ) : WithTop ℕ) < ZeroHittingTime X ω ∧ X 2 ω = 1} =
      (1 / 3 : ENNReal) := by
  rw [SurvivingLevelEventAtTwo]
  norm_num [P, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

theorem SurvivingLevelMeanAtTwo :
    EventConditionalExpectation P (fun ω => X 2 ω - X 3 ω)
      {ω | ((2 : ℕ) : WithTop ℕ) < ZeroHittingTime X ω ∧ X 2 ω = 1} = 0 := by
  have Nonnegative : ∀ t ω, 0 ≤ X t ω := by
    intro t ω
    have InS := Values t ω
    simp only [Finset.mem_insert, Finset.mem_singleton] at InS
    rcases InS with Zero | One
    · rw [Zero]
    · rw [One]
      norm_num
  have Identity := StoppedStateDriftEqSurvivingEventExpectation P X
    (fun _ => measurable_of_countable _) Nonnegative 2 1 (by norm_num)
  exact Identity.symm.trans StoppedDriftVanishes

/-- The new positive-mass surviving-level premise explicitly rejects the
original three-path counterexample at delta=1/3, t=2, s=1. -/
theorem RawCounterexampleFailsSurvivingDrift :
    ¬(∀ (t : ℕ) (s : ℝ), s ∈ ({0, 1} : Finset ℝ) → s ≠ 0 →
      0 < P {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} →
      (1 / 3 : ℝ) * s ≤ EventConditionalExpectation P
        (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s}) := by
  intro Drift
  have Positive : 0 <
      P {ω | ((2 : ℕ) : WithTop ℕ) < ZeroHittingTime X ω ∧ X 2 ω = 1} := by
    rw [SurvivingLevelMassAtTwo]
    norm_num
  have Bound := Drift 2 1 (by simp) (by norm_num) Positive
  rw [SurvivingLevelMeanAtTwo] at Bound
  norm_num at Bound

end
end AbsorptionConditioningAudit
