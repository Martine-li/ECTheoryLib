import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import ECTheoryLib.Tools.Drift.Potential
import ECTheoryLib.Probability.Processes.ConditionalDrift
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential-moment control of an interval crossing

The drift region a < s < b and the entrance region s >= b have separate
moment hypotheses. The lower target is explicitly absorbing. Common finite
range is pointwise; positive current-state events suffice, with no Markov or
independence assumption. This intermediate theorem is not the general
negative-drift theorem with exponentially decaying jump tails.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Unit reward at the lower target, exponential inside the crossing interval,
and zero above its upper boundary. This separates drift from entrance control. -/
def ExponentialBarrierPotential (a b Lambda s : ℝ) : ℝ :=
  if s ≤ a then 1 else if b ≤ s then 0 else Real.exp (-Lambda*(s-a))

theorem ExponentialBarrierNonnegative (a b Lambda s : ℝ) :
    0 ≤ ExponentialBarrierPotential a b Lambda s := by
  unfold ExponentialBarrierPotential
  split
  · norm_num
  · split
    · exact le_rfl
    · exact (Real.exp_pos _).le

theorem ExponentialBarrierLeOne (a b Lambda s : ℝ) (NonnegativeLambda : 0 ≤ Lambda) :
    ExponentialBarrierPotential a b Lambda s ≤ 1 := by
  unfold ExponentialBarrierPotential
  split
  · exact le_rfl
  · rename_i Above
    split
    · norm_num
    · apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr NonnegativeLambda) (by linarith)

theorem ExponentialBarrierLeRaw (a b Lambda s : ℝ) (NonnegativeLambda : 0 ≤ Lambda) :
    ExponentialBarrierPotential a b Lambda s ≤ Real.exp (-Lambda*(s-a)) := by
  unfold ExponentialBarrierPotential
  split
  · rename_i AtTarget
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr NonnegativeLambda) (sub_nonpos.mpr AtTarget)
  · split
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem ExponentialBarrierAbove (a b Lambda s : ℝ) (Ordered : a < b) (Above : b ≤ s) :
    ExponentialBarrierPotential a b Lambda s = 0 := by
  rw [ExponentialBarrierPotential, if_neg (by linarith), if_pos Above]

theorem ExponentialBarrierFactor (a b Lambda s y : ℝ) (NonnegativeLambda : 0 ≤ Lambda) :
    ExponentialBarrierPotential a b Lambda y ≤
      Real.exp (-Lambda*(s-a)) * Real.exp (-Lambda*(y-s)) := by
  have Factor : -Lambda*(y-a) = -Lambda*(s-a) + -Lambda*(y-s) := by ring
  rw [← Real.exp_add, ← Factor]
  exact ExponentialBarrierLeRaw a b Lambda y NonnegativeLambda

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Interior exponential control and a separate entrance moment bound give
an additive growth bound for the truncated barrier. No drift is demanded above b. -/
theorem ExponentialBarrierExpectedStep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b Lambda D : ℝ)
    (Ordered : a < b) (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeD : 0 ≤ D)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S) (t : ℕ)
    (Interior : ∀ s, s ∈ S → a < s → s < b → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (t+1) ω-s)))
        (StateEvent X t s) ≤ 1)
    (Entrance : ∀ s, s ∈ S → b ≤ s → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (t+1) ω-b)))
        (StateEvent X t s) ≤ D) :
    (∫ ω, ExponentialBarrierPotential a b Lambda (X (t+1) ω) ∂μ) ≤
      (∫ ω, ExponentialBarrierPotential a b Lambda (X t ω) ∂μ) + D*Real.exp (-Lambda*(b-a)) := by
  classical
  let W := ExponentialBarrierPotential a b Lambda
  let C := D*Real.exp (-Lambda*(b-a))
  have NonnegativeC : 0 ≤ C := mul_nonneg NonnegativeD (Real.exp_pos _).le
  have CurrentIntegrable := FiniteStateCompositionIntegrable μ (X t) S W (Coordinates t) (Values t)
  have NextIntegrable := FiniteStateCompositionIntegrable μ (X (t+1)) S W (Coordinates (t+1)) (Values (t+1))
  have Local (s : ℝ) (InS : s ∈ S) :
      (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ) ≤
        ∫ ω in StateEvent X t s, W (X t ω)+C ∂μ := by
    have EventMeasurable := StateEventMeasurable X t s (Coordinates t)
    have RightConstant : (∫ ω in StateEvent X t s, W (X t ω)+C ∂μ) =
        (W s+C)*(μ (StateEvent X t s)).toReal := by
      rw [setIntegral_congr_fun EventMeasurable (show Set.EqOn (fun ω => W (X t ω)+C)
        (fun _ => W s+C) (StateEvent X t s) from fun _ Current => congrArg (fun r => W r+C) Current),
        setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
    rw [RightConstant]
    by_cases Null : μ (StateEvent X t s)=0
    · rw [Measure.restrict_eq_zero.mpr Null, integral_zero_measure, Null, ENNReal.toReal_zero, mul_zero]
    · have PositiveReal := ENNReal.toReal_pos Null (measure_ne_top μ (StateEvent X t s))
      have MomentIntegral (r B : ℝ)
          (Moment : EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (t+1) ω-r)))
            (StateEvent X t s) ≤ B) :
          (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ) ≤
            Real.exp (-Lambda*(r-a))*B*(μ (StateEvent X t s)).toReal := by
        let Z := fun ω => Real.exp (-Lambda*(X (t+1) ω-r))
        have IntegrableZ := FiniteStateCompositionIntegrable μ (X (t+1)) S
          (fun v => Real.exp (-Lambda*(v-r))) (Coordinates (t+1)) (Values (t+1))
        have Average : (∫ ω in StateEvent X t s, Z ω ∂μ) ≤ B*(μ (StateEvent X t s)).toReal := by
          exact (div_le_iff₀ PositiveReal).mp Moment
        calc
          _ ≤ Real.exp (-Lambda*(r-a)) * ∫ ω in StateEvent X t s, Z ω ∂μ := by
            rw [← integral_const_mul]
            apply integral_mono_ae NextIntegrable.integrableOn
              (IntegrableZ.const_mul (Real.exp (-Lambda*(r-a)))).integrableOn
            exact ae_of_all _ (fun ω => ExponentialBarrierFactor a b Lambda r (X (t+1) ω) NonnegativeLambda)
          _ ≤ Real.exp (-Lambda*(r-a)) * (B*(μ (StateEvent X t s)).toReal) :=
            mul_le_mul_of_nonneg_left Average (Real.exp_pos _).le
          _ = _ := by ring
      by_cases AtTarget : s ≤ a
      · have UnitBound : (∫ ω in StateEvent X t s, W (X (t+1) ω) ∂μ) ≤
            (μ (StateEvent X t s)).toReal := by
          have Bound := integral_mono_ae (μ := μ.restrict (StateEvent X t s))
            NextIntegrable.integrableOn (integrable_const (1 : ℝ))
            (ae_of_all _ (fun ω => ExponentialBarrierLeOne a b Lambda (X (t+1) ω) NonnegativeLambda))
          rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] at Bound
          exact Bound
        have CurrentValue : W s = 1 := if_pos AtTarget
        rw [CurrentValue]
        calc
          _ ≤ (μ (StateEvent X t s)).toReal := UnitBound
          _ ≤ (1+C)*(μ (StateEvent X t s)).toReal := by nlinarith [ENNReal.toReal_nonneg (a := μ (StateEvent X t s))]
      · by_cases Above : b ≤ s
        · have Bound := MomentIntegral b D (Entrance s InS Above (bot_lt_iff_ne_bot.mpr Null))
          rw [show W s=0 from ExponentialBarrierAbove a b Lambda s Ordered Above, zero_add]
          calc
            _ ≤ Real.exp (-Lambda*(b-a))*D*(μ (StateEvent X t s)).toReal := Bound
            _ = C*(μ (StateEvent X t s)).toReal := by dsimp [C]; ring
        · have Bound := MomentIntegral s 1
            (Interior s InS (lt_of_not_ge AtTarget) (lt_of_not_ge Above) (bot_lt_iff_ne_bot.mpr Null))
          have CurrentValue : W s = Real.exp (-Lambda*(s-a)) := by
            change ExponentialBarrierPotential a b Lambda s = _
            rw [ExponentialBarrierPotential, if_neg AtTarget, if_neg Above]
          rw [CurrentValue]
          rw [mul_one] at Bound
          calc
            _ ≤ Real.exp (-Lambda*(s-a))*(μ (StateEvent X t s)).toReal := Bound
            _ ≤ (Real.exp (-Lambda*(s-a))+C)*(μ (StateEvent X t s)).toReal := by
              nlinarith [ENNReal.toReal_nonneg (a := μ (StateEvent X t s))]
  have SumIntegrable : Integrable (fun ω => W (X t ω)+C) μ := CurrentIntegrable.add (integrable_const C)
  have Global : (∫ ω, W (X (t+1) ω) ∂μ) ≤ ∫ ω, W (X t ω)+C ∂μ := by
    rw [FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) NextIntegrable,
      FiniteStateIntegralPartition μ X t S _ (Coordinates t) (Values t) SumIntegrable]
    exact Finset.sum_le_sum Local
  rw [integral_add CurrentIntegrable (integrable_const C), integral_const, probReal_univ, one_smul] at Global
  exact Global

end
end ECTheoryLib.Tools.Drift

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Crossing an interval from its upper side is rare when the interior
exponential moment does not grow and entrances are controlled separately.
This version explicitly assumes absorption in the lower target interval. -/
theorem ExponentialBarrierHittingTail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (S : Finset ℝ) (a b Lambda D : ℝ)
    (Ordered : a < b) (NonnegativeLambda : 0 ≤ Lambda) (NonnegativeD : 0 ≤ D)
    (Coordinates : ∀ t, Measurable (X t)) (Values : ∀ t ω, X t ω ∈ S)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b ≤ X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω ≤ a → X (t+1) ω ≤ a)
    (Interior : ∀ t s, s ∈ S → a < s → s < b → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (t+1) ω-s)))
        (StateEvent X t s) ≤ 1)
    (Entrance : ∀ t s, s ∈ S → b ≤ s → 0 < μ (StateEvent X t s) →
      EventConditionalExpectation μ (fun ω => Real.exp (-Lambda*(X (t+1) ω-b)))
        (StateEvent X t s) ≤ D) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*D*Real.exp (-Lambda*(b-a))) := by
  let W := ExponentialBarrierPotential a b Lambda
  let C := D*Real.exp (-Lambda*(b-a))
  have InitialMean : (∫ ω, W (X 0 ω) ∂μ)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [InitiallyAbove] with ω Above
    exact ExponentialBarrierAbove a b Lambda (X 0 ω) Ordered Above
  have Growth (j : ℕ) : (∫ ω, W (X j ω) ∂μ) ≤ (j : ℝ)*C := by
    induction j with
    | zero => rw [InitialMean, Nat.cast_zero, zero_mul]
    | succ j Before =>
      have Step := ExponentialBarrierExpectedStep μ X S a b Lambda D Ordered
        NonnegativeLambda NonnegativeD Coordinates Values j (Interior j) (Entrance j)
      calc
        _ ≤ (∫ ω, W (X j ω) ∂μ)+C := Step
        _ ≤ (j : ℝ)*C+C := add_le_add Before le_rfl
        _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
  have IntegrableW := FiniteStateCompositionIntegrable μ (X t) S W (Coordinates t) (Values t)
  have Markov := IntegrableW.measure_le_integral
    (ae_of_all _ (fun ω => ExponentialBarrierNonnegative a b Lambda (X t ω)))
    (s := {ω | X t ω ≤ a}) (by
      intro ω AtTarget
      change X t ω ≤ a at AtTarget
      change 1 ≤ ExponentialBarrierPotential a b Lambda (X t ω)
      rw [ExponentialBarrierPotential, if_pos AtTarget])
  let Y : ℕ → Ω → ℝ := fun j ω => if X j ω ≤ a then 0 else 1
  have ZeroIff (j : ℕ) (ω : Ω) : Y j ω=0 ↔ X j ω ≤ a := by
    dsimp [Y]
    by_cases AtTarget : X j ω ≤ a
    · rw [if_pos AtTarget]
      exact iff_of_true rfl AtTarget
    · rw [if_neg AtTarget]
      exact iff_of_false one_ne_zero AtTarget
  have AbsorbingY : ZeroIsAbsorbing μ Y := by
    intro j
    filter_upwards [Absorbing j] with ω Stays
    intro Zero
    exact (ZeroIff (j+1) ω).mpr (Stays ((ZeroIff j ω).mp Zero))
  have TimeEqual (ω : Ω) : ZeroHittingTime Y ω =
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) := by
    have ExistsEqual : (∃ j, 0 ≤ j ∧ Y j ω=0) ↔ (∃ j, 0 ≤ j ∧ X j ω ≤ a) :=
      exists_congr (fun j => and_congr_right (fun _ => ZeroIff j ω))
    unfold ZeroHittingTime FirstHittingTime hittingAfter
    simp only [Set.mem_ofPred_eq, ZeroIff]
    by_cases Left : ∃ j, 0 ≤ j ∧ Y j ω=0
    · have Right := ExistsEqual.mp Left
      rw [if_pos Left, if_pos Right]
    · have Right : ¬ ∃ j, 0 ≤ j ∧ X j ω ≤ a := fun Exists => Left (ExistsEqual.mpr Exists)
      rw [if_neg Left, if_neg Right]
  have Event : μ {ω | FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)} =
      μ {ω | X t ω ≤ a} := by
    apply measure_congr
    filter_upwards [ZeroHittingTimeLeIffOfAbsorbing μ Y AbsorbingY t] with ω Same
    rw [TimeEqual, ZeroIff] at Same
    exact propext Same
  rw [Event]
  apply Markov.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (t : ℝ)*C := Growth t
    _ = _ := by dsimp [C]; ring

end
end ECTheoryLib.Tools.Drift
