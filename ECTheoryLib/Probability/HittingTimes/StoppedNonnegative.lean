import ECTheoryLib.Probability.HittingTimes.StoppedIncrement
import ECTheoryLib.Probability.Processes.ConditionalDrift
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime

/-!
# Nonnegative processes stopped at zero

First-hitting times and full-history conditional decreases are preserved
on surviving paths. No preservation of raw level-only conditioning is claimed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*}

theorem FirstHittingTimeStopped {State : Type*} (Goal : State → Prop) (X : ℕ → Ω → State) (ω : Ω) :
    FirstHittingTime Goal (fun t => StopAtFirstHit Goal X t ω)=FirstHittingTime Goal (fun t => X t ω) := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  exact Set.ext_iff.mp (StopAtFirstHitEvent Goal X t) ω

theorem ZeroHittingTimeEqNonpositive (X : ℕ → Ω → ℝ) (Nonnegative : ∀ t ω, 0≤X t ω) (ω : Ω) :
    ZeroHittingTime X ω=FirstHittingTime (fun s : ℝ => s≤0) (fun t => X t ω) := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  refine (FirstHittingTimeLeIff (fun s : ℝ => s=0) (fun j => X j ω) t).trans
    (Iff.trans ?_ (FirstHittingTimeLeIff (fun s : ℝ => s≤0) (fun j => X j ω) t).symm)
  constructor
  · rintro ⟨j,Before,Equal⟩
    exact ⟨j,Before,Equal.le⟩
  · rintro ⟨j,Before,Below⟩
    exact ⟨j,Before,le_antisymm Below (Nonnegative j ω)⟩

theorem StopAtNonpositiveNonnegative (X : ℕ → Ω → ℝ) (Nonnegative : ∀ t ω, 0≤X t ω) :
    ∀ t ω, 0≤StopAtFirstHit (fun s : ℝ => s≤0) X t ω :=
  StopAtFirstHitValues _ X (Set.Ici 0) Nonnegative

theorem StopAtNonpositiveZeroTime (X : ℕ → Ω → ℝ) (Nonnegative : ∀ t ω, 0≤X t ω) (ω : Ω) :
    ZeroHittingTime (StopAtFirstHit (fun s : ℝ => s≤0) X) ω=ZeroHittingTime X ω := by
  rw [ZeroHittingTimeEqNonpositive _ (StopAtNonpositiveNonnegative X Nonnegative),
    FirstHittingTimeStopped,ZeroHittingTimeEqNonpositive X Nonnegative]

theorem StopAtNonpositiveZeroAbsorbing [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (Nonnegative : ∀ t ω, 0≤X t ω) :
    ZeroIsAbsorbing μ (StopAtFirstHit (fun s : ℝ => s≤0) X) := by
  intro t
  apply ae_of_all
  intro ω Equal
  exact le_antisymm (StopAtFirstHitAbsorbing (fun s : ℝ => s≤0) X t ω Equal.le)
    (StopAtNonpositiveNonnegative X Nonnegative (t+1) ω)

/-- Stopping preserves the full-history conditional decrease on surviving
paths. It does not assert preservation of conditioning only on the raw level. -/
theorem StoppedConditionalDecrease [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (AdaptedX : Adapted F X)
    (t : ℕ) (DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ) :
    (μ[fun ω => StopAtFirstHit (fun s : ℝ => s≤0) X t ω-
      StopAtFirstHit (fun s : ℝ => s≤0) X (t+1) ω | F t]) =ᵐ[μ]
      (fun ω => if 0<StopAtFirstHit (fun s : ℝ => s≤0) X t ω then
        (μ[fun u => X t u-X (t+1) u | F t]) ω else 0) := by
  let A := {ω | 0<X t ω}
  let D := fun ω => X t ω-X (t+1) ω
  have EventF : MeasurableSet[F t] A := measurableSet_lt measurable_const (AdaptedX t)
  have Event : MeasurableSet A := F.le t _ EventF
  have Equal : (fun ω => -ActiveIncrement X 0 t ω)=A.indicator D := by
    funext ω
    by_cases Active : ω∈A
    · rw [Set.indicator_of_mem Active]
      change 0<X t ω at Active
      change -(if 0<X t ω then X (t+1) ω-X t ω else 0)=X t ω-X (t+1) ω
      rw [if_pos Active,neg_sub]
    · rw [Set.indicator_of_notMem Active]
      change ¬0<X t ω at Active
      change -(if 0<X t ω then X (t+1) ω-X t ω else 0)=0
      rw [if_neg Active,neg_zero]
  have ActiveIntegrable : Integrable (fun ω => -ActiveIncrement X 0 t ω) μ := by
    rw [Equal]
    exact DecreaseIntegrable.indicator Event
  have Stopped := (StoppedIncrementConditional μ X F AdaptedX 0 t (fun z => -z) ActiveIntegrable).2
  simp only [neg_sub,neg_zero] at Stopped
  rw [Equal] at Stopped
  have Conditional := condExp_indicator (m := F t) DecreaseIntegrable EventF
  filter_upwards [Stopped,Conditional] with ω Stopped Conditional
  rw [Stopped]
  by_cases Before : 0<StopAtFirstHit (fun s : ℝ => s≤0) X t ω
  · rw [if_pos Before,if_pos Before,Conditional]
    have Current := (StopAtFirstHitStepBefore (fun s : ℝ => s≤0) X t ω (not_le_of_gt Before)).1
    apply Set.indicator_of_mem
    change 0<X t ω
    rwa [← Current]
  · simp only [if_neg Before]

/-- A lower history-conditioned mean bound transfers to each positive-mass
level event. Only genuine integrable observables are averaged. -/
theorem StateEventExpectationLowerBoundOfCondExp [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (h : ℝ → ℝ) (t : ℕ) (Z : Ω → ℝ)
    (ObservableIntegrable : Integrable Z μ)
    (Bound : ∀ᵐ ω ∂μ, X t ω≠0 → h (X t ω)≤(μ[Z | F t]) ω)
    (s : ℝ) (Nonzero : s≠0) (Positive : 0<μ (StateEvent X t s)) :
    h s≤EventConditionalExpectation μ Z (StateEvent X t s) := by
  have Negative := StateEventExpectationUpperBoundOfCondExp μ X F AdaptedX (fun s => -h s) t
    (fun ω => -Z ω) ObservableIntegrable.neg (by
      have Neg := condExp_neg Z (F t) (μ := μ)
      filter_upwards [Bound,Neg] with ω Bound Neg
      intro Active
      change (μ[-Z | F t]) ω≤-h (X t ω)
      rw [Neg]
      exact neg_le_neg (Bound Active)) s Nonzero Positive
  unfold EventConditionalExpectation at Negative ⊢
  rw [integral_neg,neg_div] at Negative
  exact neg_le_neg_iff.mp Negative

/-- A full-history lower bound transfers to the stopped process's level
events. The original potential need not be Markov or absorbing. -/
theorem StoppedStateDriftLowerBoundOfCondExp [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ)
    (Nonnegative : ∀ s∈S, 0≤s) (Values : ∀ t ω, X t ω∈S) (h : ℝ → ℝ)
    (Bound : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      h (X t ω)≤(μ[fun u => X t u-X (t+1) u | F t]) ω)
    (t : ℕ) (s : ℝ) (Nonzero : s≠0)
    (Positive : 0<μ (StateEvent (StopAtFirstHit (fun s : ℝ => s≤0) X) t s)) :
    h s≤StateDrift μ (StopAtFirstHit (fun s : ℝ => s≤0) X) t s := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S AdaptedX.measurable (ae_of_all _ (Values j))
  have IntegrableY (j : ℕ) : Integrable (Y j) μ :=
    FiniteStateIntegrable μ (Y j) S AdaptedY.measurable (ae_of_all _ (YValues j))
  apply StateEventExpectationLowerBoundOfCondExp μ Y F AdaptedY h t
    (fun ω => Y t ω-Y (t+1) ω) ((IntegrableY t).sub (IntegrableY (t+1))) _ s Nonzero Positive
  have Conditional := StoppedConditionalDecrease μ X F AdaptedX t ((IntegrableX t).sub (IntegrableX (t+1)))
  filter_upwards [Conditional,Bound t] with ω Conditional Bound
  intro Active
  have Above : 0<Y t ω := lt_of_le_of_ne (Nonnegative _ (YValues t ω)) (Ne.symm Active)
  rw [Conditional,if_pos Above]
  have Equal := (StopAtFirstHitStepBefore (fun s : ℝ => s≤0) X t ω (not_le_of_gt Above)).1
  change Y t ω=X t ω at Equal
  rw [Equal]
  apply Bound
  rwa [← Equal]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A complete-history upper bound likewise transfers to stopped level
events. The finite range supplies actual decrease integrability. -/
theorem StoppedStateDriftUpperBoundOfCondExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (S : Finset ℝ)
    (Nonnegative : ∀ s∈S, 0≤s) (Values : ∀ t ω, X t ω∈S) (h : ℝ → ℝ)
    (Bound : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 →
      (μ[fun u => X t u-X (t+1) u | F t]) ω≤h (X t ω))
    (t : ℕ) (s : ℝ) (Nonzero : s≠0)
    (Positive : 0<μ (StateEvent (StopAtFirstHit (fun s : ℝ => s≤0) X) t s)) :
    StateDrift μ (StopAtFirstHit (fun s : ℝ => s≤0) X) t s≤h s := by
  let Y := StopAtFirstHit (fun s : ℝ => s≤0) X
  have AdaptedY : Adapted F Y := StopAtFirstHitAdapted X F AdaptedX _ measurableSet_Iic
  have YValues : ∀ j ω, Y j ω∈S := StopAtFirstHitValues _ X (S : Set ℝ) Values
  have IntegrableX (j : ℕ) : Integrable (X j) μ :=
    FiniteStateIntegrable μ (X j) S AdaptedX.measurable (ae_of_all _ (Values j))
  have IntegrableY (j : ℕ) : Integrable (Y j) μ :=
    FiniteStateIntegrable μ (Y j) S AdaptedY.measurable (ae_of_all _ (YValues j))
  apply StateDriftUpperBoundOfCondExp μ Y F AdaptedY h t
    ((IntegrableY t).sub (IntegrableY (t+1))) _ s Nonzero Positive
  have Conditional := StoppedConditionalDecrease μ X F AdaptedX t ((IntegrableX t).sub (IntegrableX (t+1)))
  filter_upwards [Conditional,Bound t] with ω Conditional Bound
  intro Active
  have Above : 0<Y t ω := lt_of_le_of_ne (Nonnegative _ (YValues t ω)) (Ne.symm Active)
  rw [Conditional,if_pos Above]
  have Equal := (StopAtFirstHitStepBefore (fun s : ℝ => s≤0) X t ω (not_le_of_gt Above)).1
  change Y t ω=X t ω at Equal
  rw [Equal]
  apply Bound
  rwa [← Equal]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A pathwise relation at a nonzero state is preserved on every active
stopped step, including the first step that reaches zero. -/
theorem StopAtNonpositiveActiveRelation (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (Nonnegative : ∀ t ω, 0≤X t ω) (R : ℝ → ℝ → Prop)
    (Relation : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → R (X t ω) (X (t+1) ω)) (t : ℕ) :
    ∀ᵐ ω ∂μ, StopAtFirstHit (fun s : ℝ => s≤0) X t ω≠0 →
      R (StopAtFirstHit (fun s : ℝ => s≤0) X t ω) (StopAtFirstHit (fun s : ℝ => s≤0) X (t+1) ω) := by
  filter_upwards [Relation t] with ω StepRelation
  intro Active
  have NonnegativeY := StopAtFirstHitValues (fun s : ℝ => s≤0) X (Set.Ici 0) Nonnegative t ω
  have Above : 0<StopAtFirstHit (fun s : ℝ => s≤0) X t ω := lt_of_le_of_ne NonnegativeY (Ne.symm Active)
  have Equal := StopAtFirstHitStepBefore (fun s : ℝ => s≤0) X t ω (not_le_of_gt Above)
  rw [Equal.1,Equal.2]
  apply StepRelation
  rwa [← Equal.1]

/-- Descent is only needed before the first hit; the stopped path is globally
nonincreasing even when the original process restarts after zero. -/
theorem StopAtNonpositiveNonincreasing (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (Nonnegative : ∀ t ω, 0≤X t ω)
    (Descent : ∀ t, ∀ᵐ ω ∂μ, X t ω≠0 → X (t+1) ω≤X t ω) (t : ℕ) :
    ∀ᵐ ω ∂μ, StopAtFirstHit (fun s : ℝ => s≤0) X (t+1) ω≤StopAtFirstHit (fun s : ℝ => s≤0) X t ω := by
  filter_upwards [StopAtNonpositiveActiveRelation μ X Nonnegative (fun s r => r≤s) Descent t] with ω Active
  by_cases Zero : StopAtFirstHit (fun s : ℝ => s≤0) X t ω=0
  · rw [StopAtFirstHitFrozenStep (fun s : ℝ => s≤0) X t ω (le_of_eq Zero)]
  · exact Active Zero

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*}

/-- A nonzero stopped level consists exactly of paths still alive at that
level in the original process. This is a pointwise identity, including paths
whose first hit is infinite. -/
theorem StoppedNonzeroStateEventEqSurviving
    (X : ℕ → Ω → ℝ) (Nonnegative : ∀ t ω, 0 ≤ X t ω)
    (t : ℕ) (s : ℝ) (Nonzero : s ≠ 0) :
    StateEvent (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s =
      {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} := by
  ext ω
  change (StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω = s) ↔
    ((t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s)
  constructor
  · intro Current
    have Active : ¬StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω ≤ 0 := by
      intro Below
      apply Nonzero
      exact Current.symm.trans
        (le_antisymm Below (StopAtNonpositiveNonnegative X Nonnegative t ω))
    refine ⟨?_, ?_⟩
    · rw [ZeroHittingTimeEqNonpositive X Nonnegative ω]
      apply lt_of_not_ge
      intro Hit
      exact Active ((StopAtFirstHitGoalIff (fun x : ℝ => x ≤ 0) X t ω).mpr Hit)
    · exact ((StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X t ω Active).1).symm.trans Current
  · rintro ⟨Before, Current⟩
    have Active : ¬StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω ≤ 0 := by
      intro AtGoal
      have Hit := (StopAtFirstHitGoalIff (fun x : ℝ => x ≤ 0) X t ω).mp AtGoal
      rw [← ZeroHittingTimeEqNonpositive X Nonnegative ω] at Hit
      exact (not_lt_of_ge Hit) Before
    exact (StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X t ω Active).1.trans Current

variable [MeasurableSpace Ω]

/-- The event average is exactly preserved after adding survival to the raw
conditioning event. The equality also holds formally on null events; the
tail interface below imposes the drift bound only on positive-probability events.
Its finite measurable range supplies integrability for the probabilistic use. -/
theorem StoppedStateDriftEqSurvivingEventExpectation
    (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (Nonnegative : ∀ t ω, 0 ≤ X t ω)
    (t : ℕ) (s : ℝ) (Nonzero : s ≠ 0) :
    StateDrift μ (StopAtFirstHit (fun x : ℝ => x ≤ 0) X) t s =
      EventConditionalExpectation μ (fun ω => X t ω - X (t + 1) ω)
        {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} := by
  let Y := StopAtFirstHit (fun x : ℝ => x ≤ 0) X
  have AdaptedX : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) X := by
    intro j
    change Measurable (X j)
    exact CoordinatesMeasurable j
  have AdaptedY : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) Y :=
    StopAtFirstHitAdapted X _ AdaptedX _ measurableSet_Iic
  have EventMeasurable : MeasurableSet (StateEvent Y t s) :=
    StateEventMeasurable Y t s AdaptedY.measurable
  have EqualDecrease : Set.EqOn (fun ω => Y t ω - Y (t + 1) ω)
      (fun ω => X t ω - X (t + 1) ω) (StateEvent Y t s) := by
    intro ω Current
    change Y t ω = s at Current
    have Active : ¬StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω ≤ 0 := by
      intro Below
      apply Nonzero
      exact Current.symm.trans
        (le_antisymm Below (StopAtNonpositiveNonnegative X Nonnegative t ω))
    have Endpoints := StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X t ω Active
    change StopAtFirstHit (fun x : ℝ => x ≤ 0) X t ω -
      StopAtFirstHit (fun x : ℝ => x ≤ 0) X (t + 1) ω = X t ω - X (t + 1) ω
    rw [Endpoints.1, Endpoints.2]
  have Event : StateEvent Y t s =
      {ω | (t : WithTop ℕ) < ZeroHittingTime X ω ∧ X t ω = s} :=
    StoppedNonzeroStateEventEqSurviving X Nonnegative t s Nonzero
  change StateDrift μ Y t s = _
  unfold StateDrift EventConditionalExpectation
  rw [setIntegral_congr_fun EventMeasurable EqualDecrease, Event]

end
end ECTheoryLib.Probability

namespace ECTheoryLib.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*}

/-- Taking the positive part above a target preserves its first-hit time,
including initial success and paths which never hit. -/
theorem ShiftedPositivePartZeroTime (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    ZeroHittingTime (fun j u => max (X j u - a) 0) ω =
      FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  change FirstHittingTime (fun s : ℝ => s = 0) (fun j => max (X j ω - a) 0) ≤
      (t : WithTop ℕ) ↔
    FirstHittingTime (fun s : ℝ => s ≤ a) (fun j => X j ω) ≤ (t : WithTop ℕ)
  refine (FirstHittingTimeLeIff (fun s : ℝ => s = 0)
    (fun j => max (X j ω - a) 0) t).trans
    (Iff.trans ?_ (FirstHittingTimeLeIff (fun s : ℝ => s ≤ a) (fun j => X j ω) t).symm)
  constructor
  · rintro ⟨j, Before, Zero⟩
    have Nonpositive : X j ω - a ≤ 0 := max_eq_right_iff.mp Zero
    exact ⟨j, Before, sub_nonpos.mp Nonpositive⟩
  · rintro ⟨j, Before, Below⟩
    exact ⟨j, Before, max_eq_right (sub_nonpos.mpr Below)⟩

/-- Clipping a stopped overshoot to the target can only reduce downward
progress; later increments remain exactly zero. -/
theorem ShiftedPositivePartStoppedDecreaseLe (X : ℕ → Ω → ℝ)
    (a : ℝ) (j : ℕ) (ω : Ω) :
    let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
    max (Y j ω - a) 0 - max (Y (j + 1) ω - a) 0 ≤ Y j ω - Y (j + 1) ω := by
  dsimp only
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  change max (Y j ω - a) 0 - max (Y (j + 1) ω - a) 0 ≤ Y j ω - Y (j + 1) ω
  by_cases Active : a < Y j ω
  · rw [max_eq_left (sub_nonneg.mpr Active.le)]
    have Bound := le_max_left (Y (j + 1) ω - a) 0
    linarith
  · have Frozen := StopAtFirstHitFrozenStep (fun s : ℝ => s ≤ a) X j ω
      (le_of_not_gt Active)
    change Y (j + 1) ω = Y j ω at Frozen
    rw [Frozen]
    simp only [sub_self, le_refl]

/-- The shifted positive part of the actually stopped process is zero
absorbing even when the original process may leave the target again. -/
theorem ShiftedPositivePartStoppedZeroAbsorbing [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (a : ℝ) :
    ZeroIsAbsorbing μ (fun j ω =>
      max (StopAtFirstHit (fun s : ℝ => s ≤ a) X j ω - a) 0) := by
  intro j
  apply ae_of_all
  intro ω Zero
  let Y := StopAtFirstHit (fun s : ℝ => s ≤ a) X
  change max (Y j ω - a) 0 = 0 at Zero
  have Below : Y j ω ≤ a := by
    have Bound := le_max_left (Y j ω - a) 0
    rw [Zero] at Bound
    linarith
  have Frozen := StopAtFirstHitFrozenStep (fun s : ℝ => s ≤ a) X j ω Below
  change Y (j + 1) ω = Y j ω at Frozen
  change max (Y (j + 1) ω - a) 0 = 0
  rw [Frozen]
  exact Zero

end
end ECTheoryLib.Probability
