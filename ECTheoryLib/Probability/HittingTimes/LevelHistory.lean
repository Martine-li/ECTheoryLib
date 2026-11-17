import ECTheoryLib.Probability.HittingTimes.LevelHittingTime
import ECTheoryLib.Probability.HittingTimes.GeometricStages
import Mathlib.Probability.Process.Adapted

/-!
# Measurable histories of nested goal-entry times

A fixed finite duration history is known at its cumulative entry time. This
lets a deterministic-time, past-event progress bound control the next stage
after arbitrary histories. Infinite histories are handled separately without
assuming termination: after an infinite entry time subsequent durations are zero.

We reuse Mathlib stopping times, filtrations and conditional measures. Only the
entry-duration conversion is new; no strong Markov or stage independence premise
is imposed.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Mathlib hittingAfter makes each adapted goal-entry time a stopping time. -/
theorem FirstHittingTimeProcessIsStoppingTime {Ω State : Type*}
    [MeasurableSpace Ω] [MeasurableSpace State]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X) (Goal : State → Prop)
    (GoalMeasurable : MeasurableSet {x | Goal x}) :
    IsStoppingTime F (fun ω => FirstHittingTime Goal (fun t => X t ω)) := by
  exact AdaptedX.isStoppingTime_hittingAfter GoalMeasurable

/-- The first n stage durations have the prescribed finite values. -/
def DurationHistoryEvent {Ω State : Type*} (Goals : ℕ → State → Prop)
    (X : ℕ → Ω → State) (n : ℕ) (h : ℕ → ℕ) : Set Ω :=
  {ω | ∀ i < n, LevelDuration Goals i (fun t => X t ω) = (h i : WithTop ℕ)}

/-- The corresponding entry times are the cumulative finite durations. -/
def EntryHistoryEvent {Ω State : Type*} (Goals : ℕ → State → Prop)
    (X : ℕ → Ω → State) (n : ℕ) (h : ℕ → ℕ) : Set Ω :=
  {ω | ∀ j ≤ n, FirstHittingTime (Goals j) (fun t => X t ω) =
    ((∑ i ∈ Finset.range j, h i : ℕ) : WithTop ℕ)}

/-- Finite duration histories and finite entry histories describe the same event. -/
theorem DurationHistoryEventEqEntryHistory {Ω State : Type*} (Goals : ℕ → State → Prop)
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (X : ℕ → Ω → State) (n : ℕ) (h : ℕ → ℕ) :
    DurationHistoryEvent Goals X n h = EntryHistoryEvent Goals X n h := by
  ext ω
  constructor
  · intro Durations j Before
    rw [← LevelDurationSum Goals Nested Initially (fun t => X t ω) j, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i InRange
    exact Durations i (Nat.lt_of_lt_of_le (Finset.mem_range.mp InRange) Before)
  · intro Entries i Before
    unfold LevelDuration
    rw [Entries i (Nat.le_of_lt Before), Entries (i+1) (Nat.succ_le_of_lt Before)]
    have CastSub (a b : ℕ) : (a : WithTop ℕ)-(b : WithTop ℕ) = ((a-b : ℕ) : WithTop ℕ) := rfl
    rw [CastSub]
    congr 1
    rw [Finset.sum_range_succ]
    omega

/-- A finite entry history is known by the last prescribed entry time. -/
theorem EntryHistoryEventMeasurable {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (n : ℕ) (h : ℕ → ℕ) :
    MeasurableSet[F (∑ i ∈ Finset.range n, h i)] (EntryHistoryEvent Goals X n h) := by
  have Event : EntryHistoryEvent Goals X n h =
      ⋂ j : ℕ, ⋂ (_Before : j ≤ n),
        {ω | FirstHittingTime (Goals j) (fun t => X t ω) =
          ((∑ i ∈ Finset.range j, h i : ℕ) : WithTop ℕ)} := by
    ext ω
    simp only [EntryHistoryEvent, mem_ofPred_eq, mem_iInter]
  rw [Event]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro Before
  apply (FirstHittingTimeProcessIsStoppingTime F X AdaptedX (Goals j)
    (GoalMeasurable j)).measurableSet_eq_le
  exact Finset.sum_le_sum_of_subset (Finset.range_mono Before)

/-- The completed duration history is measurable at its deterministic total time. -/
theorem DurationHistoryEventMeasurable {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (h : ℕ → ℕ) :
    MeasurableSet[F (∑ i ∈ Finset.range n, h i)] (DurationHistoryEvent Goals X n h) := by
  rw [DurationHistoryEventEqEntryHistory Goals Nested Initially X n h]
  exact EntryHistoryEventMeasurable F X AdaptedX Goals GoalMeasurable n h

/-- After a finite entry time, surviving s more steps is an ordinary time translation. -/
theorem ExtendedNatDurationSurvival (T : WithTop ℕ) (a s : ℕ) :
    (s : WithTop ℕ) < T-(a : WithTop ℕ) ↔ ((a+s : ℕ) : WithTop ℕ) < T := by
  cases T using WithTop.recTopCoe with
  | top =>
      change (s : WithTop ℕ) < ⊤ ↔ ((a+s : ℕ) : WithTop ℕ) < ⊤
      simp
  | coe t =>
      change (s : WithTop ℕ) < (t : WithTop ℕ)-(a : WithTop ℕ) ↔
        ((a+s : ℕ) : WithTop ℕ) < (t : WithTop ℕ)
      have CastSub : (t : WithTop ℕ)-(a : WithTop ℕ) = ((t-a : ℕ) : WithTop ℕ) := rfl
      rw [CastSub]
      norm_cast
      omega

/-- On a finite history, the current entry time is the sum of earlier durations. -/
theorem DurationHistoryEndpoint {Ω State : Type*} (Goals : ℕ → State → Prop)
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (X : ℕ → Ω → State) (n : ℕ) (h : ℕ → ℕ) (ω : Ω)
    (History : ω ∈ DurationHistoryEvent Goals X n h) :
    FirstHittingTime (Goals n) (fun t => X t ω) = ((∑ i ∈ Finset.range n, h i : ℕ) : WithTop ℕ) := by
  rw [DurationHistoryEventEqEntryHistory Goals Nested Initially X n h] at History
  exact History n le_rfl

open scoped unitInterval

/-- Past-event progress bounds imply geometric survival contraction after a finite stage history. -/
theorem FiniteStageHistorySurvivalStep {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (p : I)
    (Progress : ∀ t (A : Set Ω), MeasurableSet[F t] A →
      (∀ ω ∈ A, FirstHittingTime (Goals n) (fun j => X j ω) ≤ (t : WithTop ℕ) ∧
        (t : WithTop ℕ) < FirstHittingTime (Goals (n+1)) (fun j => X j ω)) →
      P.real (A ∩ {ω | ((t+1 : ℕ) : WithTop ℕ) < FirstHittingTime (Goals (n+1)) (fun j => X j ω)}) ≤
        (1-(p : ℝ))*P.real A)
    (h : ℕ → ℕ) (s : ℕ) :
    (P[|DurationHistoryEvent Goals X n h]).real
        {ω | ((s+1 : ℕ) : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)} ≤
      (1-(p : ℝ))*(P[|DurationHistoryEvent Goals X n h]).real
        {ω | (s : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)} := by
  let H := DurationHistoryEvent Goals X n h
  let a := ∑ i ∈ Finset.range n, h i
  let T := fun ω => FirstHittingTime (Goals (n+1)) (fun j => X j ω)
  have HistoryMeasurable : MeasurableSet[F a] H :=
    DurationHistoryEventMeasurable F X AdaptedX Goals GoalMeasurable Nested Initially n h
  have GlobalHistoryMeasurable : MeasurableSet H := measurableSet_of_filtration HistoryMeasurable
  have StoppingT : IsStoppingTime F T := FirstHittingTimeProcessIsStoppingTime F X AdaptedX _ (GoalMeasurable (n+1))
  have SurvivalEvent (r : ℕ) :
      H ∩ {ω | (r : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)} =
        H ∩ {ω | ((a+r : ℕ) : WithTop ℕ) < T ω} := by
    ext ω
    constructor
    · intro Member
      refine ⟨Member.1, ?_⟩
      have Endpoint := DurationHistoryEndpoint Goals Nested Initially X n h ω Member.1
      change FirstHittingTime (Goals n) (fun t => X t ω) = (a : WithTop ℕ) at Endpoint
      have Survives := Member.2
      change (r : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω) at Survives
      unfold LevelDuration at Survives
      rw [Endpoint] at Survives
      exact (ExtendedNatDurationSurvival (T ω) a r).mp Survives
    · intro Member
      refine ⟨Member.1, ?_⟩
      have Endpoint := DurationHistoryEndpoint Goals Nested Initially X n h ω Member.1
      change FirstHittingTime (Goals n) (fun t => X t ω) = (a : WithTop ℕ) at Endpoint
      change (r : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)
      unfold LevelDuration
      rw [Endpoint]
      exact (ExtendedNatDurationSurvival (T ω) a r).mpr Member.2
  have CurrentMeasurable : MeasurableSet[F (a+s)] (H ∩ {ω | ((a+s : ℕ) : WithTop ℕ) < T ω}) :=
    (F.mono (Nat.le_add_right a s) H HistoryMeasurable).inter (StoppingT.measurableSet_gt (a+s))
  have LocalBound := Progress (a+s) (H ∩ {ω | ((a+s : ℕ) : WithTop ℕ) < T ω}) CurrentMeasurable (by
    intro ω Member
    refine ⟨?_, Member.2⟩
    rw [DurationHistoryEndpoint Goals Nested Initially X n h ω Member.1]
    exact_mod_cast Nat.le_add_right a s)
  have NextEvent : (H ∩ {ω | ((a+s : ℕ) : WithTop ℕ) < T ω}) ∩
      {ω | ((a+s+1 : ℕ) : WithTop ℕ) < T ω} = H ∩ {ω | ((a+(s+1) : ℕ) : WithTop ℕ) < T ω} := by
    ext ω
    constructor
    · intro Member
      exact ⟨Member.1.1, by simpa only [Nat.add_assoc] using Member.2⟩
    · intro Member
      have Next : ((a+s+1 : ℕ) : WithTop ℕ) < T ω := by
        simpa only [mem_ofPred_eq, Nat.add_assoc] using Member.2
      exact ⟨⟨Member.1, lt_of_le_of_lt (by exact_mod_cast Nat.le_succ (a+s)) Next⟩, Next⟩
  change P.real ((H ∩ {ω | ((a+s : ℕ) : WithTop ℕ) < T ω}) ∩
    {ω | ((a+s+1 : ℕ) : WithTop ℕ) < T ω}) ≤ _ at LocalBound
  rw [NextEvent] at LocalBound
  have ConditionalFormula (A : Set Ω) : (P[|H]).real A = (P H)⁻¹.toReal * P.real (H ∩ A) := by
    rw [measureReal_def, cond_apply GlobalHistoryMeasurable, ENNReal.toReal_mul]
    rfl
  rw [ConditionalFormula, ConditionalFormula, SurvivalEvent (s+1), SurvivalEvent s]
  have Scaled := mul_le_mul_of_nonneg_left LocalBound (ENNReal.toReal_nonneg : 0 ≤ (P H)⁻¹.toReal)
  calc
    _ ≤ (P H)⁻¹.toReal * ((1-(p : ℝ))*P.real (H ∩ {ω | ((a+s : ℕ) : WithTop ℕ) < T ω})) := Scaled
    _ = _ := by ring

/-- The entry-time identity also retains infinite earlier durations. -/
theorem ExtendedDurationHistoryEndpoint {Ω State : Type*} (Goals : ℕ → State → Prop)
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (X : ℕ → Ω → State) (n : ℕ) (h : Fin n → WithTop ℕ) (ω : Ω)
    (History : ExtendedNatPrefix (fun i ω => LevelDuration Goals i (fun t => X t ω)) n ω = h) :
    FirstHittingTime (Goals n) (fun t => X t ω) = ∑ i : Fin n, h i := by
  rw [← LevelDurationSum Goals Nested Initially (fun t => X t ω) n, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun History i

/-- The conditional contraction includes infinite histories, where later stages have zero duration. -/
theorem StageHistorySurvivalStep {Ω State : Type*} [MeasurableSpace Ω] [MeasurableSpace State]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → State) (AdaptedX : Adapted F X)
    (Goals : ℕ → State → Prop) (GoalMeasurable : ∀ j, MeasurableSet {x | Goals j x})
    (Nested : ∀ i x, Goals (i+1) x → Goals i x) (Initially : ∀ x, Goals 0 x)
    (n : ℕ) (p : I)
    (Progress : ∀ t (A : Set Ω), MeasurableSet[F t] A →
      (∀ ω ∈ A, FirstHittingTime (Goals n) (fun j => X j ω) ≤ (t : WithTop ℕ) ∧
        (t : WithTop ℕ) < FirstHittingTime (Goals (n+1)) (fun j => X j ω)) →
      P.real (A ∩ {ω | ((t+1 : ℕ) : WithTop ℕ) < FirstHittingTime (Goals (n+1)) (fun j => X j ω)}) ≤
        (1-(p : ℝ))*P.real A)
    (h : Fin n → WithTop ℕ) (s : ℕ) :
    (P[|ExtendedNatPrefix (fun i ω => LevelDuration Goals i (fun t => X t ω)) n ⁻¹' {h}]).real
        {ω | ((s+1 : ℕ) : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)} ≤
      (1-(p : ℝ))*(P[|ExtendedNatPrefix (fun i ω => LevelDuration Goals i (fun t => X t ω)) n ⁻¹' {h}]).real
        {ω | (s : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω)} := by
  classical
  let D := fun i ω => LevelDuration Goals i (fun t => X t ω)
  let H := ExtendedNatPrefix D n ⁻¹' {h}
  by_cases FiniteHistory : ∀ i, h i ≠ ⊤
  · let q : ℕ → ℕ := fun i => if Before : i < n then (h ⟨i, Before⟩).untop (FiniteHistory _) else 0
    have CoeQ (i : Fin n) : (q i : WithTop ℕ) = h i := by
      dsimp only [q]
      rw [dif_pos i.isLt]
      exact WithTop.coe_untop (h i) (FiniteHistory i)
    have Event : H = DurationHistoryEvent Goals X n q := by
      ext ω
      constructor
      · intro InHistory i Before
        have Value := congrFun InHistory (⟨i, Before⟩ : Fin n)
        exact Value.trans (CoeQ ⟨i, Before⟩).symm
      · intro InHistory
        change ExtendedNatPrefix D n ω = h
        funext i
        exact (InHistory i i.isLt).trans (CoeQ i)
    change (P[|H]).real {ω | ((s+1 : ℕ) : WithTop ℕ) < D n ω} ≤
      (1-(p : ℝ))*(P[|H]).real {ω | (s : WithTop ℕ) < D n ω}
    rw [Event]
    exact FiniteStageHistorySurvivalStep P F X AdaptedX Goals GoalMeasurable Nested Initially n p Progress q s
  · obtain ⟨i, Infinite⟩ : ∃ i, h i = ⊤ := by simpa only [not_forall, not_not] using FiniteHistory
    have SumInfinite : (∑ j : Fin n, h j) = ⊤ := WithTop.sum_eq_top.mpr ⟨i, Finset.mem_univ i, Infinite⟩
    have NoSurvival : H ∩ {ω | ((s+1 : ℕ) : WithTop ℕ) < D n ω} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω Member
      have Endpoint := ExtendedDurationHistoryEndpoint Goals Nested Initially X n h ω Member.1
      rw [SumInfinite] at Endpoint
      have Zero := LevelDurationAfterInfiniteEntry Goals n (fun t => X t ω) Endpoint
      have Survives : ((s+1 : ℕ) : WithTop ℕ) < LevelDuration Goals n (fun t => X t ω) := Member.2
      rw [Zero] at Survives
      exact (not_lt_of_ge zero_le) Survives
    have MeasurableD : Measurable (D n) :=
      LevelDurationMeasurable Goals GoalMeasurable X (fun _ => AdaptedX.measurable) n
    have MeasurableSurvival : MeasurableSet {ω | ((s+1 : ℕ) : WithTop ℕ) < D n ω} :=
      MeasurableD measurableSet_Ioi
    have ZeroConditional : (P[|H]).real {ω | ((s+1 : ℕ) : WithTop ℕ) < D n ω} = 0 := by
      rw [measureReal_def, cond_apply' MeasurableSurvival, NoSurvival,
        measure_empty, mul_zero, ENNReal.toReal_zero]
    change (P[|H]).real {ω | ((s+1 : ℕ) : WithTop ℕ) < D n ω} ≤ _
    rw [ZeroConditional]
    exact mul_nonneg (sub_nonneg.mpr p.2.2) measureReal_nonneg

end
end ECTheoryLib.Probability
