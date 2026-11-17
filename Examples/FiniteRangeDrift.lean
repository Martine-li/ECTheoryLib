import ECTheoryLib.Tools.Drift.Additive
import ECTheoryLib.Probability.Processes.ConditionalDrift

/-! A finite-range obstruction to globally positive drift away from a target. See docs/SOURCE_NOTES.md or docs/COVERAGE.md for source relations. -/




namespace NegativeDriftSourceAudit
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- A common finite range cannot have strictly negative signed drift at every
reachable state above a threshold, at every time. Use the largest state that
has positive mass at any time, not a possibly unreachable maximum of S. -/
theorem GlobalAwayDriftImpossible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (S : Finset ℝ)
    (MeasurableX : ∀ t, Measurable (X t)) (InS : ∀ t ω, X t ω ∈ S)
    (a : ℝ)
    (Away : ∀ t s, s ∈ S → a < s → 0 < μ (StateEvent X t s) → StateDrift μ X t s < 0)
    (t₀ : ℕ) (s₀ : ℝ) (Above : a < s₀) : μ (StateEvent X t₀ s₀) = 0 := by
  classical
  by_contra Positive
  let R := S.filter (fun s => ∃ t, 0 < μ (StateEvent X t s))
  have InitialInS : s₀ ∈ S := by
    obtain ⟨ω, Value⟩ := nonempty_of_measure_ne_zero Positive
    change X t₀ ω = s₀ at Value
    rw [← Value]
    exact InS t₀ ω
  have InitialInR : s₀ ∈ R := Finset.mem_filter.mpr ⟨InitialInS, t₀, bot_lt_iff_ne_bot.mpr Positive⟩
  have Nonempty : R.Nonempty := ⟨s₀, InitialInR⟩
  let M := R.max' Nonempty
  have MaxInR : M ∈ R := Finset.max'_mem R Nonempty
  have MaxInS : M ∈ S := (Finset.mem_filter.mp MaxInR).1
  obtain ⟨u, AtMaxPositive⟩ := (Finset.mem_filter.mp MaxInR).2
  have AboveMax : a < M := Above.trans_le (Finset.le_max' R s₀ InitialInR)
  have NextBound : ∀ᵐ ω ∂μ, X (u+1) ω ≤ M := by
    have Each (s : {s // s ∈ S}) : ∀ᵐ ω ∂μ, X (u+1) ω = s.val → s.val ≤ M := by
      by_cases Reachable : s.val ∈ R
      · exact ae_of_all _ (fun _ _ => Finset.le_max' R s.val Reachable)
      · have Null : μ (StateEvent X (u+1) s.val) = 0 := by
          by_contra Nonzero
          apply Reachable
          exact Finset.mem_filter.mpr ⟨s.property, u+1, bot_lt_iff_ne_bot.mpr Nonzero⟩
        have Avoid : ∀ᵐ ω ∂μ, X (u+1) ω ≠ s.val := by
          rw [ae_iff]
          simp only [not_not]
          exact Null
        filter_upwards [Avoid] with ω Different
        intro Equal
        exact False.elim (Different Equal)
    have All := (ae_all_iff).mpr Each
    filter_upwards [All] with ω AllAt
    exact AllAt ⟨X (u+1) ω, InS (u+1) ω⟩ rfl
  have NonnegativeDrift : 0 ≤ StateDrift μ X u M := by
    rw [StateDrift, EventConditionalExpectation]
    apply div_nonneg _ ENNReal.toReal_nonneg
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae NextBound,
      ae_restrict_mem (StateEventMeasurable X u M (MeasurableX u))] with ω Future Current
    change X u ω = M at Current
    rw [Current]
    exact sub_nonneg.mpr Future
  exact (not_lt_of_ge NonnegativeDrift) (Away u M MaxInS AboveMax AtMaxPositive)

/-- The same necessary condition follows from the full-filtration drift bound
in the printed theorem. All integrability comes from its common finite range. -/
theorem GlobalAwayDriftImpossibleOfCondExp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (S : Finset ℝ)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (AdaptedX : Adapted F X)
    (InS : ∀ t ω, X t ω ∈ S) (a Delta : ℝ) (PositiveDelta : 0 < Delta)
    (Away : ∀ t, ∀ᵐ ω ∂μ, a < X t ω →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta)
    (t₀ : ℕ) (s₀ : ℝ) (Above : a < s₀) : μ (StateEvent X t₀ s₀) = 0 := by
  have MeasurableX : ∀ t, Measurable (X t) := fun t => (AdaptedX t).mono (F.le t) le_rfl
  have IntegrableX (t : ℕ) : Integrable (X t) μ :=
    FiniteStateIntegrable μ (X t) S (MeasurableX t) (ae_of_all _ (InS t))
  apply GlobalAwayDriftImpossible μ X S MeasurableX InS a _ t₀ s₀ Above
  intro t s _InS AboveS Positive
  have PastEvent : MeasurableSet[F t] (StateEvent X t s) :=
    measurableSet_eq_fun (AdaptedX t) measurable_const
  have AmbientEvent := F.le t _ PastEvent
  have DecreaseIntegrable : Integrable (fun ω => X t ω-X (t+1) ω) μ :=
    (IntegrableX t).sub (IntegrableX (t+1))
  have ConditionalIntegral := setIntegral_condExp (F.le t) DecreaseIntegrable PastEvent
  have NumeratorBound : (∫ ω in StateEvent X t s, X t ω-X (t+1) ω ∂μ) ≤
      (μ (StateEvent X t s)).toReal * (-Delta) := by
    rw [← ConditionalIntegral]
    have Bound : (∫ ω in StateEvent X t s,
        (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ∂μ) ≤
        ∫ _ω in StateEvent X t s, -Delta ∂μ := by
      apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
      apply (ae_restrict_iff' AmbientEvent).mpr
      filter_upwards [Away t] with ω Bound
      intro Current
      change X t ω = s at Current
      apply Bound
      rw [Current]
      exact AboveS
    rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at Bound
    exact Bound
  have PositiveReal : 0 < (μ (StateEvent X t s)).toReal :=
    ENNReal.toReal_pos Positive.ne' (measure_ne_top _ _)
  have DriftBound : StateDrift μ X t s ≤ -Delta := by
    rw [StateDrift, EventConditionalExpectation]
    apply (div_le_iff₀ PositiveReal).mpr
    rw [mul_comm]
    exact NumeratorBound
  linarith

/-- In particular, the printed combination of a common finite state space,
initial position above the threshold, and drift away on the entire upper
half-line has no model. The jump-tail assumption is not needed to contradict it. -/
theorem PrintedFiniteModelEmpty {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (S : Finset ℝ)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (AdaptedX : Adapted F X)
    (InS : ∀ t ω, X t ω ∈ S) (a Delta : ℝ) (PositiveDelta : 0 < Delta)
    (InitiallyAbove : ∀ᵐ ω ∂μ, a < X 0 ω)
    (Away : ∀ t, ∀ᵐ ω ∂μ, a < X t ω →
      (μ[fun ω => X t ω-X (t+1) ω | F t]) ω ≤ -Delta) : False := by
  classical
  have Each (s : {s // s ∈ S}) : ∀ᵐ ω ∂μ, X 0 ω = s.val → s.val ≤ a := by
    by_cases Above : a < s.val
    · have Null := GlobalAwayDriftImpossibleOfCondExp μ X S F AdaptedX InS a Delta
        PositiveDelta Away 0 s.val Above
      have Avoid : ∀ᵐ ω ∂μ, X 0 ω ≠ s.val := by
        rw [ae_iff]
        simp only [not_not]
        exact Null
      filter_upwards [Avoid] with ω Different
      intro Same
      exact False.elim (Different Same)
    · exact ae_of_all _ (fun _ _ => le_of_not_gt Above)
  have All := (ae_all_iff).mpr Each
  obtain ⟨ω, Above, Upper⟩ := (InitiallyAbove.and All).exists
  exact (not_le_of_gt Above) (Upper ⟨X 0 ω, InS 0 ω⟩ rfl)

end
end NegativeDriftSourceAudit
