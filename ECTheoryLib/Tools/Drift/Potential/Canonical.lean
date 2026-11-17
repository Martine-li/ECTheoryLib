import ECTheoryLib.Probability.Processes.ScalarProcess
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Canonical conditional remaining-time potential

Source: Lengler, Chapter 2.5, printed pages 123--125, including footnote 30.
For an integrable extended-natural stopping time, condition the nonnegative
remaining runtime on the actual filtration. Its conditional decrease is one
while alive and zero after the hit; its first zero is the original runtime
almost surely. The initial conditional expectation retains random F0 data.

Finite expected runtime is essential to the real conversion and the drift
identities. Adaptation and the total conditional-expression identities alone
do not establish that finiteness. No finite state, bounded runtime, Markov
property, original absorption, or completed filtration is assumed. The stopped
potential agrees with E[T_real | F_t] - t before the hit; that raw expression
may be negative afterwards. This construction is a representation theorem,
rather than a way to establish an unknown runtime bound by assuming it finite.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real clock value. Its probabilistic use below is justified by finite
extended expectation; the value at infinity is not used as a runtime. -/
def CanonicalRuntimeReal (T : Ω → WithTop ℕ) (ω : Ω) : ℝ :=
  (ENat.toENNReal (T ω)).toReal

/-- Nonnegative residual of the total runtime at natural time t. -/
def CanonicalResidual (T : Ω → WithTop ℕ) (t : ℕ) (ω : Ω) : ℝ :=
  max (CanonicalRuntimeReal T ω - (t : ℝ)) 0

/-- Canonical remaining-time potential, stopped at the original runtime. -/
def CanonicalRemainingPotential (μ : Measure Ω)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : Ω → WithTop ℕ) (t : ℕ) : Ω → ℝ := μ[CanonicalResidual T t | F t]

theorem CanonicalResidualIntegrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    Integrable (CanonicalResidual T t) μ := by
  have Observable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun n : WithTop ℕ => ENat.toENNReal n)).comp Stopping.measurable'
  have Clock : Integrable (CanonicalRuntimeReal T) μ :=
    integrable_toReal_of_lintegral_ne_top Observable.aemeasurable FiniteMean
  exact (Clock.sub (integrable_const (t : ℝ))).pos_part

/-- Mathlib supplies an exactly adapted representative, without completing F. -/
theorem CanonicalRemainingPotentialAdapted (μ : Measure Ω)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ) :
    Adapted F (CanonicalRemainingPotential μ F T) := by
  intro t
  exact stronglyMeasurable_condExp.measurable

/-- Integrability of Mathlib's total conditional-expectation representative.
The genuine remaining-time interpretation additionally uses finite mean. -/
theorem CanonicalRemainingPotentialIntegrable (μ : Measure Ω)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : Ω → WithTop ℕ) (t : ℕ) :
    Integrable (CanonicalRemainingPotential μ F T t) μ := integrable_condExp

/-- Finite expectation excludes the infinite-clock default before this
integer residual identity is used. -/
theorem CanonicalResidualDifference (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    (fun ω => CanonicalResidual T t ω - CanonicalResidual T (t + 1) ω) =ᵐ[μ]
      ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) := by
  have Observable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun n : WithTop ℕ => ENat.toENNReal n)).comp Stopping.measurable'
  have FiniteAE := ae_lt_top Observable FiniteMean
  have Arithmetic (n : WithTop ℕ) (Finite : n ≠ ⊤) :
      max ((ENat.toENNReal n).toReal - (t : ℝ)) 0 -
        max ((ENat.toENNReal n).toReal - ((t + 1 : ℕ) : ℝ)) 0 =
      if (t : WithTop ℕ) < n then 1 else 0 := by
    obtain ⟨k, Equal⟩ := WithTop.ne_top_iff_exists.mp Finite
    rw [← Equal]
    change max ((k : ENNReal).toReal - (t : ℝ)) 0 -
      max ((k : ENNReal).toReal - ((t + 1 : ℕ) : ℝ)) 0 =
        if (t : WithTop ℕ) < (k : WithTop ℕ) then 1 else 0
    simp only [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
    by_cases Before : (t : WithTop ℕ) < (k : WithTop ℕ)
    · rw [if_pos Before]
      have NatBefore : t < k := by exact_mod_cast Before
      have Cast : (t : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt NatBefore
      rw [max_eq_left (show (0 : ℝ) ≤ (k : ℝ) - t by linarith),
        max_eq_left (show (0 : ℝ) ≤ (k : ℝ) - (t + 1) by linarith)]
      ring
    · have NatBefore : k ≤ t := by exact_mod_cast le_of_not_gt Before
      have Cast : (k : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr NatBefore
      simp only [if_neg Before, max_eq_right (show (k : ℝ) - t ≤ 0 by linarith),
        max_eq_right (show (k : ℝ) - (t + 1) ≤ 0 by linarith), sub_self]
  filter_upwards [FiniteAE] with ω Finite
  have NotTop : T ω ≠ ⊤ := by
    intro Top
    have EmbeddedTop : ENat.toENNReal (⊤ : WithTop ℕ) = (⊤ : ENNReal) := rfl
    rw [Top, EmbeddedTop] at Finite
    exact (lt_irrefl _ Finite).elim
  simpa only [CanonicalResidual, CanonicalRuntimeReal, Set.indicator_apply, Set.mem_ofPred_eq]
    using Arithmetic (T ω) NotTop

/-- Conditional decrease is exactly one while alive, and zero after the hit. -/
theorem CanonicalRemainingPotentialDrift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    (μ[fun ω => CanonicalRemainingPotential μ F T t ω -
      CanonicalRemainingPotential μ F T (t + 1) ω | F t]) =ᵐ[μ]
      ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) := by
  have Current := CanonicalResidualIntegrable μ F T Stopping FiniteMean t
  have Next := CanonicalResidualIntegrable μ F T Stopping FiniteMean (t + 1)
  have Linear := condExp_sub
    (CanonicalRemainingPotentialIntegrable μ F T t)
    (CanonicalRemainingPotentialIntegrable μ F T (t + 1)) (F t)
  have Self : μ[CanonicalRemainingPotential μ F T t | F t] =
      CanonicalRemainingPotential μ F T t :=
    condExp_of_stronglyMeasurable (F.le t) stronglyMeasurable_condExp integrable_condExp
  have Tower := condExp_condExp_of_le (μ := μ) (f := CanonicalResidual T (t + 1))
    (F.mono (Nat.le_succ t)) (F.le (t + 1))
  have ResidualLinear := condExp_sub Current Next (F t)
  have Difference := condExp_congr_ae (m := F t)
    (CanonicalResidualDifference μ F T Stopping FiniteMean t)
  have AliveMeasurable := Stopping.measurableSet_gt t
  have AliveAmbient : MeasurableSet {ω | (t : WithTop ℕ) < T ω} :=
    (F.le t) _ AliveMeasurable
  have IndicatorFixed :
      μ[({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) | F t] =
        ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable (F.le t)
      (stronglyMeasurable_const.indicator AliveMeasurable)
      ((integrable_const (1 : ℝ)).indicator AliveAmbient)
  filter_upwards [Linear, Tower, ResidualLinear, Difference] with ω LY TY LR DR
  rw [Self] at LY
  change (μ[fun u => CanonicalRemainingPotential μ F T t u -
    CanonicalRemainingPotential μ F T (t + 1) u | F t]) ω = _ at LY
  rw [LY]
  change (μ[CanonicalResidual T t | F t]) ω -
    (μ[μ[CanonicalResidual T (t + 1) | F (t + 1)] | F t]) ω = _
  rw [TY]
  exact LR.symm.trans (DR.trans (congrFun IndicatorFixed ω))

/-- At time zero, the representative retains exactly the conditional clock
given F0. This identity of total conditional-expectation expressions does not
by itself establish finite expectation of the clock. -/
theorem CanonicalRemainingPotentialInitial (μ : Measure Ω)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ) :
    CanonicalRemainingPotential μ F T 0 = μ[CanonicalRuntimeReal T | F 0] := by
  have Initial : CanonicalResidual T 0 = CanonicalRuntimeReal T := by
    funext ω
    simp only [CanonicalResidual, Nat.cast_zero, sub_zero,
      max_eq_left (show 0 ≤ CanonicalRuntimeReal T ω from ENNReal.toReal_nonneg)]
  unfold CanonicalRemainingPotential
  rw [Initial]

/-- The initial integral is the original finite extended expectation in real
coordinates; F0 may contain genuine random initialization information. -/
theorem CanonicalRemainingPotentialInitialMean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) :
    ExpectedValue μ (CanonicalRemainingPotential μ F T 0) =
      (∫⁻ ω, ENat.toENNReal (T ω) ∂μ).toReal := by
  have Observable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun n : WithTop ℕ => ENat.toENNReal n)).comp Stopping.measurable'
  change (∫ ω, CanonicalRemainingPotential μ F T 0 ω ∂μ) = _
  rw [CanonicalRemainingPotentialInitial, integral_condExp (F.le 0)]
  exact integral_toReal Observable.aemeasurable (ae_lt_top Observable FiniteMean)

/-- Nonnegativity holds for the conditional-expectation representative almost
surely; no completion of the filtration is required. -/
theorem CanonicalRemainingPotentialNonnegative (μ : Measure Ω)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : Ω → WithTop ℕ) (t : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ CanonicalRemainingPotential μ F T t ω := by
  exact condExp_nonneg (Filter.Eventually.of_forall fun _ => le_max_right _ _)

/-- While the runtime has not ended, the canonical potential is at least one.
The indicator formulation also retains the zero lower bound after the hit. -/
theorem CanonicalRemainingPotentialAliveLowerBound (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
      CanonicalRemainingPotential μ F T t := by
  have AliveMeasurable := Stopping.measurableSet_gt t
  have AliveAmbient : MeasurableSet {ω | (t : WithTop ℕ) < T ω} :=
    (F.le t) _ AliveMeasurable
  have IndicatorIntegrable :
      Integrable (({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator AliveAmbient
  have IndicatorFixed :
      μ[({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) | F t] =
        ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable (F.le t)
      (stronglyMeasurable_const.indicator AliveMeasurable) IndicatorIntegrable
  have RawLower :
      ({ω | (t : WithTop ℕ) < T ω}).indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ]
        CanonicalResidual T t := by
    filter_upwards [CanonicalResidualDifference μ F T Stopping FiniteMean t] with ω Difference
    have Nonnegative : 0 ≤ CanonicalResidual T (t + 1) ω := le_max_right _ _
    linarith
  have Monotone := condExp_mono (m := F t) IndicatorIntegrable
    (CanonicalResidualIntegrable μ F T Stopping FiniteMean t) RawLower
  simpa only [IndicatorFixed, CanonicalRemainingPotential] using Monotone

omit [MeasurableSpace Ω] in
/-- The stopped residual is pointwise zero after a finite hit, including on
exceptional paths; this does not use conditional expectation. -/
theorem CanonicalResidualZeroAfter (T : Ω → WithTop ℕ) (t : ℕ) (ω : Ω)
    (Hit : T ω ≤ (t : WithTop ℕ)) : CanonicalResidual T t ω = 0 := by
  have NotTop : T ω ≠ ⊤ := ne_of_lt (lt_of_le_of_lt Hit (WithTop.coe_lt_top t))
  obtain ⟨k, Equal⟩ := WithTop.ne_top_iff_exists.mp NotTop
  have Before : (k : WithTop ℕ) ≤ (t : WithTop ℕ) := Equal.le.trans Hit
  have NatBefore : k ≤ t := by exact_mod_cast Before
  have Cast : (k : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr NatBefore
  unfold CanonicalResidual CanonicalRuntimeReal
  rw [← Equal]
  change max ((k : ENNReal).toReal - (t : ℝ)) 0 = 0
  rw [ENNReal.toReal_natCast, max_eq_right (sub_nonpos.mpr Cast)]

/-- Past measurability of the hit event transfers the stopped residual's zero
value through conditional expectation. -/
theorem CanonicalRemainingPotentialZeroAfter (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    ∀ᵐ ω ∂μ, T ω ≤ (t : WithTop ℕ) →
      CanonicalRemainingPotential μ F T t ω = 0 := by
  have RawZero : ({ω | T ω ≤ (t : WithTop ℕ)}).indicator (CanonicalResidual T t) = 0 := by
    funext ω
    by_cases Hit : T ω ≤ (t : WithTop ℕ)
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_pos Hit,
        CanonicalResidualZeroAfter T t ω Hit, Pi.zero_apply]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_neg Hit, Pi.zero_apply]
  have HitMeasurable : MeasurableSet[F t] {ω | T ω ≤ (t : WithTop ℕ)} := Stopping t
  have Pullout :
      μ[({ω | T ω ≤ (t : WithTop ℕ)}).indicator (CanonicalResidual T t) | F t] =ᵐ[μ]
        ({ω | T ω ≤ (t : WithTop ℕ)}).indicator (μ[CanonicalResidual T t | F t]) :=
    condExp_indicator (CanonicalResidualIntegrable μ F T Stopping FiniteMean t) HitMeasurable
  rw [RawZero, condExp_zero] at Pullout
  filter_upwards [Pullout] with ω Equal Hit
  have Value := Equal.symm
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, if_pos Hit, Pi.zero_apply,
    CanonicalRemainingPotential] using Value

/-- At each natural time, zero potential characterizes having already hit.
The statement is almost sure for the exactly adapted representative. -/
theorem CanonicalRemainingPotentialZeroIff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    ∀ᵐ ω ∂μ, CanonicalRemainingPotential μ F T t ω = 0 ↔ T ω ≤ (t : WithTop ℕ) := by
  filter_upwards [CanonicalRemainingPotentialAliveLowerBound μ F T Stopping FiniteMean t,
    CanonicalRemainingPotentialZeroAfter μ F T Stopping FiniteMean t] with ω Lower After
  constructor
  · intro Zero
    by_contra Before
    have Alive : (t : WithTop ℕ) < T ω := lt_of_not_ge Before
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_pos Alive, Zero] at Lower
    norm_num at Lower
  · exact After

/-- The original stopping time is the first zero of the canonical potential,
outside a single null set covering all natural times. -/
theorem CanonicalRemainingPotentialFirstZero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) :
    ZeroHittingTime (CanonicalRemainingPotential μ F T) =ᵐ[μ] T := by
  have EveryTime := ae_all_iff.mpr
    (CanonicalRemainingPotentialZeroIff μ F T Stopping FiniteMean)
  have Observable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun n : WithTop ℕ => ENat.toENNReal n)).comp Stopping.measurable'
  filter_upwards [EveryTime, ae_lt_top Observable FiniteMean] with ω Criteria Finite
  have NotTop : T ω ≠ ⊤ := by
    intro Top
    have EmbeddedTop : ENat.toENNReal (⊤ : WithTop ℕ) = (⊤ : ENNReal) := rfl
    rw [Top, EmbeddedTop] at Finite
    exact (lt_irrefl _ Finite).elim
  obtain ⟨k, Equal⟩ := WithTop.ne_top_iff_exists.mp NotTop
  have AtK : CanonicalRemainingPotential μ F T k ω = 0 :=
    (Criteria k).mpr Equal.ge
  have FirstUpper : ZeroHittingTime (CanonicalRemainingPotential μ F T) ω ≤ (k : WithTop ℕ) :=
    (FirstHittingTimeLeIff (fun x : ℝ => x = 0)
      (fun s => CanonicalRemainingPotential μ F T s ω) k).mpr ⟨k, le_rfl, AtK⟩
  have FirstFinite : ZeroHittingTime (CanonicalRemainingPotential μ F T) ω ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt FirstUpper (WithTop.coe_lt_top k))
  obtain ⟨j, FirstEqual⟩ := WithTop.ne_top_iff_exists.mp FirstFinite
  have HitByJ : ZeroHittingTime (CanonicalRemainingPotential μ F T) ω ≤ (j : WithTop ℕ) :=
    FirstEqual.ge
  obtain ⟨i, BeforeJ, AtZero⟩ :=
    (FirstHittingTimeLeIff (fun x : ℝ => x = 0)
      (fun s => CanonicalRemainingPotential μ F T s ω) j).mp HitByJ
  have BeforeI : T ω ≤ (i : WithTop ℕ) := (Criteria i).mp AtZero
  have BeforeJ' : (i : WithTop ℕ) ≤ (j : WithTop ℕ) := by exact_mod_cast BeforeJ
  exact le_antisymm (FirstUpper.trans_eq Equal) ((BeforeI.trans BeforeJ').trans_eq FirstEqual)

/-- On the surviving event, stopping the residual does not change the book's
raw expression E[T_real | F_t] - t. The raw expression need not be nonnegative
after the original runtime has ended. -/
theorem CanonicalRemainingPotentialRawBefore (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (T : Ω → WithTop ℕ)
    (Stopping : IsStoppingTime F T)
    (FiniteMean : (∫⁻ ω, ENat.toENNReal (T ω) ∂μ) ≠ ⊤) (t : ℕ) :
    ∀ᵐ ω ∂μ, (t : WithTop ℕ) < T ω →
      CanonicalRemainingPotential μ F T t ω = (μ[CanonicalRuntimeReal T | F t]) ω - (t : ℝ) := by
  have Observable : Measurable (fun ω => ENat.toENNReal (T ω)) :=
    (measurable_of_countable (fun n : WithTop ℕ => ENat.toENNReal n)).comp Stopping.measurable'
  have Clock : Integrable (CanonicalRuntimeReal T) μ :=
    integrable_toReal_of_lintegral_ne_top Observable.aemeasurable FiniteMean
  have AliveMeasurable := Stopping.measurableSet_gt t
  have RawStopped :
      ({ω | (t : WithTop ℕ) < T ω}).indicator (CanonicalResidual T t) =ᵐ[μ]
        ({ω | (t : WithTop ℕ) < T ω}).indicator
          (fun ω => CanonicalRuntimeReal T ω - (t : ℝ)) := by
    filter_upwards [CanonicalResidualDifference μ F T Stopping FiniteMean t] with ω Difference
    by_cases Alive : (t : WithTop ℕ) < T ω
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_pos Alive] at Difference ⊢
      have NextNonnegative : 0 ≤ CanonicalResidual T (t + 1) ω := le_max_right _ _
      have Positive : 0 < CanonicalResidual T t ω := by linarith
      have RawNonnegative : 0 ≤ CanonicalRuntimeReal T ω - (t : ℝ) := by
        by_contra Negative
        have Value : CanonicalResidual T t ω = 0 :=
          max_eq_right (le_of_lt (lt_of_not_ge Negative))
        rw [Value] at Positive
        exact (lt_irrefl _ Positive).elim
      exact max_eq_left RawNonnegative
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_neg Alive]
  have Linear := condExp_sub Clock (integrable_const (t : ℝ)) (F t)
  have Constant : μ[(fun _ : Ω => (t : ℝ)) | F t] = fun _ => (t : ℝ) :=
    condExp_const (F.le t) (t : ℝ)
  have PulloutCurrent :
      μ[({ω | (t : WithTop ℕ) < T ω}).indicator (CanonicalResidual T t) | F t] =ᵐ[μ]
        ({ω | (t : WithTop ℕ) < T ω}).indicator (μ[CanonicalResidual T t | F t]) :=
    condExp_indicator (CanonicalResidualIntegrable μ F T Stopping FiniteMean t) AliveMeasurable
  have PulloutRaw :
      μ[({ω | (t : WithTop ℕ) < T ω}).indicator
        (fun ω => CanonicalRuntimeReal T ω - (t : ℝ)) | F t] =ᵐ[μ]
        ({ω | (t : WithTop ℕ) < T ω}).indicator
          (μ[fun ω => CanonicalRuntimeReal T ω - (t : ℝ) | F t]) :=
    condExp_indicator (Clock.sub (integrable_const (t : ℝ))) AliveMeasurable
  have Same := condExp_congr_ae (m := F t) RawStopped
  filter_upwards [PulloutCurrent, Same, PulloutRaw, Linear] with ω Current Equal Raw Sum Alive
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_pos Alive] at Current Raw
  rw [Constant] at Sum
  exact Current.symm.trans (Equal.trans (Raw.trans Sum))

end
end ECTheoryLib.Tools.Drift

