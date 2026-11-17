import ECTheoryLib.Probability.Processes.PathDrift
import ECTheoryLib.Probability.Processes.PathInvariant
import ECTheoryLib.Probability.Processes.FiniteStateBounds

/-!
# Bounded local drift on countable state representations

Full states may be lists and therefore form an infinite type even when a concrete
run preserves population size. Uniform bounds on the integrands supply the
integrability previously obtained from finite full states. This module extends
the local-to-path expectation bridge without replacing the actual list process
or changing the scalar drift theorem's pointwise finite-range requirement.
-/
namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {State : Type*} [Countable State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Iterated expectation for a uniformly bounded real function of adjacent
states on the actual countable-state path law. -/
theorem PathMeasureTransitionIntegralOfBounded (Step : Transition State) (Initial : PMF State)
    (t : ℕ) (f : State → State → ℝ) (B : ℝ) (Bound : ∀ x y, ‖f x y‖ ≤ B) :
    (∫ Path, f (Path t) (Path (t + 1)) ∂PathMeasure Step Initial) =
      ∫ Path, (∫ y, f (Path t) y ∂(Step (Path t)).toMeasure) ∂PathMeasure Step Initial := by
  let PairFunction : (Finset.Iic t → State) × State → ℝ :=
    fun Pair => f (HistoryLast t Pair.1) Pair.2
  have PairMeasurable : Measurable (fun Path : ℕ → State =>
      (Preorder.frestrictLe t Path, Path (t + 1))) :=
    (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t + 1))
  have FunctionMeasurable : Measurable PairFunction := measurable_of_countable _
  have FunctionIntegrable : Integrable PairFunction
      ((PathMeasure Step Initial).map (Preorder.frestrictLe t) ⊗ₘ HistoryKernel Step t) :=
    (integrable_const B).mono' FunctionMeasurable.aestronglyMeasurable
      (ae_of_all _ (fun Pair => Bound (HistoryLast t Pair.1) Pair.2))
  have HistoryMeasurable : Measurable (fun History : Finset.Iic t → State =>
      ∫ y, f (HistoryLast t History) y ∂(Step (HistoryLast t History)).toMeasure) :=
    measurable_of_countable _
  calc
    (∫ Path, f (Path t) (Path (t + 1)) ∂PathMeasure Step Initial) =
        ∫ Pair, PairFunction Pair ∂((PathMeasure Step Initial).map
          (fun Path : ℕ → State => (Preorder.frestrictLe t Path, Path (t + 1)))) := by
      rw [integral_map_of_stronglyMeasurable PairMeasurable FunctionMeasurable.stronglyMeasurable]
      rfl
    _ = ∫ Pair, PairFunction Pair ∂((PathMeasure Step Initial).map
        (Preorder.frestrictLe t) ⊗ₘ HistoryKernel Step t) := by rw [PathMeasureJointLaw]
    _ = ∫ History, (∫ y, f (HistoryLast t History) y ∂(Step (HistoryLast t History)).toMeasure)
        ∂((PathMeasure Step Initial).map (Preorder.frestrictLe t)) := by
      rw [Measure.integral_compProd FunctionIntegrable]
      rfl
    _ = ∫ Path, (∫ y, f (Path t) y ∂(Step (Path t)).toMeasure) ∂PathMeasure Step Initial := by
      rw [integral_map_of_stronglyMeasurable (Preorder.measurable_frestrictLe t)
        HistoryMeasurable.stronglyMeasurable]
      rfl

/-- Legal-state local drift bounds survive conditioning on a nonzero potential
level of positive probability. Full states need only be countable; the potential
is uniformly bounded in norm, and may be signed in this bridge alone. -/
theorem PathMeasureStateDriftLowerBoundOfBounded (Step : Transition State) (Initial : PMF State)
    (V : State → ℝ) (d : ℝ → ℝ) (Valid : State → Prop)
    (B : ℝ) (Bound : ∀ x, ‖V x‖ ≤ B)
    (LocalDrift : ∀ x, Valid x → V x ≠ 0 → d (V x) ≤ ∫ y, V x - V y ∂(Step x).toMeasure)
    (t : ℕ) (s : ℝ) (Nonzero : s ≠ 0)
    (ValidAtTime : ∀ᵐ Path ∂PathMeasure Step Initial, Valid (Path t))
    (EventPositive : 0 < (PathMeasure Step Initial) (StateEvent (fun t Path => V (Path t)) t s)) :
    d s ≤ StateDrift (PathMeasure Step Initial) (fun t Path => V (Path t)) t s := by
  classical
  let μ := PathMeasure Step Initial
  let X : ℕ → (ℕ → State) → ℝ := fun t Path => V (Path t)
  let Event := StateEvent X t s
  let EventDecrease : State → State → ℝ := fun x y => if V x = s then V x - V y else 0
  have BNonnegative : 0 ≤ B := by
    obtain ⟨x⟩ := Initial.support_nonempty
    exact (norm_nonneg (V x)).trans (Bound x)
  have EventBound (x y : State) : ‖EventDecrease x y‖ ≤ 2 * B := by
    unfold EventDecrease
    split_ifs
    · exact (norm_sub_le _ _).trans (by linarith [Bound x, Bound y])
    · simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) BNonnegative
  have AverageBound (x : State) : ‖∫ y, EventDecrease x y ∂(Step x).toMeasure‖ ≤ 2 * B := by
    have BoundMean := norm_integral_le_of_norm_le_const (μ := (Step x).toMeasure)
      (ae_of_all _ (EventBound x))
    simpa only [probReal_univ, mul_one] using BoundMean
  have EventMeasurable : MeasurableSet Event :=
    StateEventMeasurable X t s ((measurable_of_countable V).comp (measurable_pi_apply t))
  have AverageLower : ∀ᵐ Path ∂μ, (if V (Path t) = s then d s else 0) ≤
      ∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure := by
    filter_upwards [ValidAtTime] with Path IsValid
    by_cases AtLevel : V (Path t) = s
    · simp only [EventDecrease, AtLevel, if_true]
      have CurrentNonzero : V (Path t) ≠ 0 := fun Zero => Nonzero (AtLevel.symm.trans Zero)
      have Local := LocalDrift (Path t) IsValid CurrentNonzero
      rw [AtLevel] at Local
      exact Local
    · simp only [EventDecrease, AtLevel, if_false, integral_zero, le_refl]
  have IndicatorEquality : (fun Path : ℕ → State => if V (Path t) = s then d s else 0) =
      Event.indicator (fun _ => d s) := rfl
  have LeftIntegrable : Integrable (fun Path : ℕ → State => if V (Path t) = s then d s else 0) μ := by
    rw [IndicatorEquality]
    exact (integrable_const _).indicator EventMeasurable
  have RightMeasurable : Measurable (fun Path : ℕ → State =>
      ∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure) :=
    (measurable_of_countable (fun x => ∫ y, EventDecrease x y ∂(Step x).toMeasure)).comp
      (measurable_pi_apply t)
  have RightIntegrable : Integrable (fun Path : ℕ → State =>
      ∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure) μ :=
    (integrable_const (2 * B)).mono' RightMeasurable.aestronglyMeasurable
      (ae_of_all _ (fun Path => AverageBound (Path t)))
  -- Boundedness justifies both integrals before averaging the local inequality.
  have IntegralLower := integral_mono_ae LeftIntegrable RightIntegrable AverageLower
  rw [IndicatorEquality, integral_indicator_const _ EventMeasurable] at IntegralLower
  have Numerator : (∫ Path in Event, X t Path - X (t + 1) Path ∂μ) =
      ∫ Path, (∫ y, EventDecrease (Path t) y ∂(Step (Path t)).toMeasure) ∂μ := by
    rw [← integral_indicator EventMeasurable]
    change (∫ Path, EventDecrease (Path t) (Path (t + 1)) ∂μ) = _
    exact PathMeasureTransitionIntegralOfBounded Step Initial t EventDecrease (2 * B) EventBound
  rw [← Numerator] at IntegralLower
  have EventRealPositive : 0 < (μ Event).toReal :=
    ENNReal.toReal_pos EventPositive.ne' (measure_ne_top μ Event)
  change d s ≤ (∫ Path in Event, X t Path - X (t + 1) Path ∂μ) / (μ Event).toReal
  apply (le_div_iff₀ EventRealPositive).mpr
  change (μ Event).toReal * d s ≤ _ at IntegralLower
  simpa only [mul_comm] using IntegralLower

end
end ECTheoryLib.Probability
