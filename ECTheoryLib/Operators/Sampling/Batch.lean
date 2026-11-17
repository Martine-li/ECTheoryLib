import ECTheoryLib.Operators.Selection.Population
import ECTheoryLib.Probability.PMF.BoundedPMF

/-!
# Independent batch success

For a fixed sampling law, the probability of at least one success in N independent
samples is `1 - (1 - q)^N`. The lower bound `x / 2` applies whenever `0 ≤ x ≤ 1`
and `x ≤ N*q`. This converts a parent-selection factor of `1/N` into constant
progress for an entire generation, while allowing repeated sample values.
-/
namespace ECTheoryLib.Operators.Sampling
open MeasureTheory Probability Selection
noncomputable section

/-- The zero-one real indicator of an event on a sample. -/
def EventValue {α : Type*} (Event : α → Prop) (x : α) : ℝ := by
  classical
  exact if Event x then 1 else 0

theorem EventValueNonnegative {α : Type*} (Event : α → Prop) (x : α) : 0 ≤ EventValue Event x := by
  unfold EventValue
  split_ifs <;> norm_num

theorem EventValueBound {α : Type*} (Event : α → Prop) (x : α) : ‖EventValue Event x‖ ≤ 1 := by
  unfold EventValue
  split_ifs <;> norm_num

/-- Expected event indicator under a PMF. Its probability interpretation requires
a measurable event, automatic for the countable discrete spaces in the results below. -/
def EventProbability {α : Type*} [MeasurableSpace α] (p : PMF α) (Event : α → Prop) : ℝ :=
  ∫ x, EventValue Event x ∂p.toMeasure

theorem EventProbabilityNonnegative {α : Type*} [MeasurableSpace α]
    (p : PMF α) (Event : α → Prop) : 0 ≤ EventProbability p Event :=
  integral_nonneg (EventValueNonnegative Event)

theorem EventProbabilityLeOne {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (Event : α → Prop) : EventProbability p Event ≤ 1 := by
  apply (le_abs_self _).trans
  have Bound := norm_integral_le_of_norm_le_const (μ := p.toMeasure) (ae_of_all _ (EventValueBound Event))
  simpa only [EventProbability, Real.norm_eq_abs, probReal_univ, mul_one] using Bound

/-- Complementary events have complementary probabilities; bounded indicators
ensure that the subtraction of real integrals is legitimate. -/
theorem EventProbabilityComplement {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (Event : α → Prop) :
    EventProbability p (fun x => ¬ Event x) = 1 - EventProbability p Event := by
  have Complement : EventValue (fun x => ¬ Event x) = fun x => 1 - EventValue Event x := by
    funext x
    by_cases Hit : Event x
    · simp [EventValue, Hit]
    · simp [EventValue, Hit]
  rw [EventProbability, Complement, integral_sub (integrable_const _)
    (PMFIntegrableOfBounded p _ 1 (EventValueBound Event)), integral_const]
  simp only [probReal_univ, one_smul, EventProbability]

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace (List α)] [MeasurableSingletonClass (List α)]

/-- The probability that every sample misses the event is the product of the
single-sample miss probabilities. The empty batch misses with probability one. -/
theorem IndependentSamplesMiss (p : PMF α) (Event : α → Prop) (N : ℕ) :
    EventProbability (IndependentSamples p N) (fun L => ∀ x ∈ L, ¬ Event x) =
      (1 - EventProbability p Event) ^ N := by
  induction N with
  | zero => simp [EventProbability, IndependentSamples, EventValue, PMF.toMeasure_pure]
  | succ N Previous =>
      unfold EventProbability at Previous ⊢
      rw [IndependentSamples, PMFIntegralBindOfBounded _ _ _ 1
        (EventValueBound (fun L => ∀ x ∈ L, ¬ Event x))]
      simp_rw [PMFIntegralMapCountable]
      have Cons (x : α) :
          (∫ L, EventValue (fun L => ∀ y ∈ L, ¬ Event y) (x :: L)
            ∂(IndependentSamples p N).toMeasure) =
          EventValue (fun y => ¬ Event y) x * (1 - EventProbability p Event) ^ N := by
        by_cases Hit : Event x
        · simp only [EventValue, List.forall_mem_cons, Hit, not_true_eq_false, false_and,
            if_false, integral_zero, zero_mul]
        · have Remove : (fun L : List α => EventValue (fun L => ∀ y ∈ L, ¬ Event y) (x :: L)) =
              EventValue (fun L => ∀ y ∈ L, ¬ Event y) := by
            funext L
            have Same : (∀ y ∈ x :: L, ¬ Event y) ↔ (∀ y ∈ L, ¬ Event y) := by
              constructor
              · intro All y Present
                exact All y (List.mem_cons_of_mem x Present)
              · intro All y Present
                rcases List.mem_cons.mp Present with Equal | InTail
                · exact Equal ▸ Hit
                · exact All y InTail
            exact congrArg (fun P : Prop => @ite ℝ P (Classical.propDecidable P) 1 0) (propext Same)
          rw [Remove]
          simp only [EventValue, Hit, not_false_eq_true, if_true, one_mul]
          exact Previous
      simp_rw [Cons]
      rw [integral_mul_const]
      change EventProbability p (fun x => ¬ Event x) * _ = _
      rw [EventProbabilityComplement, pow_succ]
      unfold EventProbability
      ring

/-- Exact probability of at least one successful sample in the actual ordered batch law. -/
theorem IndependentSamplesSuccess (p : PMF α) (Event : α → Prop) (N : ℕ) :
    EventProbability (IndependentSamples p N) (fun L => ∃ x ∈ L, Event x) =
      1 - (1 - EventProbability p Event) ^ N := by
  have Miss := IndependentSamplesMiss p Event N
  have Complement := EventProbabilityComplement (IndependentSamples p N) (fun L => ∃ x ∈ L, Event x)
  have Negation : (fun L : List α => ¬ ∃ x ∈ L, Event x) = (fun L => ∀ x ∈ L, ¬ Event x) := by
    funext L
    simp only [not_exists, not_and]
  rw [Negation, Miss] at Complement
  linarith

/-- A bounded target rate `x` gives success probability at least `x/2` whenever
the expected number of successes is at least `x`. This is a lower bound, not an
independence-free union bound; independence enters through the exact batch law. -/
theorem IndependentSamplesSuccessLower (p : PMF α) (Event : α → Prop) (N : ℕ)
    (x : ℝ) (Small : x ≤ 1)
    (Rate : x ≤ N * EventProbability p Event) :
    x / 2 ≤ EventProbability (IndependentSamples p N) (fun L => ∃ y ∈ L, Event y) := by
  let q := EventProbability p Event
  have QNonnegative : 0 ≤ q := EventProbabilityNonnegative p Event
  have QAtMostOne : q ≤ 1 := EventProbabilityLeOne p Event
  have ProductBound (k : ℕ) : (1 - q) ^ k * (1 + k * q) ≤ 1 := by
    induction k with
    | zero => norm_num
    | succ k Previous =>
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        calc
          (1 - q) ^ k * (1 - q) * (1 + ((k : ℝ) + 1) * q) =
              (1 - q) ^ k * ((1 - q) * (1 + ((k : ℝ) + 1) * q)) := by ring
          _ ≤ (1 - q) ^ k * (1 + k * q) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (sub_nonneg.mpr QAtMostOne) k)
            nlinarith [sq_nonneg q, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg q)]
          _ ≤ 1 := Previous
  have NP : 0 ≤ (N : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) QNonnegative
  have Denominator : 0 < 1 + (N : ℝ) * q := by linarith
  have Fraction : (N : ℝ) * q / (1 + N * q) ≤ 1 - (1 - q) ^ N := by
    apply (div_le_iff₀ Denominator).mpr
    nlinarith [ProductBound N]
  have Half : x / 2 ≤ (N : ℝ) * q / (1 + N * q) := by
    apply (le_div_iff₀ Denominator).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr Small) NP]
  rw [IndependentSamplesSuccess]
  exact Half.trans Fraction

end
end ECTheoryLib.Operators.Sampling
