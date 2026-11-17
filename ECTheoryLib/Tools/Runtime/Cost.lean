import ECTheoryLib.Probability.HittingTimes.Expectation

/-!
# Fixed evaluation costs up to a hitting time

`EvaluationCost` charges initialization and a fixed positive number of evaluations
per completed transition. The goal is inspected at transition boundaries. The
identity does not model early stopping inside a generation or random step costs.
Nontermination has infinite cost when the per-transition cost is positive.
-/
namespace ECTheoryLib.Tools.Runtime
open MeasureTheory ECTheoryLib.Probability
noncomputable section

/-- Initialization cost plus the cost of all completed transitions until first success.
`PerStep > 0` is required when interpreting nontermination as infinite evaluations. -/
def EvaluationCost {State : Type*} (Goal : State → Prop) (InitialCost PerStep : Nat)
    (Path : Nat → State) : ENNReal :=
  (InitialCost : ENNReal) + (PerStep : ENNReal) * FirstHittingTimeValue Goal Path

/-- Expected evaluation cost under the same path law used for iteration runtime. -/
def ExpectedEvaluationCost {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (Step : Transition State) (Goal : State → Prop)
    (Initial : PMF State) (InitialCost PerStep : Nat) : ENNReal :=
  ∫⁻ Path, EvaluationCost Goal InitialCost PerStep Path ∂PathMeasure Step Initial

/-- Fixed per-step costs commute with expectation, including infinite runtime.
This is an identity for boundary-observed stopping; initialization is charged once. -/
theorem ExpectedEvaluationCostEq {State : Type*} [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] (Step : Transition State) (Goal : State → Prop)
    (Initial : PMF State) (InitialCost PerStep : Nat) :
    ExpectedEvaluationCost Step Goal Initial InitialCost PerStep =
      (InitialCost : ENNReal) + (PerStep : ENNReal) * ExpectedHittingTime Step Goal Initial := by
  unfold ExpectedEvaluationCost EvaluationCost ExpectedHittingTime
  rw [lintegral_add_left measurable_const,
    lintegral_const_mul _ (FirstHittingTimeValueMeasurable Goal), lintegral_const]
  simp only [measure_univ, mul_one]

/-- A positive cost per step preserves the infinite-cost interpretation of no hit. -/
theorem EvaluationCostOfNoHit {State : Type*} (Goal : State → Prop)
    (InitialCost PerStep : Nat) (PositiveCost : 0 < PerStep) (Path : Nat → State)
    (NoHit : FirstHittingTime Goal Path = ⊤) :
    EvaluationCost Goal InitialCost PerStep Path = ⊤ := by
  have CostNonzero : (PerStep : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt PositiveCost
  unfold EvaluationCost FirstHittingTimeValue
  rw [NoHit]
  change (InitialCost : ENNReal) + (PerStep : ENNReal) * (⊤ : ENNReal) = ⊤
  rw [ENNReal.mul_top CostNonzero, add_top]

end
end ECTheoryLib.Tools.Runtime

namespace ECTheoryLib.Tools.Runtime
open ECTheoryLib.Probability
noncomputable section

/-- One initial evaluation and one evaluation per iteration retain the exact
real-threshold meaning, including negative thresholds and nontermination. -/
theorem UnitEvaluationCostLeOfRealIff {State : Type*} (Goal : State → Prop)
    (Path : ℕ → State) (a : ℝ) :
    EvaluationCost Goal 1 1 Path≤ENNReal.ofReal a ↔
      ∃ k : ℕ, FirstHittingTime Goal Path=(k : WithTop ℕ) ∧ (k : ℝ)+1≤a := by
  cases Time : FirstHittingTime Goal Path with
  | top =>
    rw [EvaluationCostOfNoHit Goal 1 1 (by decide) Path Time]
    simp
  | coe k =>
    have Value : FirstHittingTimeValue Goal Path=(k : ENNReal) := by
      unfold FirstHittingTimeValue
      rw [Time]
      exact ENat.toENNReal_coe k
    have Cost : EvaluationCost Goal 1 1 Path=ENNReal.ofReal ((k : ℝ)+1) := by
      simp [EvaluationCost,Value,ENNReal.ofReal_add,add_comm]
    rw [Cost,ENNReal.ofReal_le_ofReal_iff']
    have Positive : (0 : ℝ)<(k : ℝ)+1 := by positivity
    simp [not_le_of_gt Positive]

end
end ECTheoryLib.Tools.Runtime
