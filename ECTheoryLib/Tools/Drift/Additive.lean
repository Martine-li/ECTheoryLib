import ECTheoryLib.Probability.Processes.ScalarProcess
import ECTheoryLib.Probability.HittingTimes.ScalarHittingTime
import ECTheoryLib.Probability.Processes.FiniteStateBounds
import ECTheoryLib.Tools.Drift.FiniteState
import ECTheoryLib.Tools.Drift.Telescoping
import ECTheoryLib.Tools.Drift.LowerBound

/-!
# Additive drift bounds with explicit zero absorption

Source: Johannes Lengler, *Drift Analysis*, Theorem 2.3.1(a),(b), pp. 95-97,
in Doerr and Neumann (eds.), *Theory of Evolutionary Computation* (2020),
https://doi.org/10.1007/978-3-030-29414-4_2. The source
proof's convention of staying at zero after a hit is an explicit hypothesis here.
The scalar process need not be Markov and initialization may be random. Its values
belong pointwise to a common finite nonnegative set.

A positive lower bound on event-conditioned expected decrease gives an upper
runtime bound; a positive upper bound gives the converse lower bound. Drift is
required only on nonzero potential events of positive probability. Runtime is
an extended expectation, and finite expectation is never a premise.
Both directly callable theorems and the legacy proposition specifications remain
available, independent of any concrete algorithm or problem.
-/

namespace ECTheoryLib.Tools.Drift

open MeasureTheory ECTheoryLib.Probability

/-- Additive upper-bound specification with explicit zero absorption:
expected first-zero hitting time is at most the initial mean divided by Delta. -/

def AdditiveDriftUpperBoundStatement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω),
    
    IsProbabilityMeasure μ →
    
    
    
    
    ∀ (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ),
      
      
      (∀ t, Measurable (X t)) →
      
      0 ∈ S →
      (∀ s ∈ S, 0 ≤ s) →
      -- The finite-range convention is pointwise in both time and sample.
      (∀ t ω, X t ω ∈ S) →
      
      ZeroIsAbsorbing μ X →
      
      0 < Delta →
      
      (∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
        0 < μ (StateEvent X t s) →
        Delta ≤ StateDrift μ X t s) →
      
      
      
      ExpectedZeroHittingTime μ X ≤
        ENNReal.ofReal (ExpectedValue μ (X 0) / Delta)

/-- Lengler's additive drift upper bound, Theorem 2.3.1(a), with explicit
almost-sure zero absorption. Expected first-zero hitting time is at most the
initial mean divided by the positive drift floor. Initialization may be random;
no Markov property, pathwise decrease, or finite expectation is assumed.
The pointwise finite nonnegative range follows the source's model.
`0 ∈ S` preserves its state-space convention, although the proof does not use it. -/
theorem AdditiveDriftUpperBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (_ZeroInS : 0 ∈ S)
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PositiveDelta : 0 < Delta)
    (StateDriftLowerBound : ∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → Delta ≤ StateDrift μ X t s) :
    ExpectedZeroHittingTime μ X ≤
      ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) := by
  -- Finite measurable range gives integrability; nonnegativity bounds the terminal mean below.
  have ExpectationsNonnegative : ∀ t, 0 ≤ ExpectedValue μ (X t) := by
    intro t
    exact FiniteStateExpectedValueNonneg μ (X t) S StatesNonnegative (ValuesInS t)
  -- Combine conditional progress over the finite partition of nonzero states.
  have OneStepDecrease : ∀ t,
      Delta * (μ {ω | X t ω ≠ 0}).toReal ≤
        ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) := by
    intro t
    exact StateDriftLowerBoundToExpectedDecrease μ X S Delta
      CoordinatesMeasurable ValuesInS ZeroAbsorbing StateDriftLowerBound t
  -- Bound every finite tail sum before taking the supremum of nonnegative partial sums.
  have TailSumBound :
      (∑' t : Nat, μ {ω | X t ω ≠ 0}) ≤
        ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) := by
    apply ExpectedDecreaseTailSumUpperBound
      (fun t => ExpectedValue μ (X t)) (fun t => μ {ω | X t ω ≠ 0})
      Delta PositiveDelta ExpectationsNonnegative
    · intro t
      exact measure_ne_top μ {ω | X t ω ≠ 0}
    · exact OneStepDecrease
  -- Absorption identifies runtime tails with nonzero events; the tail formula allows infinity.
  rw [ExpectedZeroHittingTimeEqNonzeroSum μ X CoordinatesMeasurable ZeroAbsorbing]
  exact TailSumBound

/-- Proof of the legacy upper-bound specification, for clients receiving
a DriftTheorem parameter. The library supplies this proof directly. -/
theorem AdditiveDriftUpperBoundStatementProof (Ω : Type*) [MeasurableSpace Ω] :
    AdditiveDriftUpperBoundStatement Ω := by
  intro μ ProbabilityMeasure X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS ZeroAbsorbing PositiveDelta StateDriftLowerBound
  let : IsProbabilityMeasure μ := ProbabilityMeasure
  exact AdditiveDriftUpperBound μ X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS ZeroAbsorbing PositiveDelta StateDriftLowerBound

/-- Additive lower-bound specification in the same process model.
An upper bound on drift gives a lower runtime bound without assuming finiteness. -/
def AdditiveDriftLowerBoundStatement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ),
      (∀ t, Measurable (X t)) →
      0 ∈ S →
      (∀ s ∈ S, 0 ≤ s) →
      (∀ t ω, X t ω ∈ S) →
      ZeroIsAbsorbing μ X →
      0 < Delta →
      (∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
        0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ Delta) →
      ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) ≤
        ExpectedZeroHittingTime μ X

/-- Lengler's additive drift lower bound, Theorem 2.3.1(b), with explicit
zero absorption. Infinite expected time satisfies the bound automatically.
In the finite-expectation branch, tails tend to zero and the common finite range
forces terminal means to vanish. This case split adds no finiteness premise. -/
theorem AdditiveDriftLowerBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → ℝ) (S : Finset ℝ) (Delta : ℝ)
    (CoordinatesMeasurable : ∀ t, Measurable (X t))
    (_ZeroInS : 0 ∈ S)
    (StatesNonnegative : ∀ s ∈ S, 0 ≤ s)
    (ValuesInS : ∀ t ω, X t ω ∈ S)
    (ZeroAbsorbing : ZeroIsAbsorbing μ X)
    (PositiveDelta : 0 < Delta)
    (StateDriftUpperBound : ∀ (t : Nat) (s : ℝ), s ∈ S → s ≠ 0 →
      0 < μ (StateEvent X t s) → StateDrift μ X t s ≤ Delta) :
    ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) ≤
      ExpectedZeroHittingTime μ X := by
  have OneStepDecrease : ∀ t,
      ExpectedValue μ (X t) - ExpectedValue μ (X (t + 1)) ≤
        Delta * (μ {ω | X t ω ≠ 0}).toReal := by
    intro t
    exact StateDriftUpperBoundToExpectedDecrease μ X S Delta
      CoordinatesMeasurable ValuesInS ZeroAbsorbing StateDriftUpperBound t
  -- Derive vanishing terminal means only in the finite-tail-sum branch.
  have TerminalExpectationTendstoZero :
      (∑' t : Nat, μ {ω | X t ω ≠ 0}) ≠ ⊤ →
        Filter.Tendsto (fun t => ExpectedValue μ (X t)) Filter.atTop (nhds 0) := by
    intro TailSumFinite
    have TailProbabilityTendstoZero :
        Filter.Tendsto (fun t => μ {ω | X t ω ≠ 0}) Filter.atTop (nhds 0) := by
      exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top TailSumFinite
    have RealTailProbabilityTendstoZero :
        Filter.Tendsto (fun t => (μ {ω | X t ω ≠ 0}).toReal)
          Filter.atTop (nhds 0) := by
      have ConvertedLimit :=
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp TailProbabilityTendstoZero
      rw [ENNReal.toReal_zero] at ConvertedLimit
      exact ConvertedLimit
    exact FiniteStateExpectedValueTendstoZero μ X S CoordinatesMeasurable
      StatesNonnegative ValuesInS RealTailProbabilityTendstoZero
  have TailSumBound :
      ENNReal.ofReal (ExpectedValue μ (X 0) / Delta) ≤
        ∑' t : Nat, μ {ω | X t ω ≠ 0} := by
    apply ExpectedDecreaseTailSumLowerBound
      (fun t => ExpectedValue μ (X t)) (fun t => μ {ω | X t ω ≠ 0})
      Delta PositiveDelta
    · intro t
      exact measure_ne_top μ {ω | X t ω ≠ 0}
    · exact OneStepDecrease
    · exact TerminalExpectationTendstoZero
  rw [ExpectedZeroHittingTimeEqNonzeroSum μ X CoordinatesMeasurable ZeroAbsorbing]
  exact TailSumBound

/-- Proof of the legacy additive lower-bound specification. -/
theorem AdditiveDriftLowerBoundStatementProof (Ω : Type*) [MeasurableSpace Ω] :
    AdditiveDriftLowerBoundStatement Ω := by
  intro μ ProbabilityMeasure X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS ZeroAbsorbing PositiveDelta StateDriftUpperBound
  let : IsProbabilityMeasure μ := ProbabilityMeasure
  exact AdditiveDriftLowerBound μ X S Delta CoordinatesMeasurable ZeroInS
    StatesNonnegative ValuesInS ZeroAbsorbing PositiveDelta StateDriftUpperBound

end ECTheoryLib.Tools.Drift
