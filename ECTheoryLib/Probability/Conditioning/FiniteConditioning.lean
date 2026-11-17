import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Finite partitions and total expectation

Book Lemma 1.7.1. An arbitrary finite measurable partition is represented
by a measurable finite classifier, then Mathlib sum_meas_smul_cond_fiber
supplies the measure decomposition. Probability and integrable real expectation
are its direct consequences. Null cells contribute zero; their conditional
measure is zero, not a probability measure. No finite sample-space assumption
is made, and signed integrable variables are included.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Conditioning preserves integrability; a null event gives Mathlib's zero conditional measure. -/
theorem ConditionalEventIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (FiniteMean : Integrable X P) (C : Set Ω) :
    Integrable X P[|C] := by
  by_cases ZeroMass : P C = 0
  · rw [cond_eq_zero_of_meas_eq_zero ZeroMass]
    exact integrable_zero_measure
  · unfold ProbabilityTheory.cond
    exact FiniteMean.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr ZeroMass)

private theorem FinitePartitionClassifier {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] (C : ι → Set Ω)
    (Cells : ∀ i, MeasurableSet (C i))
    (DisjointCells : Pairwise (fun i j => Disjoint (C i) (C j)))
    (Cover : ∀ ω, ∃ i, ω ∈ C i) :
    ∃ X : Ω → ι, Measurable X ∧ ∀ i, X ⁻¹' {i} = C i := by
  classical
  let X : Ω → ι := fun ω => Classical.choose (Cover ω)
  have InCell (ω : Ω) : ω ∈ C (X ω) := Classical.choose_spec (Cover ω)
  have Fiber (i : ι) : X ⁻¹' {i} = C i := by
    ext ω
    change X ω = i ↔ ω ∈ C i
    constructor
    · intro Equal
      rw [← Equal]
      exact InCell ω
    · intro Member
      by_contra Different
      exact Set.disjoint_left.mp (DisjointCells Different) (InCell ω) Member
  refine ⟨X, ?_, Fiber⟩
  apply measurable_to_countable'
  intro i
  rw [Fiber]
  exact Cells i

/-- Arbitrary finite measurable partitions reduce to Mathlib's conditional-fiber decomposition. -/
theorem FinitePartitionConditionalMeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsFiniteMeasure P] (C : ι → Set Ω)
    (Cells : ∀ i, MeasurableSet (C i))
    (DisjointCells : Pairwise (fun i j => Disjoint (C i) (C j)))
    (Cover : ∀ ω, ∃ i, ω ∈ C i) :
    ∑ i, P (C i) • P[|C i] = P := by
  let Instance : MeasurableSpace ι := ⊤
  obtain ⟨X, Observable, Fiber⟩ := FinitePartitionClassifier C Cells DisjointCells Cover
  have Decomposition := sum_meas_smul_cond_fiber Observable P
  simp only [Fiber] at Decomposition
  exact Decomposition

/-- Book 1.7.1 total probability, including zero-mass cells with zero weighted contribution. -/
theorem FinitePartitionTotalProbability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsFiniteMeasure P] (C : ι → Set Ω)
    (Cells : ∀ i, MeasurableSet (C i))
    (DisjointCells : Pairwise (fun i j => Disjoint (C i) (C j)))
    (Cover : ∀ ω, ∃ i, ω ∈ C i) (A : Set Ω) :
    P A = ∑ i, (P[|C i]) A * P (C i) := by
  calc
    P A = (∑ i, P (C i) • P[|C i]) A :=
      congrArg (fun μ : Measure Ω => μ A) (FinitePartitionConditionalMeasure P C Cells DisjointCells Cover).symm
    _ = _ := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
        smul_eq_mul, mul_comm]

/-- Book 1.7.1 total expectation for an integrable real variable and an arbitrary finite partition. -/
theorem FinitePartitionTotalExpectation {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsFiniteMeasure P] (C : ι → Set Ω)
    (Cells : ∀ i, MeasurableSet (C i))
    (DisjointCells : Pairwise (fun i j => Disjoint (C i) (C j)))
    (Cover : ∀ ω, ∃ i, ω ∈ C i) (X : Ω → ℝ) (FiniteMean : Integrable X P) :
    (∫ ω, X ω ∂P) = ∑ i, P.real (C i) * (∫ ω, X ω ∂P[|C i]) := by
  have Decomposition := FinitePartitionConditionalMeasure P C Cells DisjointCells Cover
  have SumIntegrable : Integrable X (∑ i, P (C i) • P[|C i]) := by
    rw [Decomposition]
    exact FiniteMean
  have EachIntegrable : ∀ i, Integrable X (P (C i) • P[|C i]) := by
    intro i
    exact (integrable_finsetSum_measure.mp SumIntegrable) i (Finset.mem_univ i)
  calc
    (∫ ω, X ω ∂P) = ∫ ω, X ω ∂(∑ i, P (C i) • P[|C i]) := by rw [Decomposition]
    _ = ∑ i, ∫ ω, X ω ∂P (C i) • P[|C i] :=
      integral_finsetSum_measure (fun i _Member => EachIntegrable i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _Member
      rw [integral_smul_measure]
      rfl

end
end ECTheoryLib.Probability

