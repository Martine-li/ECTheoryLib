import Mathlib.Probability.CDF
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Order.IsLUB

/-!
# First-order stochastic domination

Doerr, Definition 1.8.1 and Lemma 1.8.5 (pp. 25-27), in
*Theory of Evolutionary Computation* (2020).

The smaller law has the larger lower-tail probabilities. We compare existing
Mathlib measures, and use map/HasLaw for variables on different sample spaces.
The definition is meaningful on any ordered range, including extended natural
times; no conversion of an infinite runtime to a real number is involved.

Probabilistic interpretations use probability measures. Elementary reflexivity,
transitivity and ordered-map facts hold even without normalization. This file
does not assert the existence of an ordered coupling from domination.
-/

namespace ECTheoryLib.Probability

open MeasureTheory ProbabilityTheory Set Filter

noncomputable section

/-- The law `ν` stochastically dominates `μ`: its lower tails are smaller.
For real probability laws this is exactly Doerr's Definition 1.8.1. -/
def StochasticDominated {α : Type*} [Preorder α] [MeasurableSpace α]
    (μ ν : Measure α) : Prop := ∀ a, ν (Iic a) ≤ μ (Iic a)

theorem StochasticDominatedRefl {α : Type*} [Preorder α] [MeasurableSpace α]
    (μ : Measure α) : StochasticDominated μ μ := by
  intro a
  exact le_rfl

theorem StochasticDominatedTrans {α : Type*} [Preorder α] [MeasurableSpace α]
    {μ ν ξ : Measure α} (First : StochasticDominated μ ν)
    (Second : StochasticDominated ν ξ) : StochasticDominated μ ξ := by
  intro a
  exact le_trans (Second a) (First a)

/-- Antisymmetry is equality of laws, not pointwise equality of random variables. -/
theorem StochasticDominatedAntisymm {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] (μ ν : Measure α) [IsFiniteMeasure μ]
    (Forward : StochasticDominated μ ν) (Backward : StochasticDominated ν μ) : μ = ν := by
  apply Measure.ext_of_Iic μ ν
  intro a
  exact le_antisymm (Backward a) (Forward a)

/-- Lemma 1.8.5(b), using Mathlib's notion of identical distribution. -/
theorem StochasticDominatedOfIdentDistrib {α Ω Ω' : Type*} [Preorder α]
    [MeasurableSpace α] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → α) (Y : Ω' → α)
    (SameLaw : IdentDistrib X Y μ ν) : StochasticDominated (μ.map X) (ν.map Y) := by
  rw [SameLaw.map_eq]
  exact StochasticDominatedRefl _

section RandomVariables

variable {α Ω Ω' : Type*} [Preorder α] [TopologicalSpace α]
    [ClosedIicTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The distribution-level relation is the book's event-probability definition,
including variables on distinct spaces. -/
theorem StochasticDominatedMapIff (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → α) (Y : Ω' → α) (MeasurableX : AEMeasurable X μ)
    (MeasurableY : AEMeasurable Y ν) :
    StochasticDominated (μ.map X) (ν.map Y) ↔
      ∀ a, ν {ω | Y ω ≤ a} ≤ μ {ω | X ω ≤ a} := by
  unfold StochasticDominated
  simp only [Measure.map_apply_of_aemeasurable MeasurableX measurableSet_Iic,
    Measure.map_apply_of_aemeasurable MeasurableY measurableSet_Iic]
  rfl

/-- Lemma 1.8.5(a), strengthened from pointwise to almost-everywhere order. -/
theorem StochasticDominatedOfAELe (μ : Measure Ω) (X Y : Ω → α)
    (MeasurableX : AEMeasurable X μ) (MeasurableY : AEMeasurable Y μ)
    (Ordered : X ≤ᵐ[μ] Y) : StochasticDominated (μ.map X) (μ.map Y) := by
  apply (StochasticDominatedMapIff μ μ X Y MeasurableX MeasurableY).mpr
  intro a
  apply measure_mono_ae
  filter_upwards [Ordered] with ω PointwiseOrder
  intro BelowThreshold
  exact le_trans PointwiseOrder BelowThreshold

/-- An explicitly given ordered coupling proves domination of its marginal laws.
The coupled variables may live on any common sample space. -/
theorem StochasticDominatedOfCoupling (γ : Measure Ω) (μ ν : Measure α)
    (X Y : Ω → α) (FirstLaw : HasLaw X μ γ) (SecondLaw : HasLaw Y ν γ)
    (Ordered : X ≤ᵐ[γ] Y) : StochasticDominated μ ν := by
  rw [← FirstLaw.map_eq, ← SecondLaw.map_eq]
  exact StochasticDominatedOfAELe γ X Y FirstLaw.aemeasurable SecondLaw.aemeasurable Ordered

end RandomVariables

section Tails

variable {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [ClosedIicTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- Lower closed tails reverse order exactly when strict upper tails preserve it. -/
theorem StochasticDominatedIffStrictTail (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticDominated μ ν ↔ ∀ a, μ (Ioi a) ≤ ν (Ioi a) := by
  have Complement (ρ : Measure α) [IsProbabilityMeasure ρ] (a : α) :
      ρ (Ioi a) = 1 - ρ (Iic a) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
  constructor
  · intro Dominated a
    rw [Complement μ a, Complement ν a]
    exact tsub_le_tsub_left (Dominated a) 1
  · intro Tail a
    have Bound := Tail a
    rw [Complement μ a, Complement ν a] at Bound
    exact (ENNReal.sub_le_sub_iff_left prob_le_one ENNReal.one_ne_top).mp Bound

end Tails

/-- The equivalent non-strict upper-tail formulation stated after Definition
1.8.1. Continuity of measures handles atoms at the threshold; no atomlessness
or density assumption on either distribution is made. -/
theorem StochasticDominatedIffClosedTail (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticDominated μ ν ↔ ∀ a, μ (Ici a) ≤ ν (Ici a) := by
  constructor
  · intro Dominated a
    obtain ⟨u, Increasing, Below, Limit⟩ := exists_seq_strictMono_tendsto a
    have IncreasingSets : Monotone (fun n : ℕ => Iic (u n)) := by
      intro i j BelowIndex
      exact Iic_subset_Iic.mpr (Increasing.monotone BelowIndex)
    have OpenLowerBound : ν (Iio a) ≤ μ (Iio a) := by
      rw [← iUnion_Iic_eq_Iio_of_lt_of_tendsto Below Limit,
        IncreasingSets.measure_iUnion, IncreasingSets.measure_iUnion]
      exact iSup_mono (fun n => Dominated (u n))
    have Complement (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
        ρ (Ici a) = 1 - ρ (Iio a) := by
      rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
    rw [Complement μ, Complement ν]
    exact tsub_le_tsub_left OpenLowerBound 1
  · intro ClosedTail
    apply (StochasticDominatedIffStrictTail μ ν).mpr
    intro a
    obtain ⟨u, Decreasing, Above, Limit⟩ :=
      exists_seq_strictMono_tendsto (α := ℝᵒᵈ) a
    let v : ℕ → ℝ := fun n => u n
    have DecreasingReal : Antitone v := Decreasing.monotone
    have IncreasingSets : Monotone (fun n : ℕ => Ici (v n)) := by
      intro i j BelowIndex
      exact Ici_subset_Ici.mpr (DecreasingReal BelowIndex)
    have AboveReal : ∀ n, a < v n := Above
    have LimitReal : Tendsto v atTop (nhds a) := Limit
    rw [← iUnion_Ici_eq_Ioi_of_lt_of_tendsto AboveReal LimitReal,
      IncreasingSets.measure_iUnion, IncreasingSets.measure_iUnion]
    exact iSup_mono (fun n => ClosedTail (v n))

/-- Mathlib's existing CDF represents the same relation; no new CDF is defined. -/
theorem StochasticDominatedIffCDF (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    StochasticDominated μ ν ↔ ∀ a, cdf ν a ≤ cdf μ a := by
  constructor
  · intro Dominated a
    rw [cdf_eq_real, cdf_eq_real]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (Dominated a)
  · intro CDFOrder a
    rw [← ofReal_cdf ν a, ← ofReal_cdf μ a]
    exact ENNReal.ofReal_le_ofReal (CDFOrder a)

end
end ECTheoryLib.Probability
