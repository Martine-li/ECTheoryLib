import ECTheoryLib.Probability.StochasticOrder.StochasticSum
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ConditionalProbability

/-!
# Conditional stochastic domination and one-step addition

This module reuses Mathlib regular conditional laws, disintegration and kernel
composition. Positive event conditioning is identified with the regular law
only at nonzero atoms; arbitrary null-history versions are not constrained.
-/

namespace ECTheoryLib.Probability
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
noncomputable section

/-- The CDF of a history-dependent increment is the integral of its conditional CDF. -/
theorem KernelAdditionLowerTail {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (κ : Kernel H ℝ) [IsSFiniteKernel κ]
    (g : H → ℝ) (MeasurableG : Measurable g) (a : ℝ) :
    ((μ ⊗ₘ κ).map (fun p => g p.1 + p.2)) (Iic a) =
      ∫⁻ h, κ h (Iic (a - g h)) ∂μ := by
  have MeasurableAdd : Measurable (fun p : H × ℝ => g p.1 + p.2) :=
    (MeasurableG.comp measurable_fst).add measurable_snd
  rw [Measure.map_apply MeasurableAdd measurableSet_Iic,
    Measure.compProd_apply (measurableSet_Iic.preimage MeasurableAdd)]
  apply lintegral_congr
  intro h
  congr 1
  ext z
  change g h + z ≤ a ↔ z ≤ a - g h
  constructor
  · intro Bound
    linarith
  · intro Bound
    linarith

/-- Integrate almost-everywhere conditional domination, retaining the same past cost. -/
theorem StochasticDominatedKernelAdd {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (κ η : Kernel H ℝ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (g : H → ℝ) (MeasurableG : Measurable g)
    (Dominated : ∀ᵐ h ∂μ, StochasticDominated (κ h) (η h)) :
    StochasticDominated ((μ ⊗ₘ κ).map (fun p => g p.1 + p.2))
      ((μ ⊗ₘ η).map (fun p => g p.1 + p.2)) := by
  intro a
  rw [KernelAdditionLowerTail μ η g MeasurableG a,
    KernelAdditionLowerTail μ κ g MeasurableG a]
  apply lintegral_mono_ae
  filter_upwards [Dominated] with h Ordered
  exact Ordered (a - g h)

/-- A constant increment kernel gives an independent convolution law. -/
theorem ConstantKernelAdditionLaw {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] (ν : Measure ℝ) [SFinite ν]
    (g : H → ℝ) (MeasurableG : Measurable g) :
    (μ ⊗ₘ Kernel.const H ν).map (fun p => g p.1 + p.2) = (μ.map g) ∗ ν := by
  rw [Measure.compProd_const, Measure.conv]
  have ProductLaw := Measure.map_prod_map μ ν MeasurableG measurable_id
  have MeasurableAdd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  rw [Measure.map_id] at ProductLaw
  rw [ProductLaw, Measure.map_map MeasurableAdd
    (MeasurableG.prodMap measurable_id)]
  rfl

/-- Upper comparison for an increment conditioned on any measurable history. -/
theorem StochasticDominatedConditionalAdd {Ω H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → ℝ)
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (g : H → ℝ) (MeasurableG : Measurable g)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Dominated : ∀ᵐ h ∂P.map Hst, StochasticDominated (condDistrib V Hst P h) ν) :
    StochasticDominated (P.map (fun ω => g (Hst ω) + V ω)) ((P.map (g ∘ Hst)) ∗ ν) := by
  have HistoryProbability : IsProbabilityMeasure (P.map Hst) :=
    Measure.isProbabilityMeasure_map MeasurableHistory.aemeasurable
  have Compared := StochasticDominatedKernelAdd (P.map Hst) (condDistrib V Hst P)
    (Kernel.const H ν) g MeasurableG Dominated
  have MeasurableAdd : Measurable (fun p : H × ℝ => g p.1 + p.2) :=
    (MeasurableG.comp measurable_fst).add measurable_snd
  rw [ConstantKernelAdditionLaw _ ν g MeasurableG,
    compProd_map_condDistrib MeasurableV.aemeasurable,
    Measure.map_map MeasurableAdd
      (MeasurableHistory.prodMk MeasurableV),
    Measure.map_map MeasurableG MeasurableHistory] at Compared
  exact Compared

/-- At a positive-probability history, the regular conditional law equals event conditioning. -/
theorem ConditionalDistributionAtAtom {Ω H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSingletonClass H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → ℝ)
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (h : H) (Positive : (P.map Hst) {h} ≠ 0) :
    condDistrib V Hst P h = (cond P (Hst ⁻¹' {h})).map V := by
  apply Measure.ext
  intro A MeasurableA
  rw [condDistrib_apply_of_ne_zero MeasurableV h Positive A,
    Measure.map_apply MeasurableHistory (measurableSet_singleton h),
    Measure.map_apply (MeasurableHistory.prodMk MeasurableV)
      ((measurableSet_singleton h).prod MeasurableA),
    Measure.map_apply MeasurableV MeasurableA,
    cond_apply' (MeasurableA.preimage MeasurableV)]
  rfl

/-- Lower comparison for an increment conditioned on any measurable history. -/
theorem StochasticDominatedConditionalAddLower {Ω H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hst : Ω → H) (V : Ω → ℝ)
    (MeasurableHistory : Measurable Hst) (MeasurableV : Measurable V)
    (g : H → ℝ) (MeasurableG : Measurable g)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Dominated : ∀ᵐ h ∂P.map Hst, StochasticDominated ν (condDistrib V Hst P h)) :
    StochasticDominated ((P.map (g ∘ Hst)) ∗ ν) (P.map (fun ω => g (Hst ω) + V ω)) := by
  have HistoryProbability : IsProbabilityMeasure (P.map Hst) :=
    Measure.isProbabilityMeasure_map MeasurableHistory.aemeasurable
  have Compared := StochasticDominatedKernelAdd (P.map Hst) (Kernel.const H ν)
    (condDistrib V Hst P) g MeasurableG Dominated
  have MeasurableAdd : Measurable (fun p : H × ℝ => g p.1 + p.2) :=
    (MeasurableG.comp measurable_fst).add measurable_snd
  rw [ConstantKernelAdditionLaw _ ν g MeasurableG,
    compProd_map_condDistrib MeasurableV.aemeasurable,
    Measure.map_map MeasurableAdd (MeasurableHistory.prodMk MeasurableV),
    Measure.map_map MeasurableG MeasurableHistory] at Compared
  exact Compared


end
end ECTheoryLib.Probability
