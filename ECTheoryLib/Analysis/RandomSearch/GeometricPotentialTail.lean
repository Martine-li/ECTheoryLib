import ECTheoryLib.Tools.Drift.IntegrableMultiplicativeTail
import ECTheoryLib.Algorithms.RandomSearch
import ECTheoryLib.Probability.Processes.CountableHistoryConditional
import ECTheoryLib.Probability.Distributions.GeometricWaiting
import ECTheoryLib.Probability.HittingTimes.StoppedNonnegative
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Independent geometric search with an unbounded numerical potential

Each transition draws a natural number from geometricMeasure (3/4), starting
from the pure state 1 and seeking zero. The potential is the sampled number
itself, including after selection of the first-hit stopped process. Its first
stopped coordinate has positive mass at arbitrarily large values. The original
search can leave zero, witnessed by a positive-mass two-step trajectory event.
The final bound counts transitions and uses stopped-current-level drift.
-/

namespace ECTheoryLib.Analysis.RandomSearch.GeometricPotential

open MeasureTheory ProbabilityTheory ECTheoryLib ECTheoryLib.Probability
open ECTheoryLib.Tools.Drift
open scoped unitInterval ENNReal BigOperators
noncomputable section

def Success : I := ⟨3 / 4, by norm_num⟩
def Samples : PMF ℕ := (geometricMeasure Success).toPMF
def Step : Transition ℕ := IndependentRandomSearchStep Samples
def Law : Measure (ℕ → ℕ) := PathMeasure Step (PMF.pure 1)
def X (t : ℕ) (path : ℕ → ℕ) : ℝ := path t
def Y : ℕ → (ℕ → ℕ) → ℝ := StopAtFirstHit (fun x : ℝ => x ≤ 0) X
def History : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℕ)) :=
  Filtration.piLE (X := fun _ : ℕ => ℕ)
abbrev Level (t : ℕ) : MeasurableSpace (ℕ → ℕ) :=
  MeasurableSpace.comap (Y t) (borel ℝ)

instance : IsProbabilityMeasure Law := by unfold Law; infer_instance

theorem SampleMeasure : Samples.toMeasure = geometricMeasure Success := by
  exact Measure.toPMF_toMeasure _

theorem SamplesIntegrable : Integrable (fun n : ℕ => (n : ℝ)) Samples.toMeasure := by
  rw [SampleMeasure]
  have Waiting := GeometricWaitingIntegrable Success (by norm_num [Success])
  convert Waiting.sub (integrable_const (1 : ℝ)) using 1
  funext n
  simp

theorem SamplesMean : (∫ n : ℕ, (n : ℝ) ∂Samples.toMeasure) = 1 / 3 := by
  have Waiting := GeometricWaitingExpectation Success (by norm_num [Success])
  have NatIntegrable : Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure Success) := by
    simpa only [SampleMeasure] using SamplesIntegrable
  have Form : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) = (fun n : ℕ => (n : ℝ) + 1) := by
    funext n
    simp
  rw [Form, integral_add NatIntegrable (integrable_const (1 : ℝ))] at Waiting
  norm_num [Success] at Waiting
  change (∫ n : ℕ, (n : ℝ) ∂geometricMeasure Success) + 1 = 4 / 3 at Waiting
  rw [SampleMeasure]
  linarith

theorem SampleSingleton (k : ℕ) : Samples.toMeasure.real {k} = (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ k := by
  have Nonzero : Success ≠ 0 := by
    intro Equal
    have H : (3 / 4 : ℝ) = 0 := congrArg (fun p : I => (p : ℝ)) Equal
    norm_num at H
  rw [SampleMeasure, geometricMeasure_real_singleton Nonzero]
  norm_num [Success]
  ring

/-- Constant independent sampling, as an identity of the existing kernels. -/
theorem HistoryKernelConstant (t : ℕ) :
    HistoryKernel Step t = Kernel.const (Finset.Iic t → ℕ) Samples.toMeasure := by
  apply Kernel.ext
  intro history
  rfl

theorem JointProductLaw (t : ℕ) :
    Law.map (fun path => (Preorder.frestrictLe t path, path (t + 1))) =
      (Law.map (Preorder.frestrictLe t)).prod Samples.toMeasure := by
  have Joint := PathMeasureJointLaw Step (PMF.pure 1) t
  rw [HistoryKernelConstant, Measure.compProd_const] at Joint
  exact Joint.symm

/-- This uses countable trajectory consistency, not the finite-state marginal API. -/
theorem NextMarginal (t : ℕ) : Law.map (fun path => path (t + 1)) = Samples.toMeasure := by
  have PrefixMeasurable := Preorder.measurable_frestrictLe (X := fun _ : ℕ => ℕ) t
  have PairMeasurable : Measurable (fun path : ℕ → ℕ => (Preorder.frestrictLe t path, path (t + 1))) :=
    PrefixMeasurable.prodMk (measurable_pi_apply (t + 1))
  have PrefixProbability : IsProbabilityMeasure (Law.map (Preorder.frestrictLe t)) :=
    Measure.isProbabilityMeasure_map PrefixMeasurable.aemeasurable
  have Mapped := congrArg (fun μ : Measure ((Finset.Iic t → ℕ) × ℕ) => μ.map Prod.snd) (JointProductLaw t)
  rw [Measure.map_map measurable_snd PairMeasurable, Measure.map_snd_prod,
    measure_univ, one_smul] at Mapped
  exact Mapped

theorem InitialFixed : ∀ᵐ path ∂Law, X 0 path = 1 := by
  filter_upwards [PathMeasureInitialPure Step (1 : ℕ)] with path Initial
  simp [X, Initial]

theorem RawAdapted : Adapted History X :=
  CountablePathPotentialAdapted (fun n : ℕ => (n : ℝ))

theorem RawMeasurable (t : ℕ) : Measurable (X t) := RawAdapted.measurable

theorem RawNonnegative (t : ℕ) (path : ℕ → ℕ) : 0 ≤ X t path := Nat.cast_nonneg _

theorem RawGap (t : ℕ) (path : ℕ → ℕ) : X t path = 0 ∨ 1 ≤ X t path := by
  by_cases Zero : path t = 0
  · left; simp [X, Zero]
  · right
    change (1 : ℝ) ≤ (path t : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr Zero)

theorem RawIntegrable (t : ℕ) : Integrable (X t) Law := by
  cases t with
  | zero =>
      apply (integrable_const (1 : ℝ)).congr
      filter_upwards [InitialFixed] with path Equal
      exact Equal.symm
  | succ t =>
    have MarginalIntegrable : Integrable (fun n : ℕ => (n : ℝ)) (Law.map (fun path => path (t + 1))) := by
      rw [NextMarginal]
      exact SamplesIntegrable
    exact MarginalIntegrable.comp_measurable (measurable_pi_apply (t + 1))

theorem StoppedAdapted : Adapted History Y :=
  StopAtFirstHitAdapted X History RawAdapted _ measurableSet_Iic

theorem StoppedNonnegative (t : ℕ) (path : ℕ → ℕ) : 0 ≤ Y t path :=
  StopAtNonpositiveNonnegative X RawNonnegative t path

theorem StoppedLeRaw (t : ℕ) (path : ℕ → ℕ) : Y t path ≤ X t path := by
  by_cases Hit : Y t path ≤ 0
  · exact Hit.trans (RawNonnegative t path)
  · exact (StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X t path Hit).1.le

theorem StoppedIntegrable (t : ℕ) : Integrable (Y t) Law := by
  apply (RawIntegrable t).mono_nonneg StoppedAdapted.measurable.aestronglyMeasurable
  · exact ae_of_all _ (StoppedNonnegative t)
  · exact ae_of_all _ (StoppedLeRaw t)

theorem LocalMeanDecrease (x : ℕ) :
    (∫ y : ℕ, (x : ℝ) - (y : ℝ) ∂(Step x).toMeasure) = (x : ℝ) - 1 / 3 := by
  change (∫ y : ℕ, (x : ℝ) - (y : ℝ) ∂Samples.toMeasure) = _
  rw [integral_sub (integrable_const _) SamplesIntegrable, SamplesMean]
  simp

theorem RawHistoryDecrease (t : ℕ) :
    (Law[fun path => X t path - X (t + 1) path | History t]) =ᵐ[Law]
      (fun path => X t path - 1 / 3) := by
  have Conditional := PathMeasureStateConditionalExpectationOfIntegrable Step (PMF.pure 1) t
    (fun x y : ℕ => (x : ℝ) - (y : ℝ)) ((RawIntegrable t).sub (RawIntegrable (t + 1)))
  simpa only [LocalMeanDecrease, Law, X, History] using Conditional

theorem StoppedHistoryDrift (t : ℕ) :
    (fun path => (2 / 3 : ℝ) * Y t path) ≤ᵐ[Law]
      Law[fun path => Y t path - Y (t + 1) path | History t] := by
  have Stopped := StoppedConditionalDecrease Law X History RawAdapted t
    ((RawIntegrable t).sub (RawIntegrable (t + 1)))
  filter_upwards [Stopped, RawHistoryDecrease t] with path Stop Mean
  change (Law[fun u => Y t u - Y (t + 1) u | History t]) path =
    (if 0 < Y t path then (Law[fun u => X t u - X (t+1) u | History t]) path else 0) at Stop
  rw [Stop]
  by_cases Active : 0 < Y t path
  · rw [if_pos Active, Mean]
    have Equal := (StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X t path (not_le_of_gt Active)).1
    change Y t path = X t path at Equal
    have PositiveRaw : 0 < X t path := by rwa [← Equal]
    have One : 1 ≤ X t path := (RawGap t path).resolve_left (ne_of_gt PositiveRaw)
    rw [Equal]
    linarith
  · rw [if_neg Active]
    have Zero : Y t path = 0 := le_antisymm (le_of_not_gt Active) (StoppedNonnegative t path)
    simp [Zero]

/-- The actual client uses sigma(Y_t), via a tower argument; no full-history
condition is added to the public core interface. -/
theorem StoppedLevelDrift (t : ℕ) :
    (fun path => (2 / 3 : ℝ) * Y t path) ≤ᵐ[Law]
      Law[fun path => Y t path - Y (t + 1) path | Level t] := by
  have LevelLeHistory : Level t ≤ History t := (StoppedAdapted t).comap_le
  have LevelLe : Level t ≤ (inferInstance : MeasurableSpace (ℕ → ℕ)) :=
    LevelLeHistory.trans (History.le t)
  have LevelMeasurable : Measurable[Level t] (Y t) := comap_measurable _
  have ScaledIntegrable : Integrable (fun path => (2 / 3 : ℝ) * Y t path) Law :=
    (StoppedIntegrable t).const_mul _
  have Self := condExp_of_stronglyMeasurable (μ := Law) LevelLe
    (measurable_const.mul LevelMeasurable).stronglyMeasurable ScaledIntegrable
  change Law[fun path => (2 / 3 : ℝ) * Y t path | Level t] =
    (fun path => (2 / 3 : ℝ) * Y t path) at Self
  have Monotone := condExp_mono (m := Level t) ScaledIntegrable integrable_condExp (StoppedHistoryDrift t)
  rw [Self] at Monotone
  have Tower := condExp_condExp_of_le (μ := Law) (f := fun path => Y t path - Y (t + 1) path)
    LevelLeHistory (History.le t)
  filter_upwards [Monotone, Tower] with path Lower Equal
  exact Lower.trans_eq Equal

theorem RawFirstSingleton (k : ℕ) :
    Law.real {path | X 1 path = (k : ℝ)} = (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ k := by
  have Marginal := congrArg (fun μ : Measure ℕ => μ.real {k}) (NextMarginal 0)
  rw [Measure.real, Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton k)] at Marginal
  change Law.real {path | path 1 = k} = Samples.toMeasure.real {k} at Marginal
  simpa only [X, Nat.cast_inj] using Marginal.trans (SampleSingleton k)

theorem StoppedFirstEqRaw : Y 1 =ᵐ[Law] X 1 := by
  filter_upwards [InitialFixed] with path Initial
  have InitialY : Y 0 path = 1 := by
    change StopAtFirstHit (fun x : ℝ => x ≤ 0) X 0 path = 1
    rw [StopAtFirstHitInitial, Initial]
  exact (StopAtFirstHitStepBefore (fun x : ℝ => x ≤ 0) X 0 path
    (by change ¬Y 0 path ≤ 0; rw [InitialY]; norm_num)).2

theorem StoppedFirstSingleton (k : ℕ) :
    Law.real {path | Y 1 path = (k : ℝ)} = (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ k := by
  calc
    _ = Law.real {path | X 1 path = (k : ℝ)} := measureReal_congr (by
      filter_upwards [StoppedFirstEqRaw] with path Equal
      exact congrArg (fun v : ℝ => v = (k : ℝ)) Equal)
    _ = _ := RawFirstSingleton k

theorem RawFirstUnbounded (B : ℝ) : 0 < Law.real {path | B < X 1 path} := by
  obtain ⟨k, Above⟩ := exists_nat_gt B
  have Positive : 0 < Law.real {path | X 1 path = (k : ℝ)} := by
    rw [RawFirstSingleton]
    positivity
  apply Positive.trans_le (measureReal_mono _)
  intro path Equal
  change X 1 path = (k : ℝ) at Equal
  change B < X 1 path
  rwa [Equal]

theorem StoppedFirstUnbounded (B : ℝ) : 0 < Law.real {path | B < Y 1 path} := by
  obtain ⟨k, Above⟩ := exists_nat_gt B
  have Positive : 0 < Law.real {path | Y 1 path = (k : ℝ)} := by
    rw [StoppedFirstSingleton]
    positivity
  apply Positive.trans_le (measureReal_mono _)
  intro path Equal
  change Y 1 path = (k : ℝ) at Equal
  change B < Y 1 path
  rwa [Equal]

theorem NoStoppedAlmostSureBound (B : ℝ) : ¬∀ᵐ path ∂Law, Y 1 path ≤ B := by
  intro Bound
  have Null : Law {path | B < Y 1 path} = 0 := by
    simpa only [not_le] using (ae_iff.mp Bound)
  have RealNull : Law.real {path | B < Y 1 path} = 0 := by simp [Measure.real, Null]
  exact (ne_of_gt (StoppedFirstUnbounded B)) RealNull

theorem NoStoppedFiniteRange : ¬∃ S : Finset ℝ, ∀ᵐ path ∂Law, Y 1 path ∈ S := by
  classical
  rintro ⟨S, Values⟩
  apply NoStoppedAlmostSureBound (∑ z ∈ S, |z|)
  filter_upwards [Values] with path InS
  exact (le_abs_self _).trans (Finset.single_le_sum (fun z _ => abs_nonneg z) InS)

/-- The actual transition can leave zero, with no modification at the target. -/
theorem ZeroStepLeaves : (Step 0).toMeasure.real {1} = 3 / 16 := by
  change Samples.toMeasure.real {1} = _
  norm_num [SampleSingleton]

/-- Positive mass for leaving zero under the actual pure-one trajectory law. -/
theorem ZeroThenOneProbability : Law.real {path | path 1 = 0 ∧ path 2 = 1} = 9 / 64 := by
  let A : Set (Finset.Iic 1 → ℕ) := {history | HistoryLast 1 history = 0}
  have AMeasurable : MeasurableSet A := (Set.to_countable _).measurableSet
  have PairMeasurable : Measurable (fun path : ℕ → ℕ => (Preorder.frestrictLe 1 path, path 2)) :=
    (Preorder.measurable_frestrictLe 1).prodMk (measurable_pi_apply 2)
  have Joint := congrArg (fun μ : Measure ((Finset.Iic 1 → ℕ) × ℕ) => μ.real (A ×ˢ ({1} : Set ℕ)))
    (JointProductLaw 1)
  have Left : (Law.map (fun path : ℕ → ℕ => (Preorder.frestrictLe 1 path, path 2))).real
      (A ×ˢ ({1} : Set ℕ)) = Law.real {path | path 1 = 0 ∧ path 2 = 1} := by
    rw [Measure.real, Measure.map_apply PairMeasurable (AMeasurable.prod (measurableSet_singleton 1))]
    rfl
  have PrefixZero : (Law.map (Preorder.frestrictLe 1)).real A = (3 / 4 : ℝ) := by
    rw [Measure.real, Measure.map_apply (Preorder.measurable_frestrictLe 1) AMeasurable]
    change Law.real {path | path 1 = 0} = _
    simpa only [X, Nat.cast_inj, pow_zero, mul_one] using RawFirstSingleton 0
  rw [Left, measureReal_prod_prod, PrefixZero, SampleSingleton] at Joint
  norm_num at Joint
  exact Joint

theorem RawNotAbsorbing : ¬ZeroIsAbsorbing Law X := by
  intro Absorbing
  have Avoid : ∀ᵐ path ∂Law, ¬(path 1 = 0 ∧ path 2 = 1) := by
    filter_upwards [Absorbing 1] with path Absorb
    rintro ⟨AtZero, AtOne⟩
    have Impossible := Absorb (by simp [X, AtZero])
    norm_num [X, AtOne] at Impossible
  have Null : Law {path | path 1 = 0 ∧ path 2 = 1} = 0 := by
    simpa only [not_not] using ae_iff.mp Avoid
  have RealNull : Law.real {path | path 1 = 0 ∧ path 2 = 1} = 0 := by simp [Measure.real, Null]
  rw [ZeroThenOneProbability] at RealNull
  norm_num at RealNull

theorem ActualHittingTime (path : ℕ → ℕ) : ZeroHittingTime X path = FirstHittingTime (fun n : ℕ => n = 0) path := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  change FirstHittingTime (fun s : ℝ => s = 0) (fun j => X j path) ≤ (t : WithTop ℕ) ↔
    FirstHittingTime (fun n : ℕ => n = 0) path ≤ (t : WithTop ℕ)
  rw [FirstHittingTimeLeIff, FirstHittingTimeLeIff]
  simp only [X, Nat.cast_eq_zero]

/-- Apply integrable stopped-level drift to the actual search with its
unbounded natural-state potential. Time counts transitions after initialization. -/
theorem GeometricSearchTail (r : ℝ) (NonnegativeR : 0 ≤ r) :
    Law {path | (⌈3 * r / 2⌉₊ : WithTop ℕ) < FirstHittingTime (fun n : ℕ => n = 0) path} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have Bound := MultiplicativeDriftUpperTailOfIntegrableStoppedLevel Law X 1 ((2 : ℝ) / 3)
    RawMeasurable (by norm_num) RawGap StoppedIntegrable StoppedLevelDrift
    1 (by norm_num) InitialFixed (by norm_num) r NonnegativeR
  have Index : (r + Real.log ((1 : ℝ) / 1)) / ((2 : ℝ) / 3) = 3 * r / 2 := by
    norm_num
    ring
  simpa only [Index, ActualHittingTime] using Bound

end
end ECTheoryLib.Analysis.RandomSearch.GeometricPotential

