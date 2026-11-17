import ECTheoryLib.Tools.Drift.ExponentialBarrier
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Interval-crossing bounds without a finite potential range

A bounded barrier supplies integrability. Complete-history increment
moments control its growth. The hitting theorem retains target absorption.
-/

namespace ECTheoryLib.Tools.Drift
open MeasureTheory ECTheoryLib.Probability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

theorem ExponentialBarrierMeasurable (a b Lambda : ℝ) :
    Measurable (ExponentialBarrierPotential a b Lambda) := by
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Ici measurable_const
      (Real.measurable_exp.comp ((measurable_id.sub_const a).const_mul (-Lambda))))

theorem ExponentialBarrierIntegrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (a b Lambda : ℝ) (NonnegativeLambda : 0≤Lambda) (Observable : Measurable X) :
    Integrable (fun ω => ExponentialBarrierPotential a b Lambda (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((ExponentialBarrierMeasurable a b Lambda).comp Observable).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖ExponentialBarrierPotential a b Lambda (X ω)‖≤1
    rw [Real.norm_eq_abs, abs_of_nonneg (ExponentialBarrierNonnegative a b Lambda (X ω))]
    exact ExponentialBarrierLeOne a b Lambda (X ω) NonnegativeLambda)

/-- Full-history barrier growth on a general real-valued process. The
negative exponential increment is explicitly integrable; a finite potential
range is unnecessary. Interior and entrance moment conditions stay separate. -/
theorem ExponentialBarrierExpectedStepOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (a b Lambda D : ℝ)
    (Ordered : a<b) (NonnegativeLambda : 0≤Lambda) (NonnegativeD : 0≤D) (t : ℕ)
    (MomentIntegrable : Integrable (fun ω => Real.exp (-Lambda*(X (t+1) ω-X t ω))) μ)
    (Interior : ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun u => Real.exp (-Lambda*(X (t+1) u-X t u)) | F t]) ω ≤ 1)
    (Entrance : ∀ᵐ ω ∂μ, b≤X t ω →
      (μ[fun u => Real.exp (-Lambda*(X (t+1) u-X t u)) | F t]) ω ≤ D) :
    (∫ ω, ExponentialBarrierPotential a b Lambda (X (t+1) ω) ∂μ) ≤
      (∫ ω, ExponentialBarrierPotential a b Lambda (X t ω) ∂μ) + D*Real.exp (-Lambda*(b-a)) := by
  let W := ExponentialBarrierPotential a b Lambda
  let R := fun ω => Real.exp (-Lambda*(X (t+1) ω-X t ω))
  let A := {ω | X t ω≤a}
  let I := fun ω => if X t ω≤a then (1 : ℝ) else 0
  let G := fun ω => if X t ω≤a then 0 else Real.exp (-Lambda*(X t ω-a))
  have EventF : MeasurableSet[F t] A := measurableSet_le (AdaptedX t) measurable_const
  have MeasurableG : Measurable[F t] G :=
    Measurable.ite EventF measurable_const
      (Real.measurable_exp.comp (((AdaptedX t).sub_const a).const_mul (-Lambda)))
  have BoundG (ω : Ω) : 0≤G ω ∧ G ω≤1 := by
    dsimp [G]
    split
    · norm_num
    · rename_i Above
      exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr NonnegativeLambda) (by linarith))⟩
  have GNorm : ∀ᵐ ω ∂μ, ‖G ω‖≤(1 : ℝ) := ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (BoundG ω).1]
    exact (BoundG ω).2)
  have IntegrableProduct : Integrable (G*R) μ :=
    MomentIntegrable.bdd_mul (MeasurableG.mono (F.le t) le_rfl).aestronglyMeasurable GNorm
  have IntegrableI : Integrable I μ := (integrable_const (1 : ℝ)).indicator (F.le t _ EventF)
  have NextIntegrable := ExponentialBarrierIntegrable μ (X (t+1)) a b Lambda NonnegativeLambda AdaptedX.measurable
  have CurrentIntegrable := ExponentialBarrierIntegrable μ (X t) a b Lambda NonnegativeLambda AdaptedX.measurable
  have Domination : (fun ω => W (X (t+1) ω)) ≤ᵐ[μ] I+G*R := ae_of_all _ (fun ω => by
    by_cases AtTarget : X t ω≤a
    · change W (X (t+1) ω)≤I ω+G ω*R ω
      simp only [I, G, if_pos AtTarget, zero_mul, add_zero]
      exact ExponentialBarrierLeOne a b Lambda (X (t+1) ω) NonnegativeLambda
    · change W (X (t+1) ω)≤I ω+G ω*R ω
      simp only [I, G, if_neg AtTarget, zero_add]
      exact ExponentialBarrierFactor a b Lambda (X t ω) (X (t+1) ω) NonnegativeLambda)
  have ConditionalLe := condExp_mono (m := F t) NextIntegrable (IntegrableI.add IntegrableProduct) Domination
  have ConditionalAdd := condExp_add IntegrableI IntegrableProduct (F t)
  have ConditionalI : μ[I | F t]=I := condExp_of_stronglyMeasurable (F.le t)
    ((measurable_const.indicator EventF).stronglyMeasurable) IntegrableI
  have PullOut := condExp_mul_of_stronglyMeasurable_left MeasurableG.stronglyMeasurable
    IntegrableProduct MomentIntegrable
  have Pointwise : (μ[fun ω => W (X (t+1) ω) | F t]) ≤ᵐ[μ]
      (fun ω => W (X t ω)+D*Real.exp (-Lambda*(b-a))) := by
    filter_upwards [ConditionalLe,ConditionalAdd,PullOut,Interior,Entrance] with ω Bound Add Pull Inside Above
    rw [Add, ConditionalI] at Bound
    change (μ[fun ω => W (X (t+1) ω) | F t]) ω ≤ I ω+(μ[G*R | F t]) ω at Bound
    rw [Pull] at Bound
    change (μ[fun ω => W (X (t+1) ω) | F t]) ω ≤ I ω+G ω*(μ[R | F t]) ω at Bound
    have CNonnegative : 0≤D*Real.exp (-Lambda*(b-a)) := mul_nonneg NonnegativeD (Real.exp_pos _).le
    by_cases AtTarget : X t ω≤a
    · have IW : I ω=1 := if_pos AtTarget
      have GW : G ω=0 := if_pos AtTarget
      have WW : W (X t ω)=1 := if_pos AtTarget
      rw [IW,GW,zero_mul,add_zero] at Bound
      rw [WW]
      linarith
    · have IW : I ω=0 := if_neg AtTarget
      have GW : G ω=Real.exp (-Lambda*(X t ω-a)) := if_neg AtTarget
      rw [IW,zero_add] at Bound
      by_cases Upper : b≤X t ω
      · have WW : W (X t ω)=0 := ExponentialBarrierAbove a b Lambda _ Ordered Upper
        rw [WW,zero_add]
        have GMajor : G ω≤Real.exp (-Lambda*(b-a)) := by
          rw [GW]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left (sub_le_sub_right Upper a) (neg_nonpos.mpr NonnegativeLambda)
        calc
          _ ≤ G ω*(μ[R | F t]) ω := Bound
          _ ≤ G ω*D := mul_le_mul_of_nonneg_left (Above Upper) (BoundG ω).1
          _ ≤ _ := by simpa only [mul_comm D] using mul_le_mul_of_nonneg_right GMajor NonnegativeD
      · have WW : W (X t ω)=G ω := by
          dsimp [W, ExponentialBarrierPotential]
          rw [if_neg AtTarget,if_neg Upper,GW]
        have MomentBound := Inside ⟨lt_of_not_ge AtTarget,lt_of_not_ge Upper⟩
        have Scaled := mul_le_mul_of_nonneg_left MomentBound (BoundG ω).1
        rw [mul_one] at Scaled
        rw [WW]
        linarith
  have Integrated := integral_mono_ae (integrable_condExp (f := fun ω => W (X (t+1) ω)))
    (CurrentIntegrable.add (integrable_const _)) Pointwise
  simp only [Pi.add_apply] at Integrated
  rw [integral_condExp (F.le t), integral_add CurrentIntegrable (integrable_const _),
    integral_const, probReal_univ, one_smul] at Integrated
  exact Integrated

/-- Exponential interval-crossing tail with explicit moment integrability
and complete-history bounds. No common finite potential range is assumed. -/
theorem ExponentialBarrierHittingTailOfCondExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (AdaptedX : Adapted F X) (a b Lambda D : ℝ)
    (Ordered : a<b) (NonnegativeLambda : 0≤Lambda) (NonnegativeD : 0≤D)
    (InitiallyAbove : ∀ᵐ ω ∂μ, b≤X 0 ω)
    (Absorbing : ∀ t, ∀ᵐ ω ∂μ, X t ω≤a → X (t+1) ω≤a)
    (MomentIntegrable : ∀ t, Integrable (fun ω => Real.exp (-Lambda*(X (t+1) ω-X t ω))) μ)
    (Interior : ∀ t, ∀ᵐ ω ∂μ, a<X t ω ∧ X t ω<b →
      (μ[fun u => Real.exp (-Lambda*(X (t+1) u-X t u)) | F t]) ω ≤ 1)
    (Entrance : ∀ t, ∀ᵐ ω ∂μ, b≤X t ω →
      (μ[fun u => Real.exp (-Lambda*(X (t+1) u-X t u)) | F t]) ω ≤ D) (t : ℕ) :
    μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)} ≤
      ENNReal.ofReal ((t : ℝ)*D*Real.exp (-Lambda*(b-a))) := by
  let W := ExponentialBarrierPotential a b Lambda
  let C := D*Real.exp (-Lambda*(b-a))
  have InitialMean : (∫ ω, W (X 0 ω) ∂μ)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [InitiallyAbove] with ω Above
    exact ExponentialBarrierAbove a b Lambda (X 0 ω) Ordered Above
  have Growth (j : ℕ) : (∫ ω, W (X j ω) ∂μ)≤(j : ℝ)*C := by
    induction j with
    | zero => rw [InitialMean,Nat.cast_zero,zero_mul]
    | succ j Before =>
      have Step := ExponentialBarrierExpectedStepOfCondExp μ X F AdaptedX a b Lambda D
        Ordered NonnegativeLambda NonnegativeD j (MomentIntegrable j) (Interior j) (Entrance j)
      calc
        _ ≤ (∫ ω, W (X j ω) ∂μ)+C := Step
        _ ≤ (j : ℝ)*C+C := add_le_add Before le_rfl
        _ = _ := by rw [Nat.cast_add,Nat.cast_one]; ring
  have Event : μ {ω | FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)} =
      μ {ω | X t ω≤a} := by
    apply measure_congr
    filter_upwards [ae_all_iff.mpr Absorbing] with ω Stays
    apply propext
    change (FirstHittingTime (fun s : ℝ => s≤a) (fun j => X j ω)≤(t : WithTop ℕ)) ↔ X t ω≤a
    rw [FirstHittingTimeLeIff]
    constructor
    · rintro ⟨j,Before,AtTarget⟩
      exact Nat.le_induction AtTarget (fun k _ Previous => Stays k Previous) t Before
    · intro AtTarget
      exact ⟨t,le_rfl,AtTarget⟩
  rw [Event]
  have IntegrableW := ExponentialBarrierIntegrable μ (X t) a b Lambda NonnegativeLambda AdaptedX.measurable
  have Markov := IntegrableW.measure_le_integral
    (ae_of_all _ (fun ω => ExponentialBarrierNonnegative a b Lambda (X t ω)))
    (s := {ω | X t ω≤a}) (by
      intro ω AtTarget
      change X t ω≤a at AtTarget
      rw [ExponentialBarrierPotential,if_pos AtTarget])
  apply Markov.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [C,mul_assoc] using Growth t

end
end ECTheoryLib.Tools.Drift
