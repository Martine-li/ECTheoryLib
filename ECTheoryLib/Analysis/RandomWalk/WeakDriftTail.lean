import ECTheoryLib.Analysis.RandomWalk.ExcursionBounds
import ECTheoryLib.Analysis.RandomWalk.ExitRuntime
import ECTheoryLib.Analysis.RandomWalk.WeakDriftRuntime
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# High-probability cubic runtime for the weak-drift example

Source: Lengler, Example 2.4.6, printed page 118. For n>=2 and
N>=n*floor(sqrt(n)), failure by n^3 is at most 3/floor(sqrt(n)),
hence at most 6/sqrt(n). The original n^5 exact mean remains intact.
The proof uses quadratic exit drift and a supermartingale excursion bound.
-/

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- Either exit is late, or a trajectory avoiding zero must have reached m.
The first term is an upper-excursion probability; the second is an exit-time bound. -/
theorem FixedRuntimeTailByBarrier (N m : ℕ) (PositiveM : 0<m) (Capacity : m≤N)
    (ε : I) (SmallBias : (ε : ℝ)*m<1) (x : Fin (N+1)) (t : ℕ) (PositiveT : 0<t) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N ε) (PMF.pure x))
      {Path | (t : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path} ≤
      ENNReal.ofReal ((x.val : ℝ)/m)+
        ENNReal.ofReal (Probability.FiniteBiasedWalk.ExitPotential m x/(1-(ε : ℝ)*m))/(t : ENNReal) := by
  let Step := Probability.FiniteBiasedWalk.Step N ε
  let μ := PathMeasure Step (PMF.pure x)
  let Exit : Fin (N+1) → Prop := fun y => y.val=0 ∨ m≤y.val
  have Included : {Path | (t : WithTop ℕ)<FirstHittingTime (fun y : Fin (N+1) => y.val=0) Path} ⊆
      {Path | FirstHittingTime (fun y : Fin (N+1) => (m : ℝ)≤(y.val : ℝ)) Path≤(t : WithTop ℕ)} ∪
      {Path | (t : WithTop ℕ)<FirstHittingTime Exit Path} := by
    intro Path Late
    by_cases ExitLate : (t : WithTop ℕ)<FirstHittingTime Exit Path
    · exact Or.inr ExitLate
    · obtain ⟨j,Before,Hit⟩ := (FirstHittingTimeLeIff Exit Path t).mp (le_of_not_gt ExitLate)
      rcases Hit with Zero | Upper
      · exact (not_le_of_gt Late ((FirstHittingTimeLeIff _ Path t).mpr ⟨j,Before,Zero⟩)).elim
      · exact Or.inl ((FirstHittingTimeLeIff _ Path t).mpr ⟨j,Before,Nat.cast_le.mpr Upper⟩)
  have Upper := UpperBarrierByTime N ε x (m : ℝ) (Nat.cast_pos.mpr PositiveM) t
  have ExitTail := FirstHittingTimeTailOfExpected Step (PMF.pure x) Exit t PositiveT
  have ExitBound := FixedExitRuntimeUpperBound N m PositiveM Capacity ε SmallBias x
  exact (measure_mono Included).trans ((measure_union_le _ _).trans
    (add_le_add Upper (ExitTail.trans (ENNReal.div_le_div_right ExitBound _))))

end
end ECTheoryLib.Analysis.FiniteBiasedWalk

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability
open scoped unitInterval
noncomputable section

/-- A convenient explicit tail estimate when bias times the upper barrier is at most 1/2. -/
theorem FixedRuntimeTailHalfBias (N m : ℕ) (PositiveM : 0<m) (Capacity : m≤N)
    (ε : I) (HalfBias : (ε : ℝ)*m≤1/2) (x : Fin (N+1)) (Below : x.val≤m)
    (t : ℕ) (PositiveT : 0<t) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N ε) (PMF.pure x))
      {Path | (t : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path} ≤
      ENNReal.ofReal ((x.val : ℝ)/m+2*x.val*m/t) := by
  have SmallBias : (ε : ℝ)*m<1 := lt_of_le_of_lt HalfBias (by norm_num)
  have DenPositive : 0<1-(ε : ℝ)*m := sub_pos.mpr SmallBias
  have ProductNonnegative : 0≤(x.val : ℝ)*m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have Quadratic : Probability.FiniteBiasedWalk.ExitPotential m x≤(x.val : ℝ)*m := by
    simp only [Probability.FiniteBiasedWalk.ExitPotential,min_eq_left Below]
    nlinarith [sq_nonneg (x.val : ℝ)]
  have ExitMean : Probability.FiniteBiasedWalk.ExitPotential m x/(1-(ε : ℝ)*m)≤2*x.val*m := by
    apply (div_le_iff₀ DenPositive).mpr
    nlinarith [mul_nonneg ProductNonnegative (show 0≤1/2-(ε : ℝ)*m by linarith)]
  have ExitPart : ENNReal.ofReal (Probability.FiniteBiasedWalk.ExitPotential m x/(1-(ε : ℝ)*m))/(t : ENNReal)≤
      ENNReal.ofReal (2*x.val*m/t) := by
    calc
      _ ≤ ENNReal.ofReal (2*x.val*m)/(t : ENNReal) :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal ExitMean) _
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr PositiveT),ENNReal.ofReal_natCast]
  have Bound := FixedRuntimeTailByBarrier N m PositiveM Capacity ε SmallBias x t PositiveT
  apply Bound.trans
  rw [ENNReal.ofReal_add (by positivity : 0≤(x.val : ℝ)/m) (by positivity : 0≤2*(x.val : ℝ)*m/t)]
  exact add_le_add le_rfl ExitPart

/-- Choose an auxiliary integer scale k with k^2≤n. This gives a quantitative
high-probability n^3 bound for the actual walk with bias 1/n^4. -/
theorem WeakDriftCubicTail (n k N : ℕ) (AtLeastTwo : 2≤n) (PositiveK : 0<k)
    (SquaredScale : k*k≤n) (Capacity : n*k≤N) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N (WeakBias n (by omega)))
      (PMF.pure ⟨n,by have := Nat.le_mul_of_pos_right n PositiveK; omega⟩))
      {Path | ((n^3 : ℕ) : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path} ≤
      ENNReal.ofReal (3/(k : ℝ)) := by
  have NPositive : (0 : ℝ)<n := Nat.cast_pos.mpr (by omega)
  have KPositive : (0 : ℝ)<k := Nat.cast_pos.mpr PositiveK
  have NTwo : (2 : ℝ)≤n := Nat.cast_le.mpr AtLeastTwo
  have KOne : (1 : ℝ)≤k := Nat.one_le_cast.mpr PositiveK
  have Square : (k : ℝ)*(k : ℝ)≤n := by exact_mod_cast SquaredScale
  have KLeN : (k : ℝ)≤n := by nlinarith
  have HalfBias : (WeakBias n (by omega) : ℝ)*((n*k : ℕ) : ℝ)≤1/2 := by
    change (1/(n : ℝ)^4)*((n*k : ℕ) : ℝ)≤1/2
    rw [Nat.cast_mul,one_div,inv_mul_eq_div]
    apply (div_le_iff₀ (pow_pos NPositive 4)).mpr
    have Product : (n : ℝ)*k≤(n : ℝ)^2 := by nlinarith
    have SquareTwo : (2 : ℝ)≤(n : ℝ)^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr SquareTwo)]
  have Bound := FixedRuntimeTailHalfBias N (n*k) (Nat.mul_pos (by omega) PositiveK) Capacity
    (WeakBias n (by omega)) HalfBias ⟨n,by have := Nat.le_mul_of_pos_right n PositiveK; omega⟩
    (Nat.le_mul_of_pos_right n PositiveK) (n^3) (pow_pos (by omega) 3)
  apply Bound.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Nat.cast_mul,Nat.cast_pow]
  calc
    (n : ℝ)/(n*k)+2*n*(n*k)/n^3 = 1/k+2*k/n := by
      field_simp [NPositive.ne',KPositive.ne']
    _ ≤ 3/k := by
      have Ratio : (k : ℝ)/n≤1/k := (div_le_div_iff₀ NPositive KPositive).mpr (by nlinarith)
      calc
        1/(k : ℝ)+2*k/n = 1/k+2*(k/n) := by ring
        _ ≤ 1/k+2*(1/k) := add_le_add le_rfl (mul_le_mul_of_nonneg_left Ratio (by norm_num))
        _ = 3/k := by ring

end
end ECTheoryLib.Analysis.FiniteBiasedWalk

namespace ECTheoryLib.Analysis.FiniteBiasedWalk
open MeasureTheory ProbabilityTheory ECTheoryLib.Probability Filter
open scoped unitInterval Topology
noncomputable section

/-- The floor square root gives a concrete vanishing failure bound. -/
theorem WeakDriftCubicTailSqrt (n N : ℕ) (AtLeastTwo : 2≤n)
    (Capacity : n*Nat.sqrt n≤N) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N (WeakBias n (by omega)))
      (PMF.pure ⟨n,by have := Nat.le_mul_of_pos_right n (Nat.sqrt_pos.mpr (by omega : 0<n)); omega⟩))
      {Path | ((n^3 : ℕ) : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path} ≤
      ENNReal.ofReal (3/(Nat.sqrt n : ℝ)) :=
  WeakDriftCubicTail n (Nat.sqrt n) N AtLeastTwo (Nat.sqrt_pos.mpr (by omega)) (Nat.sqrt_le n) Capacity

/-- An explicit version of the source's O(n^(-1/2)) failure probability. -/
theorem WeakDriftCubicTailRealSqrt (n N : ℕ) (AtLeastTwo : 2≤n)
    (Capacity : n*Nat.sqrt n≤N) :
    (PathMeasure (Probability.FiniteBiasedWalk.Step N (WeakBias n (by omega)))
      (PMF.pure ⟨n,by have := Nat.le_mul_of_pos_right n (Nat.sqrt_pos.mpr (by omega : 0<n)); omega⟩))
      {Path | ((n^3 : ℕ) : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path} ≤
      ENNReal.ofReal (6/Real.sqrt n) := by
  apply (WeakDriftCubicTailSqrt n N AtLeastTwo Capacity).trans
  apply ENNReal.ofReal_le_ofReal
  have RootPositive : (0 : ℝ)<Nat.sqrt n := Nat.cast_pos.mpr (Nat.sqrt_pos.mpr (by omega))
  have RootOne : (1 : ℝ)≤Nat.sqrt n := Nat.one_le_cast.mpr (Nat.sqrt_pos.mpr (by omega))
  have RealPositive : 0<Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  apply (div_le_div_iff₀ RootPositive RealPositive).mpr
  have Compare := Real.real_sqrt_le_nat_sqrt_succ (a := n)
  nlinarith

/-- For any sufficiently large state-space family, failure to hit by n^3
has probability tending to zero. Shift the index by two to keep all laws defined. -/
theorem WeakDriftCubicHighProbability (N : ℕ → ℕ)
    (Capacity : ∀ j, (j+2)*Nat.sqrt (j+2)≤N j) :
    Tendsto (fun j =>
      (PathMeasure (Probability.FiniteBiasedWalk.Step (N j) (WeakBias (j+2) (by omega)))
        (PMF.pure ⟨j+2,by
          have := Nat.le_mul_of_pos_right (j+2) (Nat.sqrt_pos.mpr (by omega : 0<j+2))
          have := Capacity j
          omega⟩))
        {Path | (((j+2)^3 : ℕ) : WithTop ℕ)<FirstHittingTime (fun y => y.val=0) Path})
      atTop (𝓝 0) := by
  have RootGrowth : Tendsto (fun j : ℕ => Nat.sqrt (j+2)) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro b
    refine ⟨b*b,fun j Bound => ?_⟩
    exact Nat.le_sqrt.mpr (by omega)
  have Decay : Tendsto (fun j : ℕ => 3/(Nat.sqrt (j+2) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp RootGrowth
  have ExtendedDecay : Tendsto (fun j : ℕ => ENNReal.ofReal (3/(Nat.sqrt (j+2) : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal Decay
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ExtendedDecay
    (fun _ => zero_le) (fun j => WeakDriftCubicTailSqrt (j+2) (N j) (by omega) (Capacity j))

end
end ECTheoryLib.Analysis.FiniteBiasedWalk
