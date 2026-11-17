import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Dominance ranks and finite population selection

List positions distinguish occurrences, including repeated genotypes. All rational
objectives are maximized. `RankDepth` computes bounded strict-dominance chain
lengths by finite dynamic programming; the rank uses as many rounds as there are
population occurrences. No implementation-complexity guarantee is asserted.
Selection sorts and takes occurrences; it does not deduplicate genotypes.
-/

namespace ECTheoryLib.Operators.Selection

/-- Weak improvement in every objective and strict improvement in at least one.
Arguments are the dominating point followed by the dominated point. -/
def StrictlyDominates {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (x y : α) : Prop :=
  (∀ i, Fitness y i ≤ Fitness x i) ∧ ∃ i, Fitness y i < Fitness x i

instance {α : Type*} {m : Nat} (Fitness : α → Fin m → ℚ) :
    DecidableRel (StrictlyDominates Fitness) := by
  intro x y
  unfold StrictlyDominates
  infer_instance

theorem StrictlyDominatesIrreflexive {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (x : α) : ¬ StrictlyDominates Fitness x x := by
  intro Dominance
  obtain ⟨i, StrictImprovement⟩ := Dominance.2
  exact (lt_irrefl (Fitness x i)) StrictImprovement

theorem StrictlyDominatesTransitive {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) {x y z : α}
    (XY : StrictlyDominates Fitness x y)
    (YZ : StrictlyDominates Fitness y z) : StrictlyDominates Fitness x z := by
  constructor
  · intro i
    exact le_trans (YZ.1 i) (XY.1 i)
  · obtain ⟨i, StrictImprovement⟩ := XY.2
    exact ⟨i, lt_of_le_of_lt (YZ.1 i) StrictImprovement⟩

/-- Maximum strict-dominance chain length with at most the given number of edges. -/
def RankDepth {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) : Nat → α → Nat
  | 0, _ => 0
  | Depth + 1, x =>
      Finset.univ.sup (fun j : Fin Pool.length =>
        if StrictlyDominates Fitness Pool[j] x then
          RankDepth Fitness Pool Depth Pool[j] + 1
        else 0)

/-- Nondomination rank starting at zero, computed with population-length depth.
Equal objective vectors do not strictly dominate one another. -/
def ParetoRank {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α) : Nat :=
  RankDepth Fitness Pool Pool.length x

theorem RankDepthOfNondominated {α : Type*} {m : Nat}
    (Fitness : α → Fin m → ℚ) (Pool : List α) (x : α)
    (Nondominated : ∀ j : Fin Pool.length, ¬ StrictlyDominates Fitness Pool[j] x)
    (Depth : Nat) : RankDepth Fitness Pool Depth x = 0 := by
  cases Depth with
  | zero => rfl
  | succ Depth =>
      unfold RankDepth
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro j _
      rw [if_neg (Nondominated j)]

/-- Sort and take at most the requested number of occurrences, retaining multiplicities. -/
def SelectByOrder {α : Type*} (Capacity : Nat) (Pool : List α)
    (Better : α → α → Bool) : List α :=
  (Pool.mergeSort Better).take Capacity

theorem SelectByOrderLength {α : Type*} (Capacity : Nat) (Pool : List α)
    (Better : α → α → Bool) :
    (SelectByOrder Capacity Pool Better).length = min Capacity Pool.length := by
  unfold SelectByOrder
  rw [List.length_take, List.length_mergeSort]

theorem SelectByOrderMember {α : Type*} (Capacity : Nat) (Pool : List α)
    (Better : α → α → Bool) {x : α}
    (Selected : x ∈ SelectByOrder Capacity Pool Better) : x ∈ Pool := by
  have InSorted : x ∈ Pool.mergeSort Better := List.mem_of_mem_take Selected
  exact List.mem_mergeSort.mp InSorted

noncomputable section

/-- Independent repeated sampling from a fixed PMF, preserving sample order. -/
def IndependentSamples {α : Type*} (Distribution : PMF α) : Nat → PMF (List α)
  | 0 => PMF.pure []
  | Count + 1 => Distribution.bind (fun x =>
      (IndependentSamples Distribution Count).map (fun Tail => x :: Tail))

theorem IndependentSamplesLength {α : Type*} (Distribution : PMF α)
    (Count : Nat) (Samples : List α)
    (Possible : Samples ∈ (IndependentSamples Distribution Count).support) :
    Samples.length = Count := by
  induction Count generalizing Samples with
  | zero =>
      have SamplesEmpty : Samples = [] := by
        exact (PMF.mem_support_pure_iff _ _).mp Possible
      rw [SamplesEmpty]
      rfl
  | succ Count Previous =>
      obtain ⟨x, _, TailPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
      obtain ⟨Tail, TailSupport, SamplesEqual⟩ := (PMF.mem_support_map_iff _ _ _).mp TailPossible
      rw [← SamplesEqual, List.length_cons, Previous Tail TailSupport]

/-- Uniform sampling of all permutations of occurrence positions for tie-breaking. -/
def UniformTiePermutation (Count : Nat) : PMF (Equiv.Perm (Fin Count)) :=
  PMF.uniformOfFintype (Equiv.Perm (Fin Count))

end
end ECTheoryLib.Operators.Selection
