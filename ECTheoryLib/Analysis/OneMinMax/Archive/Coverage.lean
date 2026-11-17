import ECTheoryLib.Problems.ParetoFront
import ECTheoryLib.Problems.OneMinMax
import ECTheoryLib.Operators.Selection.ParetoArchive
import ECTheoryLib.Tools.Coverage.Line

/-!
# Current Pareto-front coverage on OneMinMax

An archive is successful exactly when it currently represents every weight
`0, ..., n`. Every search point is Pareto optimal, so first reaching one Pareto
point would not express the runtime task. Weak dominance equals equality of
weight. Consequently the actual archive update retains every observed objective
value, while replacing representatives with equal objective vectors.

The weighted deficit is defined on every nonempty archive. Valid archives have
at most `n+1` members; validity is needed for parent-probability bounds, but is
not needed for objective-value retention or monotonicity of the potential.
-/
namespace ECTheoryLib.Analysis.OneMinMaxCoverage
open Tools.Coverage
noncomputable section

/-- The archive relation maximizes the pair (number of ones, number of zeros). -/
abbrev Dominates {n : Nat} : Bits n → Bits n → Prop :=
  Problems.ParetoMaxNotWorse ECTheoryLib.OneMinMax

/-- Objective values represented by the current archive, encoded by their one count. -/
def Observed {n : Nat} (P : ParetoPopulation (Bits n)) : Finset Nat :=
  Problems.ObservedValues OneMax P.val

/-- Simultaneous coverage of all `n+1` Pareto objective values. -/
def Complete {n : Nat} (P : ParetoPopulation (Bits n)) : Prop :=
  Problems.CoversTargets OneMax (Finset.range (n + 1)) P.val

/-- Sum of the symmetric reciprocal weights of currently missing levels. -/
def Potential {n : Nat} (P : ParetoPopulation (Bits n)) : ℝ :=
  MissingWeight (Finset.range (n + 1)) (Observed P) (LineWeight n)

/-- Pairwise nondominance, including the absence of duplicate objective vectors. -/
abbrev Valid {n : Nat} (P : ParetoPopulation (Bits n)) : Prop :=
  ParetoArchiveValid Dominates P.val

/-- The existing (G)SEMO archive update specialized to OneMinMax. -/
abbrev Update {n : Nat} (P : ParetoPopulation (Bits n)) (y : Bits n) :=
  ParetoPopulationUpdate Dominates P y

/-- Every observed weight is a target level. -/
theorem ObservedWithin {n : Nat} (P : ParetoPopulation (Bits n)) :
    Observed P ⊆ Finset.range (n + 1) := by
  intro j Present
  obtain ⟨x, _InP, rfl⟩ := Finset.mem_image.mp Present
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Problems.OneMax.OneMaxLeN x))

/-- Nonempty decision archives have a represented objective value. -/
theorem ObservedNonempty {n : Nat} (P : ParetoPopulation (Bits n)) :
    (Observed P).Nonempty := P.property.image OneMax

/-- Coverage in the integer encoding means a current representative for every level. -/
theorem CompleteIff {n : Nat} (P : ParetoPopulation (Bits n)) :
    Complete P ↔ ∀ j ≤ n, ∃ x ∈ P.val, OneMax x = j := by
  rw [Complete, Problems.CoversTargetsIff]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- The integer-level encoding is equivalent to representing every attainable
objective vector. On OneMinMax every attainable objective vector is Pareto optimal. -/
theorem CompleteIffObjectiveVectors {n : Nat} (P : ParetoPopulation (Bits n)) :
    Complete P ↔ ∀ y : Bits n, ∃ x ∈ P.val, ECTheoryLib.OneMinMax x = ECTheoryLib.OneMinMax y := by
  rw [CompleteIff]
  constructor
  · intro Covered y
    obtain ⟨x, InP, Equal⟩ := Covered (OneMax y) (Problems.OneMax.OneMaxLeN y)
    refine ⟨x, InP, ?_⟩
    unfold ECTheoryLib.OneMinMax OneMin
    rw [Equal]
  · intro Covered j Bound
    obtain ⟨x, InP, Equal⟩ := Covered (PrefixOnes n j)
    refine ⟨x, InP, ?_⟩
    have FirstObjective := congrFun Equal 0
    change OneMax x = OneMax (PrefixOnes n j) at FirstObjective
    rw [Problems.LeadingOnes.OneMaxPrefixOnes Bound] at FirstObjective
    exact FirstObjective

/-- All points on OneMinMax are mutually non-strictly-dominated, so every offspring
is accepted, even when it merely replaces an equal-weight representative. -/
theorem AcceptsEveryCandidate {n : Nat} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    ParetoArchiveAccepts Dominates P.val y := by
  intro x _InP Strict
  apply Strict.2
  apply (Problems.OneMinMax.WeakDominanceIffEqualWeight x y).mpr
  exact ((Problems.OneMinMax.WeakDominanceIffEqualWeight y x).mp Strict.1).symm

/-- Updating the actual decision archive inserts the new weight and retains all old
weights. Retention concerns objective values, not the identities of representatives. -/
theorem ObservedUpdate {n : Nat} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    Observed (Update P y) = insert (OneMax y) (Observed P) := by
  ext j
  constructor
  · intro Present
    obtain ⟨x, InUpdate, Value⟩ := Finset.mem_image.mp Present
    change x ∈ ParetoArchiveUpdate Dominates P.val y at InUpdate
    rw [ParetoArchiveUpdateMembership Dominates P.val y x (AcceptsEveryCandidate P y)] at InUpdate
    rcases InUpdate with Equal | Old
    · exact Finset.mem_insert.mpr (Or.inl (Value.symm.trans (congrArg OneMax Equal)))
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Old.1, Value⟩)
  · intro Present
    rcases Finset.mem_insert.mp Present with Equal | Old
    · exact Finset.mem_image.mpr ⟨y, ParetoArchiveCandidateMem Dominates P.val y
        (AcceptsEveryCandidate P y), Equal.symm⟩
    · obtain ⟨x, InP, Value⟩ := Finset.mem_image.mp Old
      by_cases Same : OneMax x = OneMax y
      · exact Finset.mem_image.mpr ⟨y, ParetoArchiveCandidateMem Dominates P.val y
          (AcceptsEveryCandidate P y), Same.symm.trans Value⟩
      · have NotDominated : ¬ Dominates y x := by
          intro Dominated
          exact Same ((Problems.OneMinMax.WeakDominanceIffEqualWeight x y).mp Dominated)
        exact Finset.mem_image.mpr ⟨x,
          (ParetoArchiveUpdateMembership Dominates P.val y x
            (AcceptsEveryCandidate P y)).mpr (Or.inr ⟨InP, NotDominated⟩), Value⟩

/-- A valid archive has at most one representative per objective vector and hence
at most `n+1` members. This is the premise needed for uniform-parent bounds. -/
theorem ArchiveSizeBound {n : Nat} (P : ParetoPopulation (Bits n)) (IsValid : Valid P) :
    P.val.card ≤ n + 1 := by
  have Injective : Set.InjOn OneMax (P.val : Set (Bits n)) := by
    intro x InP y InP' Equal
    by_contra Different
    exact IsValid x InP y InP' Different
      ((Problems.OneMinMax.WeakDominanceIffEqualWeight y x).mpr Equal.symm)
  have CardEq : (Observed P).card = P.val.card := Finset.card_image_iff.mpr Injective
  rw [← CardEq]
  exact (Finset.card_le_card (ObservedWithin P)).trans_eq (Finset.card_range (n + 1))

/-- The potential is nonnegative on every archive, including invalid ones. -/
theorem PotentialNonnegative {n : Nat} (P : ParetoPopulation (Bits n)) :
    0 ≤ Potential P :=
  MissingWeightNonnegative _ _ _ (fun j _ => (LineWeightPositive n j).le)

/-- Zero potential is equivalent to current complete front coverage. -/
theorem PotentialZeroIffComplete {n : Nat} (P : ParetoPopulation (Bits n)) :
    Potential P = 0 ↔ Complete P :=
  MissingWeightEqZeroIff _ _ _ (fun j _ => LineWeightPositive n j)

/-- Objective-value retention makes every update's potential decrease nonnegative. -/
theorem UpdateDecreaseNonnegative {n : Nat} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    0 ≤ Potential P - Potential (Update P y) := by
  apply sub_nonneg.mpr
  apply MissingWeightAntitone _ _ _ _ (fun j _ => (LineWeightPositive n j).le)
  rw [ObservedUpdate]
  exact Finset.subset_insert _ _

/-- Generating a missing objective value decreases potential by at least its weight. -/
theorem UpdateDecreaseOfMissing {n : Nat} (P : ParetoPopulation (Bits n)) (y : Bits n)
    (Missing : OneMax y ∉ Observed P) :
    LineWeight n (OneMax y) ≤ Potential P - Potential (Update P y) := by
  apply MissingWeightDecrease _ _ _ _ (fun j _ => (LineWeightPositive n j).le)
  · rw [ObservedUpdate]
    exact Finset.subset_insert _ _
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Problems.OneMax.OneMaxLeN y))
  · exact Missing
  · rw [ObservedUpdate]
    exact Finset.mem_insert_self _ _

/-- A uniform bound on the initial deficit; no shape restriction on the archive is used. -/
theorem PotentialBound {n : Nat} (P : ParetoPopulation (Bits n)) :
    Potential P ≤ 2 * (harmonic (n + 1) : ℝ) := by
  have Bound := MissingWeightLeTotal (Finset.range (n + 1)) (Observed P) (LineWeight n)
    (fun j _ => (LineWeightPositive n j).le)
  rw [LineWeightTotal] at Bound
  exact Bound

end
end ECTheoryLib.Analysis.OneMinMaxCoverage
