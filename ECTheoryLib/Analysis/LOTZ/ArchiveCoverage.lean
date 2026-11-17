import ECTheoryLib.Problems.LOTZGeometry
import ECTheoryLib.Operators.Selection.ParetoArchive
import ECTheoryLib.Tools.Coverage.Line
import ECTheoryLib.Operators.Mutation.BitFlip

/-!
# Two-phase archive potentials for LOTZ

Phase one reaches any true Pareto point. Phase two covers all n+1 true front
points simultaneously in the current archive. Non-Pareto objective values can
be lost; only canonical Pareto points are proved to be retained. The first
potential uses the largest prefix-plus-suffix sum in the archive. The second
counts missing true front points, using the generic finite-coverage machinery.
-/
namespace ECTheoryLib.Analysis.LOTZCoverage
open Tools.Coverage
noncomputable section

/-- Weak dominance for the two maximized LOTZ objectives. -/
abbrev Dominates {n : ℕ} : Bits n → Bits n → Prop :=
  Problems.ParetoMaxNotWorse ECTheoryLib.LOTZ

/-- Actual Pareto archive update; equal objective vectors replace representatives. -/
abbrev Update {n : ℕ} (P : ParetoPopulation (Bits n)) (y : Bits n) :=
  ParetoPopulationUpdate Dominates P y

/-- Pairwise nondominance, excluding distinct representatives with equal vectors. -/
abbrev Valid {n : ℕ} (P : ParetoPopulation (Bits n)) : Prop :=
  ParetoArchiveValid Dominates P.val

/-- True front indices currently represented; non-Pareto points are not counted. -/
def Observed {n : ℕ} (P : ParetoPopulation (Bits n)) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun j => PrefixOnes n j ∈ P.val)

/-- The second phase has started when at least one true Pareto point is present. -/
def Region {n : ℕ} (P : ParetoPopulation (Bits n)) : Prop := (Observed P).Nonempty

/-- All n+1 true Pareto points must coexist in the current archive. -/
def Complete {n : ℕ} (P : ParetoPopulation (Bits n)) : Prop :=
  Finset.range (n + 1) ⊆ Observed P

/-- Prefix-plus-suffix score, bounded by n, with equality precisely at the front. -/
def Score {n : ℕ} (x : Bits n) : ℕ := LeadingOnes x + TrailingZeroes x

/-- The greatest front-approach score among current archive members. -/
def BestScore {n : ℕ} (P : ParetoPopulation (Bits n)) : ℕ := P.val.sup Score

/-- Natural deficit to the first true Pareto point. -/
def FirstLevel {n : ℕ} (P : ParetoPopulation (Bits n)) : ℕ := n - BestScore P

/-- Number of missing true front points, expressed as a real sum. -/
def Missing {n : ℕ} (P : ParetoPopulation (Bits n)) : ℝ :=
  MissingWeight (Finset.range (n + 1)) (Observed P) (fun _ => 1)

/-- Membership in the index encoding records an actual canonical point. -/
theorem ObservedIff {n : ℕ} (P : ParetoPopulation (Bits n)) (j : ℕ) :
    j ∈ Observed P ↔ j ≤ n ∧ PrefixOnes n j ∈ P.val := by
  simp only [Observed, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The coverage goal requires each canonical front point, not just one. -/
theorem CompleteIff {n : ℕ} (P : ParetoPopulation (Bits n)) :
    Complete P ↔ ∀ j ≤ n, PrefixOnes n j ∈ P.val := by
  constructor
  · intro Covered j Bound
    exact ((ObservedIff P j).mp (Covered (Finset.mem_range.mpr (Nat.lt_succ_of_le Bound)))).2
  · intro Covered j InRange
    have Bound := Nat.le_of_lt_succ (Finset.mem_range.mp InRange)
    exact (ObservedIff P j).mpr ⟨Bound, Covered j Bound⟩

/-- An archive containing the complete front necessarily entered phase two. -/
theorem CompleteInRegion {n : ℕ} (P : ParetoPopulation (Bits n)) (Covered : Complete P) :
    Region P := ⟨0, Covered (Finset.mem_range.mpr (Nat.zero_lt_succ n))⟩

/-- Valid LOTZ archives have at most n+1 members. Equal leading-prefix lengths
make their trailing-suffix lengths comparable, so such members must coincide. -/
theorem ArchiveSizeBound {n : ℕ} (P : ParetoPopulation (Bits n)) (IsValid : Valid P) :
    P.val.card ≤ n + 1 := by
  have Injective : Set.InjOn LeadingOnes (P.val : Set (Bits n)) := by
    intro x InX y InY Equal
    by_contra Different
    rcases le_total (TrailingZeroes x) (TrailingZeroes y) with Forward | Backward
    · exact IsValid y InY x InX (Ne.symm Different)
        ((Problems.LOTZ.DominanceIff y x).mpr ⟨Equal.le, Forward⟩)
    · exact IsValid x InX y InY Different
        ((Problems.LOTZ.DominanceIff x y).mpr ⟨Equal.ge, Backward⟩)
  have Within : P.val.image LeadingOnes ⊆ Finset.range (n + 1) := by
    intro j Member
    obtain ⟨x, _InP, rfl⟩ := Finset.mem_image.mp Member
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Problems.LeadingOnes.LeadingOnesLeN x))
  rw [← Finset.card_image_iff.mpr Injective]
  exact (Finset.card_le_card Within).trans_eq (Finset.card_range (n + 1))

/-- Weak dominance cannot decrease the front-approach score. -/
theorem ScoreDominance {n : ℕ} (x y : Bits n) (Dominance : Dominates y x) :
    Score x ≤ Score y := by
  obtain ⟨Prefix, Suffix⟩ := (Problems.LOTZ.DominanceIff y x).mp Dominance
  exact Nat.add_le_add Prefix Suffix

/-- The best score never exceeds the string length. -/
theorem BestScoreBound {n : ℕ} (P : ParetoPopulation (Bits n)) : BestScore P ≤ n := by
  exact Finset.sup_le (fun x _ => Problems.LeadingOnes.LeadingOnesAddTrailingZeroesLeN x)

/-- The first-phase deficit vanishes exactly when a true Pareto point is present. -/
theorem FirstLevelZeroIff {n : ℕ} (P : ParetoPopulation (Bits n)) :
    FirstLevel P = 0 ↔ Region P := by
  constructor
  · intro Zero
    have Best : BestScore P = n := le_antisymm (BestScoreBound P) (Nat.le_of_sub_eq_zero Zero)
    obtain ⟨x, InP, Equal⟩ := Finset.exists_mem_eq_sup P.val P.property Score
    have Full : LeadingOnes x + TrailingZeroes x = n := Equal.symm.trans Best
    have Canonical := (Problems.LOTZ.FullCoverageIffPrefixOnes x).mp Full
    refine ⟨LeadingOnes x, (ObservedIff P _).mpr ⟨Problems.LeadingOnes.LeadingOnesLeN x, ?_⟩⟩
    rw [← Canonical]
    exact InP
  · rintro ⟨j, Present⟩
    obtain ⟨Bound, InP⟩ := (ObservedIff P j).mp Present
    have Best := Finset.le_sup (f := Score) InP
    have FrontScore : Score (PrefixOnes n j) = n := by
      unfold Score
      rw [Problems.LeadingOnes.LeadingOnesPrefixOnes Bound,
        Problems.LeadingOnes.TrailingZeroesPrefixOnes Bound]
      omega
    rw [FrontScore] at Best
    exact Nat.sub_eq_zero_of_le Best

/-- Replacing dominated members cannot reduce the greatest score: the replacing
candidate has at least the score of every removed member. -/
theorem BestScoreUpdate {n : ℕ} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    BestScore P ≤ BestScore (Update P y) := by
  by_cases Accepted : ParetoArchiveAccepts Dominates P.val y
  · apply Finset.sup_le
    intro x InP
    by_cases Removed : Dominates y x
    · apply (ScoreDominance x y Removed).trans
      exact Finset.le_sup (f := Score) (ParetoArchiveCandidateMem Dominates P.val y Accepted)
    · apply Finset.le_sup (f := Score)
      exact (ParetoArchiveUpdateMembership Dominates P.val y x Accepted).mpr (Or.inr ⟨InP, Removed⟩)
  · change P.val.sup Score ≤ (ParetoArchiveUpdate Dominates P.val y).sup Score
    rw [ParetoArchiveUpdateReject Dominates P.val y Accepted]

/-- Nonnegative first-phase progress holds for every candidate. -/
theorem FirstLevelUpdate {n : ℕ} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    FirstLevel (Update P y) ≤ FirstLevel P := Nat.sub_le_sub_left (BestScoreUpdate P y) n

/-- Every true Pareto point already present survives the actual archive update.
The assertion concerns current points; it does not record discovery history. -/
theorem FrontRetained {n j : ℕ} (Bound : j ≤ n) (P : ParetoPopulation (Bits n))
    (y : Bits n) (Present : PrefixOnes n j ∈ P.val) : PrefixOnes n j ∈ (Update P y).val := by
  by_cases Accepted : ParetoArchiveAccepts Dominates P.val y
  · apply (ParetoArchiveUpdateMembership Dominates P.val y _ Accepted).mpr
    by_cases Removed : Dominates y (PrefixOnes n j)
    · exact Or.inl ((Problems.LOTZ.DominatesPrefixIff Bound y).mp Removed).symm
    · exact Or.inr ⟨Present, Removed⟩
  · change PrefixOnes n j ∈ ParetoArchiveUpdate Dominates P.val y
    rw [ParetoArchiveUpdateReject Dominates P.val y Accepted]
    exact Present

/-- True front indices are retained even though non-Pareto archive values may vanish. -/
theorem ObservedRetained {n : ℕ} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    Observed P ⊆ Observed (Update P y) := by
  intro j Present
  obtain ⟨Bound, InP⟩ := (ObservedIff P j).mp Present
  exact (ObservedIff _ j).mpr ⟨Bound, FrontRetained Bound P y InP⟩

/-- A canonical front candidate is always accepted because no point strictly dominates it. -/
theorem FrontAccepted {n j : ℕ} (Bound : j ≤ n) (P : ParetoPopulation (Bits n)) :
    ParetoArchiveAccepts Dominates P.val (PrefixOnes n j) := by
  intro x _InP Strict
  have Equal := (Problems.LOTZ.DominatesPrefixIff Bound x).mp Strict.1
  apply Strict.2
  rw [Equal]
  exact fun _ => le_rfl

/-- Generating a missing true front point reduces the missing count by at least one. -/
theorem MissingProgress {n j : ℕ} (Bound : j ≤ n) (P : ParetoPopulation (Bits n))
    (Absent : j ∉ Observed P) : 1 ≤ Missing P - Missing (Update P (PrefixOnes n j)) := by
  apply MissingWeightDecrease _ _ _ _ (fun _ _ => zero_le_one) (ObservedRetained _ _) j
    (Finset.mem_range.mpr (Nat.lt_succ_of_le Bound)) Absent
  exact (ObservedIff _ j).mpr ⟨Bound,
    ParetoArchiveCandidateMem Dominates P.val _ (FrontAccepted Bound P)⟩

/-- Missing-count potential is nonnegative and vanishes exactly at complete coverage. -/
theorem MissingNonnegative {n : ℕ} (P : ParetoPopulation (Bits n)) : 0 ≤ Missing P :=
  MissingWeightNonnegative _ _ _ (fun _ _ => zero_le_one)

/-- Zero missing count means simultaneous current front coverage. -/
theorem MissingZeroIff {n : ℕ} (P : ParetoPopulation (Bits n)) : Missing P = 0 ↔ Complete P :=
  MissingWeightEqZeroIff _ _ _ (fun _ _ => zero_lt_one)

/-- There are at most n+1 missing front points, for every nonempty archive. -/
theorem MissingBound {n : ℕ} (P : ParetoPopulation (Bits n)) : Missing P ≤ (n : ℝ) + 1 := by
  have Bound := MissingWeightLeTotal (Finset.range (n + 1)) (Observed P) (fun _ => (1 : ℝ))
    (fun _ _ => zero_le_one)
  simpa only [Missing, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_one] using Bound

/-- Retention makes every update's missing-count progress nonnegative. -/
theorem MissingUpdate {n : ℕ} (P : ParetoPopulation (Bits n)) (y : Bits n) :
    Missing (Update P y) ≤ Missing P :=
  MissingWeightAntitone _ _ _ _ (fun _ _ => zero_le_one) (ObservedRetained P y)

end
end ECTheoryLib.Analysis.LOTZCoverage
