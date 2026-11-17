import ECTheoryLib.Analysis.OneMinMax.NSGAII.CrowdingRetention
import ECTheoryLib.Analysis.OneMinMax.Archive.Coverage
import ECTheoryLib.SearchSpaces.BitPopulation
import ECTheoryLib.Algorithms.FixedPopulation

/-!
# Population coverage state and representation bridges

Runtime is measured on the existing ordered-list transition, retaining duplicate
individuals. Only the observation of represented Hamming weights is deduplicated.
Success means simultaneous current coverage of all n+1 weights. The weighted
deficit has a finite range on *every* list, including lists outside the fixed-size
invariant. Fixed-population wrappers forget to the original laws exactly.
-/
namespace ECTheoryLib.Analysis.NSGAIIOneMinMax
open Operators.Selection Tools.Coverage
noncomputable section

/-- Hamming weights represented in the current population, ignoring multiplicity
only for this observation, not for the algorithm's state or parent sampling. -/
def Observed {n : ℕ} (Pool : List (Bits n)) : Finset ℕ := Pool.toFinset.image OneMax

/-- Current simultaneous representation of all Pareto objective values. -/
def Complete {n : ℕ} (Pool : List (Bits n)) : Prop := Finset.range (n + 1) ⊆ Observed Pool

/-- Symmetric harmonic weight of missing levels, shared with the archive analysis. -/
def Potential {n : ℕ} (Pool : List (Bits n)) : ℝ :=
  MissingWeight (Finset.range (n + 1)) (Observed Pool) (LineWeight n)

theorem ObservedWithin {n : ℕ} (Pool : List (Bits n)) : Observed Pool ⊆ Finset.range (n + 1) := by
  intro j Present
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp Present
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Problems.OneMax.OneMaxLeN x))

/-- Membership of an observed weight provides an actual current individual. -/
theorem ObservedIff {n : ℕ} (Pool : List (Bits n)) (j : ℕ) :
    j ∈ Observed Pool ↔ ∃ x ∈ Pool, OneMax x = j := by
  simp only [Observed, Finset.mem_image, List.mem_toFinset]

theorem PotentialNonnegative {n : ℕ} (Pool : List (Bits n)) : 0 ≤ Potential Pool :=
  MissingWeightNonnegative _ _ _ (fun j _ => (LineWeightPositive n j).le)

/-- Zero deficit is equivalent to current full-front coverage, including time zero. -/
theorem PotentialZeroIffComplete {n : ℕ} (Pool : List (Bits n)) : Potential Pool = 0 ↔ Complete Pool :=
  MissingWeightEqZeroIff _ _ _ (fun j _ => LineWeightPositive n j)

/-- Uniform bound independent of the number and multiplicity of occurrences. -/
theorem PotentialBound {n : ℕ} (Pool : List (Bits n)) : Potential Pool ≤ 2 * (harmonic (n + 1) : ℝ) := by
  exact (MissingWeightLeTotal _ _ _ (fun j _ => (LineWeightPositive n j).le)).trans_eq (LineWeightTotal n)

/-- A finite set containing the potential of every raw list, not merely reachable
or fixed-size lists. This supplies the pointwise range premise of scalar drift. -/
def PotentialValues (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).powerset.image (fun S => MissingWeight (Finset.range (n + 1)) S (LineWeight n))

/-- The finite range contains every raw-list potential, without a reachability premise. -/
theorem PotentialInValues {n : ℕ} (Pool : List (Bits n)) : Potential Pool ∈ PotentialValues n :=
  Finset.mem_image.mpr ⟨Observed Pool, Finset.mem_powerset.mpr (ObservedWithin Pool), rfl⟩

theorem ZeroInValues (n : ℕ) : 0 ∈ PotentialValues n := by
  apply Finset.mem_image.mpr
  refine ⟨Finset.range (n + 1), Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_⟩
  simp only [MissingWeight, Finset.sum_eq_zero (fun j Present => if_pos Present)]

/-- A nonempty list induces a decision archive only for reusing deterministic
coverage geometry. This is not a replacement for the population transition law. -/
def AsArchive {n : ℕ} (Pool : List (Bits n)) (Nonempty : Pool ≠ []) : ParetoPopulation (Bits n) :=
  ⟨Pool.toFinset, by
    cases Pool with
    | nil => exact False.elim (Nonempty rfl)
    | cons x Tail => exact ⟨x, by simp only [List.toFinset_cons, Finset.mem_insert_self]⟩⟩

/-- The archive view and the original population represent exactly the same weights. -/
theorem AsArchiveObserved {n : ℕ} (Pool : List (Bits n)) (Nonempty : Pool ≠ []) :
    OneMinMaxCoverage.Observed (AsArchive Pool Nonempty) = Observed Pool := rfl

/-- Forgetting duplicate occurrences only in the geometric view preserves this
coverage potential, allowing reuse of the archive's deterministic progress proof. -/
theorem AsArchivePotential {n : ℕ} (Pool : List (Bits n)) (Nonempty : Pool ≠ []) :
    OneMinMaxCoverage.Potential (AsArchive Pool Nonempty) = Potential Pool := rfl

/-- Every supported environmental selection retains the input weights when the
proved capacity condition holds. The input may include arbitrary duplicates. -/
theorem EnvironmentObserved {n : ℕ} (Pool Result : List (Bits n)) (Capacity : ℕ)
    (Room : 4 * (n + 1) ≤ Capacity)
    (Possible : Result ∈ (NSGAIIEnvironment Fitness Capacity Pool).support) :
    Observed Pool ⊆ Observed Result := by
  intro j Present
  obtain ⟨x, InPool, Same⟩ := (ObservedIff Pool j).mp Present
  obtain ⟨y, InResult, Equal⟩ := EnvironmentRetainsWeight Pool Result Capacity Room Possible x InPool
  exact (ObservedIff Result j).mpr ⟨y, InResult, Equal.trans Same⟩

/-- The actual NSGA-II generation retains every old represented value. -/
theorem StepObserved {n : ℕ} (Mutation : Bits n → PMF (Bits n)) (Pool Result : List (Bits n))
    (Room : 4 * (n + 1) ≤ Pool.length)
    (Possible : Result ∈ (NSGAIIStep Mutation Fitness Pool).support) : Observed Pool ⊆ Observed Result := by
  have Nonempty : Pool ≠ [] := by intro Empty; simp only [Empty, List.length_nil] at Room; omega
  have NotEmpty : Pool.isEmpty = false := by
    cases Pool with
    | nil => exact False.elim (Nonempty rfl)
    | cons x Tail => rfl
  simp only [NSGAIIStep, NotEmpty, Bool.false_eq_true, if_false] at Possible
  obtain ⟨Offspring, _, Selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
  have Retained := EnvironmentObserved (Pool ++ Offspring) Result Pool.length Room Selected
  intro j Present
  obtain ⟨x, InPool, Same⟩ := (ObservedIff Pool j).mp Present
  exact Retained ((ObservedIff (Pool ++ Offspring) j).mpr ⟨x, List.mem_append_left _ InPool, Same⟩)

/-- Under the capacity condition, the goal is absorbing as a property even though
the population may continue changing its representatives after full coverage. -/
theorem StepComplete {n : ℕ} (Mutation : Bits n → PMF (Bits n)) (Pool Result : List (Bits n))
    (Room : 4 * (n + 1) ≤ Pool.length) (Covered : Complete Pool)
    (Possible : Result ∈ (NSGAIIStep Mutation Fitness Pool).support) : Complete Result :=
  Covered.trans (StepObserved Mutation Pool Result Room Possible)

/-- The fixed-size representation forgets to the exact existing NSGA-II list
kernel; no probabilities, occurrence order, or multiplicities are changed. -/
theorem FixedStepForget {n : ℕ} (Mutation : Bits n → PMF (Bits n)) (N : ℕ)
    (Pool : FixedPopulation (Bits n) N) :
    (FixedPopulationStep (NSGAIIStep Mutation Fitness) (NSGAIIStepLength Mutation Fitness) N Pool).map
      Subtype.val = NSGAIIStep Mutation Fitness Pool.val :=
  FixedPopulationStepForget _ _ N Pool

/-- The fixed-size initialization forgets to the actual independent uniform
list initializer, including repeated initial individuals. -/
theorem FixedInitialForget (n N : ℕ) :
    (FixedPopulationLaw (PopulationInit n N) N (PopulationInitLength n N)).map Subtype.val = PopulationInit n N :=
  FixedPopulationLawForget _ _ _

end
end ECTheoryLib.Analysis.NSGAIIOneMinMax
