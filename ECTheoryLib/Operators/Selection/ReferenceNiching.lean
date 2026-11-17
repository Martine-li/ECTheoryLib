import ECTheoryLib.Operators.Selection.NSGAIIINormalization

/-!
# NSGA-III reference association and occupancy-based niching

Source: Wietheger–Doerr, arXiv:2211.08202, Algorithm 3 for occupancy logic,
with the original Deb–Jain Algorithms 3–4 perpendicular-distance rule,
<https://www.egr.msu.edu/~kdeb/papers/k2012009.pdf>. All distances are
exact rational squared perpendicular distances to reference lines. The reference
system is nonempty and every reference vector is nonzero. Association ties and
least-occupancy reference ties are uniform. The first occupant of a niche is
uniform among its closest individuals; later occupants are uniform among its
remaining individuals (the diversity-preserving alternative allowed in the source).
Individuals are positions in a list and are removed one occurrence at a time.
-/

namespace ECTheoryLib.Operators.Selection

/-- Sum of squared rational coordinates. -/
def VectorSquaredNorm {m : Nat} (v : ObjectiveVector m) : ℚ := ∑ i : Fin m, v i * v i

/-- Rational Euclidean dot product of objective vectors. -/
def VectorDot {m : Nat} (u v : ObjectiveVector m) : ℚ := ∑ i : Fin m, u i * v i

/-- A nonempty finite family of nonnegative reference directions, each with positive squared norm. These conditions exclude the zero line direction. -/
structure ReferenceSystem (m : Nat) where
  Count : Nat
  PositiveCount : 0 < Count
  Direction : Fin Count → ObjectiveVector m
  DirectionNonnegative : ∀ r i, 0 ≤ Direction r i
  NormPositive : ∀ r, 0 < VectorSquaredNorm (Direction r)

/-- Squared perpendicular distance to the line spanned by r when r is nonzero. The total formula also returns the squared norm of v at r=0, but reference systems exclude that case. -/
def ReferenceLineDistanceSquared {m : Nat} (v r : ObjectiveVector m) : ℚ :=
  VectorSquaredNorm v - VectorDot v r * VectorDot v r / VectorSquaredNorm r

/-- All candidates attaining a minimum score within the given finite set. An empty candidate set gives an empty result. -/
def FiniteMinimizers {β γ : Type*} [DecidableEq β] [LinearOrder γ]
    (Candidates : Finset β) (Score : β → γ) : Finset β :=
  Candidates.filter (fun x => ∀ y ∈ Candidates, Score x ≤ Score y)

theorem FiniteMinimizersNonempty {β γ : Type*} [DecidableEq β] [LinearOrder γ]
    (Candidates : Finset β) (Score : β → γ) (Nonempty : Candidates.Nonempty) :
    (FiniteMinimizers Candidates Score).Nonempty := by
  obtain ⟨x, InCandidates, Minimal⟩ := Finset.exists_min_image Candidates Score Nonempty
  exact ⟨x, Finset.mem_filter.mpr ⟨InCandidates, Minimal⟩⟩

theorem FiniteMinimizerMember {β γ : Type*} [DecidableEq β] [LinearOrder γ]
    (Candidates : Finset β) (Score : β → γ) (x : β)
    (Minimal : x ∈ FiniteMinimizers Candidates Score) : x ∈ Candidates := by
  exact (Finset.mem_filter.mp Minimal).1

theorem FiniteMinimizerMinimal {β γ : Type*} [DecidableEq β] [LinearOrder γ]
    (Candidates : Finset β) (Score : β → γ) (x : β)
    (Minimal : x ∈ FiniteMinimizers Candidates Score) :
    ∀ y ∈ Candidates, Score x ≤ Score y := by
  exact (Finset.mem_filter.mp Minimal).2

/-- All reference directions whose lines minimize squared perpendicular distance to the given vector. -/
def NearestReferences {m : Nat} (References : ReferenceSystem m)
    (v : ObjectiveVector m) : Finset (Fin References.Count) :=
  FiniteMinimizers Finset.univ (fun r => ReferenceLineDistanceSquared v (References.Direction r))

theorem NearestReferencesNonempty {m : Nat} (References : ReferenceSystem m)
    (v : ObjectiveVector m) : (NearestReferences References v).Nonempty := by
  apply FiniteMinimizersNonempty
  exact ⟨⟨0, References.PositiveCount⟩, Finset.mem_univ _⟩

noncomputable section

/-- A uniform choice retaining the membership proof in the result type. -/
def UniformFinsetSubtype {β : Type*} [Fintype β] [DecidableEq β]
    (Candidates : Finset β) (CandidatesNonempty : Candidates.Nonempty) : PMF {x // x ∈ Candidates} :=
  letI : Nonempty {x // x ∈ Candidates} :=
    ⟨⟨CandidatesNonempty.choose, CandidatesNonempty.choose_spec⟩⟩
  PMF.uniformOfFintype _

/-- Uniform choice among all nearest reference lines, so association ties retain equal probability. -/
def ReferenceAssociation {m : Nat} (References : ReferenceSystem m)
    (v : ObjectiveVector m) : PMF (Fin References.Count) :=
  PMF.uniformOfFinset (NearestReferences References v) (NearestReferencesNonempty References v)

theorem ReferenceAssociationNearest {m : Nat} (References : ReferenceSystem m)
    (v : ObjectiveVector m) (r : Fin References.Count)
    (Possible : r ∈ (ReferenceAssociation References v).support) :
    ∀ q, ReferenceLineDistanceSquared v (References.Direction r) ≤
      ReferenceLineDistanceSquared v (References.Direction q) := by
  have Nearest : r ∈ NearestReferences References v := by
    exact (PMF.mem_support_uniformOfFinset_iff _ r).mp Possible
  exact fun q => FiniteMinimizerMinimal _ _ r Nearest q (Finset.mem_univ q)

/-- Independent tie sampling for distinct position labels. Repeated labels would
be overwritten; NSGA-III supplies the unique positions of its combined list. -/
def SampleReferenceAssociations {ι : Type*} [DecidableEq ι] {m : Nat}
    (References : ReferenceSystem m) (Normalized : ι → ObjectiveVector m) :
    List ι → PMF (ι → Fin References.Count)
  | [] => PMF.pure (fun _ => ⟨0, References.PositiveCount⟩)
  | j :: Rest => (ReferenceAssociation References (Normalized j)).bind (fun r =>
      (SampleReferenceAssociations References Normalized Rest).map
        (fun Association => Function.update Association j r))

/-- Number of already selected occurrences associated with the specified reference direction. -/
def NicheOccupancy {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Association : ι → Fin References.Count) (Selected : List ι) (r : Fin References.Count) : Nat :=
  (Selected.filter (fun j => decide (Association j = r))).length

/-- Reference directions still associated with at least one remaining occurrence. -/
def ActiveReferences {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Association : ι → Fin References.Count) (Remaining : List ι) :
    Finset (Fin References.Count) :=
  Finset.univ.filter (fun r => ∃ j : Fin Remaining.length, Association Remaining[j] = r)

theorem ActiveReferencesNonempty {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Association : ι → Fin References.Count) (Remaining : List ι)
    (PositiveRemaining : 0 < Remaining.length) :
    (ActiveReferences References Association Remaining).Nonempty := by
  let j : Fin Remaining.length := ⟨0, PositiveRemaining⟩
  exact ⟨Association Remaining[j], Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, j, rfl⟩⟩

/-- Active directions of minimum current occupancy, ignoring directions with no remaining candidates. -/
def LeastOccupiedReferences {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Association : ι → Fin References.Count) (Remaining Selected : List ι) :
    Finset (Fin References.Count) :=
  FiniteMinimizers (ActiveReferences References Association Remaining)
    (NicheOccupancy References Association Selected)

/-- Indices of remaining occurrences associated with a specified reference direction. -/
def NicheIndividualCandidates {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Association : ι → Fin References.Count) (Remaining : List ι) (r : Fin References.Count) :
    Finset (Fin Remaining.length) :=
  Finset.univ.filter (fun j => Association Remaining[j] = r)

theorem NicheIndividualCandidatesNonempty {ι : Type*} {m : Nat}
    (References : ReferenceSystem m) (Association : ι → Fin References.Count)
    (Remaining : List ι) (r : Fin References.Count)
    (Active : r ∈ ActiveReferences References Association Remaining) :
    (NicheIndividualCandidates References Association Remaining r).Nonempty := by
  obtain ⟨j, Associated⟩ := (Finset.mem_filter.mp Active).2
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, Associated⟩⟩

/-- For an empty niche, retain its closest remaining candidates; for an occupied niche, retain all its remaining candidates. The subsequent selection is uniform within this set. -/
def NicheSurvivorCandidates {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Normalized : ι → ObjectiveVector m) (Association : ι → Fin References.Count)
    (Remaining Selected : List ι) (r : Fin References.Count) : Finset (Fin Remaining.length) :=
  let Candidates := NicheIndividualCandidates References Association Remaining r
  if NicheOccupancy References Association Selected r = 0 then
    FiniteMinimizers Candidates
      (fun j => ReferenceLineDistanceSquared (Normalized Remaining[j]) (References.Direction r))
  else Candidates

theorem NicheSurvivorCandidatesNonempty {ι : Type*} {m : Nat}
    (References : ReferenceSystem m) (Normalized : ι → ObjectiveVector m)
    (Association : ι → Fin References.Count) (Remaining Selected : List ι)
    (r : Fin References.Count) (Active : r ∈ ActiveReferences References Association Remaining) :
    (NicheSurvivorCandidates References Normalized Association Remaining Selected r).Nonempty := by
  unfold NicheSurvivorCandidates
  split_ifs
  · exact FiniteMinimizersNonempty _ _
      (NicheIndividualCandidatesNonempty References Association Remaining r Active)
  · exact NicheIndividualCandidatesNonempty References Association Remaining r Active

/-- Select a least occupied active reference uniformly, then its first closest
or subsequent uniformly chosen individual. The result is a valid list position. -/
def ReferenceNicheIndex {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Normalized : ι → ObjectiveVector m) (Association : ι → Fin References.Count)
    (Remaining Selected : List ι) (PositiveRemaining : 0 < Remaining.length) :
    PMF (Fin Remaining.length) :=
  let ReferenceCandidates := LeastOccupiedReferences References Association Remaining Selected
  have ReferenceCandidatesNonempty : ReferenceCandidates.Nonempty :=
    FiniteMinimizersNonempty _ _
      (ActiveReferencesNonempty References Association Remaining PositiveRemaining)
  (UniformFinsetSubtype ReferenceCandidates ReferenceCandidatesNonempty).bind (fun r =>
    have Active : r.val ∈ ActiveReferences References Association Remaining :=
      FiniteMinimizerMember _ _ r.val r.property
    (UniformFinsetSubtype
      (NicheSurvivorCandidates References Normalized Association Remaining Selected r.val)
      (NicheSurvivorCandidatesNonempty References Normalized Association Remaining Selected r.val Active)).map
      (fun j => j.val))

/-- Niching removes each chosen occurrence before the next occupancy update. -/
def ReferenceNiching {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Normalized : ι → ObjectiveVector m) (Association : ι → Fin References.Count) :
    Nat → List ι → List ι → PMF (List ι)
  | 0, _, _ => PMF.pure []
  | Count + 1, Remaining, Selected =>
      if PositiveRemaining : 0 < Remaining.length then
        (ReferenceNicheIndex References Normalized Association Remaining Selected PositiveRemaining).bind
          (fun j => (ReferenceNiching References Normalized Association Count
            (Remaining.eraseIdx j.val) (Selected ++ [Remaining[j]])).map
              (fun Tail => Remaining[j] :: Tail))
      else PMF.pure []

theorem ReferenceNichingLength {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Normalized : ι → ObjectiveVector m) (Association : ι → Fin References.Count)
    (Count : Nat) (Remaining Selected Next : List ι)
    (Possible : Next ∈ (ReferenceNiching References Normalized Association Count Remaining Selected).support) :
    Next.length = min Count Remaining.length := by
  induction Count generalizing Remaining Selected Next with
  | zero =>
      have Empty : Next = [] := (PMF.mem_support_pure_iff _ _).mp Possible
      rw [Empty]
      rfl
  | succ Count Previous =>
      unfold ReferenceNiching at Possible
      split_ifs at Possible with PositiveRemaining
      · obtain ⟨j, _IndexPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
        obtain ⟨Tail, TailPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
        have TailLength := Previous (Remaining.eraseIdx j.val) (Selected ++ [Remaining[j]]) Tail TailPossible
        have ErasedLength := List.length_eraseIdx_add_one j.isLt
        rw [← Equality, List.length_cons, TailLength]
        omega
      · have Empty : Next = [] := (PMF.mem_support_pure_iff _ _).mp Possible
        rw [Empty]
        have RemainingEmptyLength : Remaining.length = 0 := by omega
        rw [RemainingEmptyLength, Nat.min_zero]
        rfl

theorem ReferenceNichingMember {ι : Type*} {m : Nat} (References : ReferenceSystem m)
    (Normalized : ι → ObjectiveVector m) (Association : ι → Fin References.Count)
    (Count : Nat) (Remaining Selected Next : List ι)
    (Possible : Next ∈ (ReferenceNiching References Normalized Association Count Remaining Selected).support)
    (x : ι) (InNext : x ∈ Next) : x ∈ Remaining := by
  induction Count generalizing Remaining Selected Next with
  | zero =>
      have Empty : Next = [] := (PMF.mem_support_pure_iff _ _).mp Possible
      rw [Empty] at InNext
      exact False.elim (List.not_mem_nil InNext)
  | succ Count Previous =>
      unfold ReferenceNiching at Possible
      split_ifs at Possible with PositiveRemaining
      · obtain ⟨j, _IndexPossible, NextPossible⟩ := (PMF.mem_support_bind_iff _ _ _).mp Possible
        obtain ⟨Tail, TailPossible, Equality⟩ := (PMF.mem_support_map_iff _ _ _).mp NextPossible
        rw [← Equality] at InNext
        obtain AtHead | InTail := List.mem_cons.mp InNext
        · rw [AtHead]
          exact List.getElem_mem j.isLt
        · exact List.mem_of_mem_eraseIdx
            (Previous (Remaining.eraseIdx j.val) (Selected ++ [Remaining[j]]) Tail TailPossible InTail)
      · have Empty : Next = [] := (PMF.mem_support_pure_iff _ _).mp Possible
        rw [Empty] at InNext
        exact False.elim (List.not_mem_nil InNext)

end

end ECTheoryLib.Operators.Selection
